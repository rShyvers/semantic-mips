import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Asm
import Semantics.Step

/-!
# EquivHarness — arithmetic equivalence corpus (thin interpreter, no MARS)

This replaces the originally-planned "unseal a real MIPS program (CS47) and
find its bug" step: that program needs assembler macros, which
`docs/spec/SPEC-NOTES.md` §9 puts explicitly out of v1 scope, so it can't be
assembled by `Asm.lean` at all. Instead, this harness validates the
semantics against a small corpus we wrote ourselves: for several arithmetic
operations, a "base" program using the direct instruction (`mult`, `div`,
`sub`, …) and a "variant" program computing the same function with
bit-shifting/bitwise instructions instead — the kind of strength-reduction a
compiler or a hand-optimizing assembly programmer would do. Two of the
pairs are *deliberately wrong* (the classic "replace division/mod by a
power of two with a raw shift/mask" bug, which breaks on negative
dividends), so this harness actually has to detect a real divergence, not
just confirm agreement everywhere — the same spirit as the sealed-program
bug hunt, on a corpus we control end to end.

**Why no MARS here, unlike `DiffHarness`:** `DiffHarness` differentially
validates the whole semantics against real MARS 4.5 by spawning a `java`
process per program — the right tool for "is this semantics the same
language as the real simulator?". That's unnecessary (and, per program,
hundreds of times slower) for "do these two *already-validated* programs
compute the same function?": the question is internal to the semantics,
so running both programs directly through our own `step`/`run` — a "thin
interpreter", pure Lean, no subprocess, no JVM, no per-case compilation —
is both sufficient and far faster. `assemble` + `run` IS the full execution
pipeline this project cares about; MARS is only needed as an external
oracle, and there is no external oracle question being asked here.

## Corpus layout (`tests/equiv/`)

Every program takes its input(s) in `$a0` (register 4) and, for the one
two-input pair, also `$a1` (register 5); every program leaves its result in
`$t9` (register 25) and halts cleanly via `syscall 10`.
-/

/-- One equivalence claim: run `basePath` and `variantPath` on the same
inputs and compare `$t9`. `expectEquivalent := true` means every tested
input must agree (a real, provable equivalence); `false` means at least one
input is expected to disagree (a deliberately-wrong variant, kept in the
corpus specifically to prove this harness isn't vacuously green). -/
structure EquivCase where
  name : String
  basePath : String
  variantPath : String
  expectEquivalent : Bool
  note : String

def corpus : List EquivCase :=
  [ { name := "mul_pow2"
    , basePath := "tests/equiv/mul_pow2_base.asm"
    , variantPath := "tests/equiv/mul_pow2_shift.asm"
    , expectEquivalent := true
    , note := "x*8 via mult/mflo vs sll by 3" }
  , { name := "mul_const5"
    , basePath := "tests/equiv/mul_const5_base.asm"
    , variantPath := "tests/equiv/mul_const5_shiftadd.asm"
    , expectEquivalent := true
    , note := "x*5 via mult/mflo vs (x<<2)+x (addu, non-trapping)" }
  , { name := "div_pow2_buggy"
    , basePath := "tests/equiv/div_pow2_base.asm"
    , variantPath := "tests/equiv/div_pow2_shift_buggy.asm"
    , expectEquivalent := false
    , note := "x/4 via div/mflo vs plain sra (WRONG: rounds toward -inf, not zero)" }
  , { name := "div_pow2_correct"
    , basePath := "tests/equiv/div_pow2_base.asm"
    , variantPath := "tests/equiv/div_pow2_shift_correct.asm"
    , expectEquivalent := true
    , note := "x/4 via div/mflo vs bias-corrected sra" }
  , { name := "mod_pow2_buggy"
    , basePath := "tests/equiv/mod_pow2_base.asm"
    , variantPath := "tests/equiv/mod_pow2_mask_buggy.asm"
    , expectEquivalent := false
    , note := "x%4 via div/mfhi vs plain andi mask (WRONG: always non-negative)" }
  , { name := "mod_pow2_correct"
    , basePath := "tests/equiv/mod_pow2_base.asm"
    , variantPath := "tests/equiv/mod_pow2_mask_correct.asm"
    , expectEquivalent := true
    , note := "x%4 via div/mfhi vs a0 - (bias-corrected quotient)*4" }
  , { name := "sub_twos_complement"
    , basePath := "tests/equiv/sub_base.asm"
    , variantPath := "tests/equiv/sub_twos_complement.asm"
    , expectEquivalent := true
    , note := "a0-a1 via subu vs nor+addiu+addu (two's-complement negate-and-add)" }
  ]

/-- Signed 32-bit test vectors: zero, unit steps around every pair's
divisor/shift-amount (both exact multiples and non-multiples, both signs),
the INT_MIN/INT_MAX boundary (and INT_MIN+3, the div/mod bias-add's own
edge case), and a handful of larger ordinary and overflow-triggering
values. The second component is only exercised by `sub_twos_complement`
(every other program ignores `$a1`); for everything else it's filler. -/
def testVectors : List (Int × Int) :=
  [ (0,0), (1,0), (-1,0), (2,0), (-2,0), (3,0), (-3,0), (4,0), (-4,0), (5,0), (-5,0)
  , (7,0), (-7,0), (8,0), (-8,0)
  , (2147483647,0), (-2147483648,0), (-2147483645,0)
  , (100,0), (-100,0), (101,0), (-101,0)
  , (123456789,0), (-123456789,0)
  , (429496729,0), (858993459,0), (-858993459,0), (-429496730,0)
  , (268435456,0), (-268435456,0), (536870912,0)
  -- sub-specific pairs (meaningful two-input cases; harmless as single-input
  -- filler elsewhere, since single-input programs never read $a1)
  , (5,3), (3,5), (-5,3), (5,-3), (-5,-3), (0,1), (1,0)
  , (2147483647,-1), (-2147483648,1), (-2147483648,-1)
  , (-2147483648,-2147483648), (2147483647,2147483647)
  , (100,37), (-100,-37), (37,-100)
  ]

/-- Outcome of running one assembled program on one input. -/
inductive RunOutcome where
  | result (v : Int)                 -- clean exit; `$t9`'s signed value
  | otherHalt (reason : String)      -- halted some other way (not `.exit`)
  | limitReached

def runOne (prog : Program) (a0 a1 : Int) (fuel : Nat) : RunOutcome :=
  let s0 := initialState textBase
  let s0 := writeReg s0 4 (ofInt32 a0)
  let s0 := writeReg s0 5 (ofInt32 a1)
  match run prog s0 fuel with
  | .halted .exit s _ => .result (asSigned (readReg s 25))
  | .halted (.illegalInstruction w) _ _ => .otherHalt s!"illegalInstruction {w}"
  | .halted (.addressError a) _ _ => .otherHalt s!"addressError {a}"
  | .halted .arithmeticOverflow _ _ => .otherHalt "arithmeticOverflow"
  | .halted .branchInDelaySlot _ _ => .otherHalt "branchInDelaySlot"
  | .limitReached _ _ => .limitReached

instance : ToString RunOutcome where
  toString
    | .result v => toString v
    | .otherHalt r => s!"<halt: {r}>"
    | .limitReached => "<limitReached>"

def outcomesMatch : RunOutcome → RunOutcome → Bool
  | .result a, .result b => a == b
  | _, _ => false

/-- Load and assemble one `.asm` file, failing loudly (this harness's whole
corpus is meant to always assemble; an `AsmError` here is itself a bug in
the corpus, not a possible verdict). -/
def loadProgram (path : String) : IO Program := do
  let src ← IO.FS.readFile path
  match assemble src with
  | .ok prog => pure prog
  | .error e => throw (IO.userError s!"{path}: assemble failed: {repr e}")

structure CaseResult where
  name : String
  mismatches : List (Int × Int × RunOutcome × RunOutcome)
  actuallyEquivalent : Bool   -- true iff zero mismatches across all test vectors

def runCase (c : EquivCase) (fuel : Nat) : IO CaseResult := do
  let base ← loadProgram c.basePath
  let variant ← loadProgram c.variantPath
  let mismatches := testVectors.filterMap fun (a0, a1) =>
    let rb := runOne base a0 a1 fuel
    let rv := runOne variant a0 a1 fuel
    if outcomesMatch rb rv then none else some (a0, a1, rb, rv)
  pure { name := c.name, mismatches := mismatches, actuallyEquivalent := mismatches.isEmpty }

def main : IO UInt32 := do
  let fuel := 1000
  let mut allOk := true
  for c in corpus do
    let r ← runCase c fuel
    let verdictOk := r.actuallyEquivalent == c.expectEquivalent
    allOk := allOk && verdictOk
    let kind := if c.expectEquivalent then "claimed equivalent" else "claimed DIFFERENT (deliberate bug)"
    IO.println s!"== {c.name} ({kind}) =="
    IO.println s!"   {c.note}"
    IO.println s!"   base={c.basePath}"
    IO.println s!"   variant={c.variantPath}"
    if r.mismatches.isEmpty then
      IO.println s!"   no mismatches across {testVectors.length} inputs"
    else
      IO.println s!"   {r.mismatches.length} mismatch(es) across {testVectors.length} inputs:"
      for (a0, a1, rb, rv) in r.mismatches.take 8 do
        IO.println s!"     a0={a0} a1={a1}: base={rb} variant={rv}"
      if r.mismatches.length > 8 then
        IO.println s!"     ... and {r.mismatches.length - 8} more"
    let status := if verdictOk then "PASS" else "FAIL (unexpected!)"
    IO.println s!"   verdict: {status}"
  IO.println ""
  if allOk then
    IO.println s!"SUMMARY: all {corpus.length} equivalence cases behaved as claimed"
    pure 0
  else
    IO.println "SUMMARY: at least one case did NOT behave as claimed — see FAIL lines above"
    pure 1
