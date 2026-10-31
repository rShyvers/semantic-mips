import Std.Data.HashMap.Basic
import MipsSim.Word
import MipsSim.Types
import MipsSim.State
import MipsSim.Instruction
import MipsSim.Asm
import MipsSim.Step

/-!
# DiffHarness — differential testing executable (Wave 3, DESIGN.md §2/§6)

Runs every `.asm` program in `MipsSim/tests/corpus/` through both our `Step`
simulator and a real MARS 4.5 process, and compares their observable output
exactly (after stripping MARS's startup banner).

## CLI

```
DiffHarness [javaPath] [marsJarPath]
```
Defaults: `javaPath := "java"`, `marsJarPath := "../vendor/mars/Mars4_5.jar"`.
Exit code `0` iff every corpus program's verdict is PASS.

## MARS output format (determined empirically — see report)

Running MARS on a trivial program prints:

```
MARS 4.5  Copyright 2003-2014 Pete Sanderson and Kenneth Vollmar
<blank line>
<program output>
```

i.e. a one-line banner, then a blank line, then whatever the program printed
to `SystemIO`. We strip everything up to and including the first blank line
(the first occurrence of `"\n\n"`).

A second empirical fact, *not* mentioned by the task prompt but required for
any comparison to be meaningful at all: **MARS's CLI driver always appends
exactly one trailing `'\n'` to stdout after the program finishes**, even when
the program printed nothing and even when the program's own last character
was already a newline (confirmed by direct experiment: a program that prints
nothing yields banner + blank line + a single bare `'\n'`). This is a
console-wrapper artifact of the MARS CLI, not part of any program's
observable output, so we strip exactly one trailing `'\n'` after the banner
split, symmetrically with the banner strip itself (both are MARS-harness
framing, not program output). Without this, *every* program would miscompare
including ones with byte-for-byte identical program output, which cannot be
the intended comparison.

MARS also does not use a distinguishing non-zero exit code for runtime
exceptions (division errors, bad syscalls, misaligned memory, …): our own
experiments show `exitCode = 0` even when MARS prints
`"Error in ... Runtime exception ..."` / `"Processing terminated due to
errors."` to stdout. We therefore detect a MARS-side runtime failure by
searching the post-banner output for the substring `"Error in "`, which
every MARS runtime-exception report begins with (`ProcessingException`'s
`generateErrorMessage`/`MessageFormat`, confirmed empirically).
-/

open IO.Process (output SpawnArgs Output)

/-- Convert an assembled `Program` (word-addressable: both `.text` and
`.data` entries, per `Asm.lean`) into byte-addressable `State.mem` entries,
using the **same big-endian convention `State.lean`'s `readMemWord`/
`writeMemWord` already use** (`addr` = most-significant byte). This is pure
plumbing — `Step.run` only ever fetches instructions from the `Program`
directly (`fetchWord`), but `lw`/`lb`/`sh`/etc. all read from `State.mem`,
which starts empty in `initialState`. Without this step, any corpus program
that loads from `.data` would see all-zero memory. -/
def materialize (p : Program) (s0 : State) : State :=
  p.fold (fun (acc : State) (addr word : W32) =>
    let b0 : UInt8 := ((word >>> 24) &&& 0xff#32).toNat.toUInt8
    let b1 : UInt8 := ((word >>> 16) &&& 0xff#32).toNat.toUInt8
    let b2 : UInt8 := ((word >>> 8) &&& 0xff#32).toNat.toUInt8
    let b3 : UInt8 := (word &&& 0xff#32).toNat.toUInt8
    { acc with
        mem := (((acc.mem.insert addr b0).insert (addr + 1#32) b1).insert
                  (addr + 2#32) b2).insert (addr + 3#32) b3 })
    s0

/-- The raw encoding of a bare `syscall` instruction (opcode 0, funct 0x0c,
all register/shamt fields 0) — the only word that can ever produce
`HaltReason.illegalInstruction` via the "unsupported syscall service number"
path in `Step.execInstr` (every real unknown-opcode/funct word also produces
`illegalInstruction`, but with a *different* raw word; a `syscall`
instruction always encodes to this exact value regardless of which service
number is in `$v0` at execution time, since the number lives in a register,
not the instruction word). -/
def syscallWord : W32 := encode .syscall

/-- Classification of our simulator's outcome for one corpus program. -/
inductive OurOutcome where
  /-- `assemble` failed: can't even build a `Program`. -/
  | asmFailed (msg : String)
  /-- Halted via `syscall 10` (normal exit). Carries the accumulated output. -/
  | clean (out : String)
  /-- Halted on an unsupported `syscall` service number (the one case where
  our v1 approximation of MARS's `SYSCALL_EXCEPTION` is deliberately
  under-specified — see DESIGN.md / Step.lean docstring). -/
  | unsupportedSyscall (out : String)
  /-- Halted for any other reason (illegal instruction on a genuine garbage
  word, address error, arithmetic overflow) — a real runtime error. -/
  | error (out : String) (reason : String)
  /-- Ran out of the fuel budget without halting (a bug, or a genuinely
  non-terminating program — neither of which this corpus should produce). -/
  | limitReached (out : String)

/-- Run one assembled program through our `Step.run`, `fuel` steps max. -/
def runOurs (src : String) (fuel : Nat) : OurOutcome :=
  match assemble src with
  | .error e => .asmFailed (toString (repr e))
  | .ok prog =>
    let s0 := materialize prog (initialState textBase)
    match run prog s0 fuel with
    | .halted .exit s _ => .clean s.out
    | .halted (.illegalInstruction w) s _ =>
      if w == syscallWord then .unsupportedSyscall s.out
      else .error s.out s!"illegalInstruction {w}"
    | .halted (.addressError a) s _ => .error s.out s!"addressError {a}"
    | .halted .arithmeticOverflow s _ => .error s.out "arithmeticOverflow"
    | .limitReached s _ => .limitReached s.out

/-- Strip the version banner, **and any assembler-diagnostic blocks that
follow it**, from raw MARS stdout.

The common case (no diagnostics) is exactly "banner line, blank line,
program output": dropping the first line and the following blank line
suffices. But MARS also emits non-fatal `Warning in ...` lines for things
like out-of-range `.byte` literals (confirmed empirically: a `.byte 0xff`
operand -- in-range as an *unsigned* byte, but out of the assembler's
signed-byte check -- produces `Warning in <path> line N column M: "0xff" is
out-of-range for a signed value and possibly truncated`, followed by its own
blank line, *before* the program's actual output). We handle this by
repeatedly stripping `("Warning in "/"Error in " line, blank line)` pairs
from the front, after the banner, until a line doesn't match that pattern --
that remainder (rejoined, preserving any blank lines the *program itself*
prints) is the real output. This cannot be done with a single `"\n\n"` split
(the naive approach), since that would also truncate at a blank line that is
part of the program's own output, or stop at the first diagnostic's blank
line instead of the last one. -/
def stripBanner (s : String) : String :=
  let isDiagnosticLine (l : String) : Bool :=
    l.startsWith "Warning in " || l.startsWith "Error in "
  let rec dropDiagnostics : List String -> List String
    | msg :: blank :: rest =>
      if blank.isEmpty && isDiagnosticLine msg then dropDiagnostics rest
      else msg :: blank :: rest
    | rest => rest
  match s.splitOn "\n" with
  | _banner :: _blank :: rest => String.intercalate "\n" (dropDiagnostics rest)
  | _ => s  -- fewer than 2 lines: nothing to strip (shouldn't happen for MARS output)

/-- Strip exactly one trailing `'\n'`, if present (the MARS CLI console
artifact — see module docstring). -/
def stripOneTrailingNewline (s : String) : String :=
  if s.endsWith "\n" then (s.dropEnd 1).toString else s

/-- Does this (post-banner) MARS output indicate a runtime exception /
assembly error rather than normal termination? -/
def marsLooksLikeError (s : String) : Bool :=
  decide ((s.splitOn "Error in ").length > 1)

structure MarsResult where
  output  : String   -- post-banner, trailing-newline-stripped stdout
  isError : Bool
  raw     : String   -- full raw stdout, for diagnostics on FAIL

def runMars (javaPath marsJarPath progPath : String) : IO MarsResult := do
  let out ← output { cmd := javaPath, args := #["-jar", marsJarPath, progPath] }
  let stripped := stripOneTrailingNewline (stripBanner out.stdout)
  pure { output := stripped, isError := marsLooksLikeError out.stdout, raw := out.stdout }

/-- Final per-program verdict. -/
inductive Verdict where
  | pass
  | fail (detail : String)

/-- First index at which two strings differ, if they're not equal
(`none` if one is a prefix of the other up to the shorter length — reported
as "length mismatch" by the caller instead). Linear scan over `Char`s is
fine for these small corpus outputs. -/
def firstDivergence (a b : String) : Option Nat := Id.run do
  let as := a.toList
  let bs := b.toList
  let mut i := 0
  let mut aRest := as
  let mut bRest := bs
  while true do
    match aRest, bRest with
    | [], [] => return none
    | [], _ :: _ => return some i
    | _ :: _, [] => return some i
    | x :: xs, y :: ys =>
      if x != y then return some i
      else
        aRest := xs
        bRest := ys
        i := i + 1
  return none

/-- Judge one program's outcome per the DESIGN.md/task rules:
- both "clean" (our `.exit` vs MARS not looking like an error): PASS iff the
  exact output strings match.
- our unsupported-syscall halt vs MARS's runtime exception: PASS iff MARS
  *also* reports an error (both-fail symmetry is the documented exception).
- exactly one side errors and the other terminates cleanly: FAIL (divergent
  halting behavior).
- both sides error (and ours isn't the unsupported-syscall case): PASS — a
  coarse "both failed" symmetry; this corpus is not expected to exercise it,
  but it's not treated as an automatic FAIL either, since no v1 instruction
  class in the corpus has a defined precise error-message format to compare. -/
def judge (ours : OurOutcome) (mars : MarsResult) : Verdict :=
  match ours with
  | .asmFailed msg => .fail s!"our assembler rejected the corpus program: {msg}"
  | .unsupportedSyscall _ =>
    if mars.isError then .pass
    else .fail "we halted on an unsupported syscall service number, but MARS exited cleanly"
  | .limitReached _ =>
    if mars.isError then .pass
    else .fail "we never halted within the fuel budget, but MARS exited cleanly"
  | .error _ reason =>
    if mars.isError then .pass
    else .fail s!"we halted with error ({reason}), but MARS exited cleanly"
  | .clean ourOut =>
    if mars.isError then
      .fail s!"we exited cleanly, but MARS reported a runtime error"
    else if ourOut == mars.output then
      .pass
    else
      match firstDivergence ourOut mars.output with
      | some i => .fail s!"output mismatch at char {i}: ours={repr ourOut}, mars={repr mars.output}"
      | none => .fail s!"output length mismatch: ours={repr ourOut}, mars={repr mars.output}"

def outcomeOut : OurOutcome → String
  | .asmFailed _ => ""
  | .clean o => o
  | .unsupportedSyscall o => o
  | .error o _ => o
  | .limitReached o => o

/-- List `.asm` files directly under `dir`, sorted by file name for a
deterministic run order. -/
def listAsmFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let asmFiles := entries.filterMap (fun e =>
    if e.fileName.endsWith ".asm" then some e.fileName else none)
  let sorted := asmFiles.qsort (· < ·)
  pure ((sorted.toList.map (fun (name : String) => dir / name)).toArray)

def main (args : List String) : IO UInt32 := do
  let javaPath := args.getD 0 "java"
  let marsJarPath := args.getD 1 "../vendor/mars/Mars4_5.jar"
  let corpusDir : System.FilePath := "tests/corpus"
  let files ← listAsmFiles corpusDir
  if files.isEmpty then
    IO.eprintln s!"no .asm files found under {corpusDir}"
    return 1
  let mut allPass := true
  for f in files do
    let src ← IO.FS.readFile f
    let ours := runOurs src 100000
    let mars ← runMars javaPath marsJarPath f.toString
    let verdict := judge ours mars
    match verdict with
    | .pass =>
      IO.println s!"PASS  {f}"
    | .fail detail =>
      allPass := false
      IO.println s!"FAIL  {f}"
      IO.println s!"  reason: {detail}"
      IO.println s!"  our output : {repr (outcomeOut ours)}"
      IO.println s!"  mars output: {repr mars.output}"
      IO.println s!"  mars raw stdout: {repr mars.raw}"
  if allPass then
    IO.println s!"SUMMARY: all {files.size} corpus programs PASS"
    return 0
  else
    IO.println s!"SUMMARY: FAIL — see divergences above"
    return 1

-- ====================================================================
-- ## In-file tests (DESIGN.md §5 / CLAUDE.md §5)
--
-- `#guard` checks that every corpus program (embedded here verbatim,
-- duplicated from the files under `tests/corpus/` since compile-time
-- `#guard`/`by decide` elaboration cannot read the filesystem) assembles
-- successfully and runs to a `halted (.exit)` outcome in our own simulator.
-- Two of them additionally get a hand-computed exact-`out` assertion.
-- These check OUR simulator's documented behavior (including its own
-- known quirks, e.g. the syscall-1 trailing newline — see the report),
-- *not* MARS's; the differential comparison against MARS happens only at
-- `main`/runtime, via the corpus files on disk.
-- ====================================================================

section CorpusGoldenTests

private def isHaltedExit (o : OurOutcome) : Bool :=
  match o with
  | .clean _ => true
  | _ => false

private def rArithSrc : String :=
"main:\n" ++
"    li   $t0, 50\n" ++
"    li   $t1, 20\n" ++
"    add  $t2, $t0, $t1\n" ++
"    sub  $t3, $t0, $t1\n" ++
"    mult $t0, $t1\n" ++
"    mflo $t4\n" ++
"    div  $t0, $t1\n" ++
"    mfhi $t5\n" ++
"    mflo $t6\n" ++
"    andi $a0, $t2, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t3, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t4, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t5, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t6, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs rArithSrc 100000)
-- Hand-computed: $t2=70, $t3=30, mult 50*20=1000 -> $t4=1000 mod 256 via andi 0x7f
-- is computed on the *register value itself* (1000 = 0x3e8, &0x7f = 0x68 = 104);
-- div 50/20 -> lo=2,hi=10 -> $t5=10,$t6=2. Chars: 70,30,104,10,2.
#guard outcomeOut (runOurs rArithSrc 100000) =
  String.ofList [Char.ofNat 70, Char.ofNat 30, Char.ofNat 104, Char.ofNat 10, Char.ofNat 2]

private def syscallIoSrc : String :=
".data\n" ++
"msg: .asciiz \"Hi\\n\"\n" ++
".text\n" ++
"main:\n" ++
"    li   $v0, 4\n" ++
"    la   $a0, msg\n" ++
"    syscall\n" ++
"    li   $v0, 1\n" ++
"    li   $a0, 42\n" ++
"    syscall\n" ++
"    li   $v0, 11\n" ++
"    li   $a0, 33\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs syscallIoSrc 100000)
-- Hand-computed: "Hi\n" (syscall 4) ++ "42" (syscall 1, no added newline per
-- the fixed Step.lean / INSTRUCTION-REF.md) ++ "!" (syscall 11, char 33).
#guard outcomeOut (runOurs syscallIoSrc 100000) = "Hi\n42!"

private def rLogicSrc : String :=
"main:\n" ++
"    li   $t0, 0x6a\n" ++
"    li   $t1, 0x3c\n" ++
"    and  $t2, $t0, $t1\n" ++
"    or   $t3, $t0, $t1\n" ++
"    xor  $t4, $t0, $t1\n" ++
"    nor  $t5, $t0, $t1\n" ++
"    slt  $t6, $t1, $t0\n" ++
"    andi $a0, $t2, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t3, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t4, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t5, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t6, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs rLogicSrc 100000)

private def shiftsSrc : String :=
"main:\n" ++
"    li   $t0, 1\n" ++
"    sll  $t1, $t0, 5\n" ++
"    li   $t2, 0x80000000\n" ++
"    srl  $t3, $t2, 31\n" ++
"    sra  $t4, $t2, 31\n" ++
"    andi $a0, $t1, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t3, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t4, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs shiftsSrc 100000)

private def iImmSrc : String :=
"main:\n" ++
"    li    $t0, 10\n" ++
"    addi  $t1, $t0, 5\n" ++
"    andi  $t2, $t0, 0x7\n" ++
"    ori   $t3, $t0, 0x5\n" ++
"    xori  $t4, $t0, 0x3\n" ++
"    lui   $t5, 0x1\n" ++
"    srl   $t6, $t5, 16\n" ++
"    andi  $a0, $t1, 0x7f\n" ++
"    li    $v0, 11\n" ++
"    syscall\n" ++
"    andi  $a0, $t2, 0x7f\n" ++
"    li    $v0, 11\n" ++
"    syscall\n" ++
"    andi  $a0, $t3, 0x7f\n" ++
"    li    $v0, 11\n" ++
"    syscall\n" ++
"    andi  $a0, $t4, 0x7f\n" ++
"    li    $v0, 11\n" ++
"    syscall\n" ++
"    andi  $a0, $t6, 0x7f\n" ++
"    li    $v0, 11\n" ++
"    syscall\n" ++
"    li    $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs iImmSrc 100000)

private def liLaMoveNopSrc : String :=
".data\n" ++
"msgval: .word 77\n" ++
".text\n" ++
"main:\n" ++
"    nop\n" ++
"    la   $t0, msgval\n" ++
"    lw   $t1, 0($t0)\n" ++
"    li   $t2, 5\n" ++
"    move $t3, $t2\n" ++
"    nop\n" ++
"    andi $a0, $t1, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t3, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs liLaMoveNopSrc 100000)

private def memWordSrc : String :=
".data\n" ++
"buf: .word 0, 0, 0, 0\n" ++
".text\n" ++
"main:\n" ++
"    la   $t0, buf\n" ++
"    addi $t0, $t0, 8\n" ++
"    li   $t1, 123\n" ++
"    sw   $t1, 0($t0)\n" ++
"    sw   $t1, -4($t0)\n" ++
"    lw   $t2, 0($t0)\n" ++
"    lw   $t3, -4($t0)\n" ++
"    andi $a0, $t2, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t3, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs memWordSrc 100000)
#guard outcomeOut (runOurs memWordSrc 100000) =
  String.ofList [Char.ofNat 123, Char.ofNat 123]

-- Deliberately endian-invariant (SPEC-NOTES.md \u00a79: our language is
-- big-endian per the ISA; MARS 4.5 headless defaults to little-endian
-- storage). `.byte`-declared cells are individually addressed (no
-- multi-byte composition, so byte order can't matter); the halfword test
-- round-trips `sh` then `lh`/`lhu` at the *same* address.
private def memByteHalfSrc : String :=
".data\n" ++
"bytebuf: .byte 0x12, 0xff, 0x05, 0x00\n" ++
"halfbuf: .word 0\n" ++
".text\n" ++
"main:\n" ++
"    la   $t0, bytebuf\n" ++
"    lb   $t1, 0($t0)\n" ++
"    lbu  $t2, 1($t0)\n" ++
"    lb   $t3, 2($t0)\n" ++
"    la   $t6, halfbuf\n" ++
"    li   $t7, 0x8003\n" ++
"    sh   $t7, 0($t6)\n" ++
"    lh   $t4, 0($t6)\n" ++
"    lhu  $t5, 0($t6)\n" ++
"    andi $a0, $t1, 0xff\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t2, 0xff\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t3, 0xff\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t4, 0xff\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t5, 0xff\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs memByteHalfSrc 100000)
-- Hand-computed: $t1=18, $t2=255, $t3=5, then sh/lh/lhu round-trip 0x8003
-- (sign-extends negative for lh, low byte 3 either way).
#guard outcomeOut (runOurs memByteHalfSrc 100000) =
  String.ofList [Char.ofNat 18, Char.ofNat 255, Char.ofNat 5, Char.ofNat 3, Char.ofNat 3]

private def branchTakenSrc : String :=
"main:\n" ++
"    li   $t0, 5\n" ++
"    li   $t1, 5\n" ++
"    li   $t2, 1\n" ++
"    beq  $t0, $t1, Lbeq\n" ++
"    li   $t2, 0\n" ++
"Lbeq:\n" ++
"    li   $t3, 3\n" ++
"    li   $t4, 4\n" ++
"    li   $t5, 1\n" ++
"    bne  $t3, $t4, Lbne\n" ++
"    li   $t5, 0\n" ++
"Lbne:\n" ++
"    li   $t6, -1\n" ++
"    li   $t7, 1\n" ++
"    blez $t6, Lblez\n" ++
"    li   $t7, 0\n" ++
"Lblez:\n" ++
"    li   $t8, 5\n" ++
"    li   $t9, 1\n" ++
"    bgtz $t8, Lbgtz\n" ++
"    li   $t9, 0\n" ++
"Lbgtz:\n" ++
"    move $a0, $t2\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    move $a0, $t5\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    move $a0, $t7\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    move $a0, $t9\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs branchTakenSrc 100000)
#guard outcomeOut (runOurs branchTakenSrc 100000) =
  String.ofList [Char.ofNat 1, Char.ofNat 1, Char.ofNat 1, Char.ofNat 1]

private def branchNotTakenSrc : String :=
"main:\n" ++
"    li   $t0, 5\n" ++
"    li   $t1, 6\n" ++
"    li   $t2, 1\n" ++
"    beq  $t0, $t1, Lbeq\n" ++
"    li   $t2, 0\n" ++
"Lbeq:\n" ++
"    li   $t3, 3\n" ++
"    li   $t4, 3\n" ++
"    li   $t5, 1\n" ++
"    bne  $t3, $t4, Lbne\n" ++
"    li   $t5, 0\n" ++
"Lbne:\n" ++
"    li   $t6, 5\n" ++
"    li   $t7, 1\n" ++
"    blez $t6, Lblez\n" ++
"    li   $t7, 0\n" ++
"Lblez:\n" ++
"    li   $t8, -3\n" ++
"    li   $t9, 1\n" ++
"    bgtz $t8, Lbgtz\n" ++
"    li   $t9, 0\n" ++
"Lbgtz:\n" ++
"    move $a0, $t2\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    move $a0, $t5\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    move $a0, $t7\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    move $a0, $t9\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs branchNotTakenSrc 100000)
#guard outcomeOut (runOurs branchNotTakenSrc 100000) =
  String.ofList [Char.ofNat 0, Char.ofNat 0, Char.ofNat 0, Char.ofNat 0]

private def jumpJalSrc : String :=
"main:\n" ++
"    jal  Lsub\n" ++
"AfterCall:\n" ++
"    move $a0, $t0\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $ra, 0xff\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n" ++
"Lsub:\n" ++
"    li   $t0, 65\n" ++
"    j    AfterCall\n"

#guard isHaltedExit (runOurs jumpJalSrc 100000)

private def addiNegSrc : String :=
"main:\n" ++
"    li   $t0, 10\n" ++
"    addi $t1, $t0, -3\n" ++
"    li   $t2, 0xffffffff\n" ++
"    li   $t3, 1\n" ++
"    slt  $t4, $t2, $t3\n" ++
"    sltu $t5, $t2, $t3\n" ++
"    andi $a0, $t1, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t4, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    andi $a0, $t5, 0x7f\n" ++
"    li   $v0, 11\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

#guard isHaltedExit (runOurs addiNegSrc 100000)
#guard outcomeOut (runOurs addiNegSrc 100000) =
  String.ofList [Char.ofNat 7, Char.ofNat 1, Char.ofNat 0]

end CorpusGoldenTests
