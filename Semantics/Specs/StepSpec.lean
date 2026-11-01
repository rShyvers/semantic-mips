import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Step
import Std.Tactic.BVDecide

/-!
# StepSpec — a reviewable specification for `step`

This file is the Specs layer for `step` (DESIGN.md §6 "Wave 3", CLAUDE.md §4).
It is meant to be **read**, not just type-checked: every theorem states a
plain-English property of the simulator and cites the `docs/spec/
INSTRUCTION-REF.md` section it encodes.

## Why this file re-states small helpers

`Step.lean`'s internal helpers (`execInstr`, `regIdx`, `addOverflows`, `mkNext`,
`advance`, `readCString`, …) are declared `private`, so they are not visible
outside `Step.lean` at all — not even by their fully-qualified name. That is
the correct scoping for an implementation file, but it means this spec file
cannot name them to `unfold` or `simp` with them.

Instead, each property below is stated as an equation on the **public**
function `step` itself, with the right-hand side written out using only
public definitions (`readReg`, `writeReg`, `readMemWord`, `asSigned`, …) plus
a handful of small local mirrors of `Step.lean`'s private helpers
(`regIdxSpec`, `addOverflowsSpec`, `subOverflowsSpec`). Each mirror's
docstring says exactly which private helper it stands in for; because the
mirror is a byte-for-byte copy of the formula in `Step.lean`, the proofs
below (which reduce `step` and compare it against the mirror-built
right-hand side by `rfl`/`decide`) are a genuine check that `step` computes
what the docstring claims — not just a restatement of trusted code under a
new name.

Hypotheses of the form `fetchWord p s.pc = some w` / `decode w = some instr`
stand for "the next instruction the simulator will run is `instr`"; they are
discharged concretely in the satisfiable-example section for every theorem.
-/

set_option maxRecDepth 4000

/-- Mirrors `Step.lean`'s private `regIdx`: converts a raw 5-bit register
field (as produced by `decode`) into the `Fin 32` index `readReg`/`writeReg`
expect. -/
def regIdxSpec (w : W32) : Fin 32 := Fin.ofNat 32 w.toNat

/-- Mirrors `Step.lean`'s private `addOverflows`: MIPS `add`/`addi` signed
overflow test from INSTRUCTION-REF ("add"/"addi" sections) — both operands
non-negative but the sum negative, or both negative but the sum
non-negative. -/
def addOverflowsSpec (a b sum : Int) : Bool :=
  decide ((0 ≤ a ∧ 0 ≤ b ∧ sum < 0) ∨ (a < 0 ∧ b < 0 ∧ 0 ≤ sum))

/-- Mirrors `Step.lean`'s private `subOverflows`: MIPS `sub` signed overflow
test from INSTRUCTION-REF ("sub" section) — minuend non-negative, subtrahend
negative, but the difference negative, or the mirror-image case. -/
def subOverflowsSpec (a b diff : Int) : Bool :=
  decide ((0 ≤ a ∧ b < 0 ∧ diff < 0) ∨ (a < 0 ∧ 0 ≤ b ∧ 0 ≤ diff))

/-- Mirrors `Step.lean`'s private `isBranchLike`: true for exactly the six
branch/jump instructions that schedule a delay-slot transfer
(`beq`,`bne`,`blez`,`bgtz`,`j`,`jal`) — used to state
`branch_in_delay_slot_halts` below. -/
def isBranchLikeSpec (instr : Instruction) : Bool :=
  match instr with
  | .beq _ _ _ | .bne _ _ _ | .blez _ _ | .bgtz _ _ | .j _ | .jal _ => true
  | _ => false

/-- Mirrors `Step.lean`'s private `zeroExtByte`: zero-extends a byte to a
full `W32`. Used by `setByteSlotSpec` below (and matches the inline
`BitVec.ofNat 32 b.toNat` the `lbu` half of `lb_lbu_spec_raw` already
writes out longhand). -/
def zeroExtByteSpec (b : UInt8) : W32 :=
  BitVec.ofNat 32 b.toNat

/-- Mirrors `Step.lean`'s private `setByteSlot`: replaces byte-position
`slot` of `w` with `b`, leaving the other three byte-positions unchanged.
`slot = 0` is the most-significant byte (bits 31..24), `slot = 3` the
least-significant (bits 7..0) -- the same big-endian byte-position
convention `readMemWord`/`writeMemWord` use. Used by `lwl`/`lwr`'s
partial-register merge (`lwl_spec_raw`/`lwr_spec_raw` below). -/
def setByteSlotSpec (w : W32) (slot : Nat) (b : UInt8) : W32 :=
  let shift := (3 - slot) * 8
  let mask : W32 := 0xff#32 <<< shift
  (w &&& ~~~mask) ||| (zeroExtByteSpec b <<< shift)

/-- Mirrors `Step.lean`'s private `getByteSlot`: extracts byte-position
`slot` of `w` (same convention as `setByteSlotSpec`). Used by `swl`/`swr`'s
partial-memory-store byte extraction (`swl_spec_raw`/`swr_spec_raw` below). -/
def getByteSlotSpec (w : W32) (slot : Nat) : UInt8 :=
  let shift := (3 - slot) * 8
  ((w >>> shift) &&& 0xff#32).toNat.toUInt8


/-- Mirrors `Step.lean`'s private `countLeadingZerosFrom`: counts leading
zero bits in `w` from the MSB (bit 31), stopping at the first set bit;
`32` if `w` is all-zero. `fuel` bounds the scan to the remaining unscanned
bit positions (`pos .. 31`). Used by `cloSpec`/`clzSpec` below (`clo_spec_raw`/
`clz_spec_raw`). -/
def countLeadingZerosFromSpec (w : W32) : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos => if w.getMsbD pos then pos else countLeadingZerosFromSpec w fuel (pos + 1)

/-- Mirrors `Step.lean`'s private `countLeadingZeros`: counts leading zero
bits in `w`, from the MSB. Used by `clz_spec_raw` below. -/
def countLeadingZerosSpec (w : W32) : Nat :=
  countLeadingZerosFromSpec w 32 0

/-- Mirrors `Step.lean`'s private `countLeadingOnes`: counts leading one
bits in `w`, from the MSB, via `countLeadingZerosSpec (~~~w)` (a run of
`1`s in `w` is exactly a run of `0`s in `~~~w`). Used by `clo_spec_raw`
below. -/
def countLeadingOnesSpec (w : W32) : Nat :=
  countLeadingZerosSpec (~~~w)

/-- Mirrors `Step.lean`'s private `signExtLowByte`: sign-extends the low
byte of a register value to 32 bits. Used by `seb_spec_raw` below. -/
def signExtLowByteSpec (w : W32) : W32 :=
  (w.extractLsb 7 0).signExtend 32

/-- Mirrors `Step.lean`'s private `lowBitsMask`: a `W32` with the low `n`
bits set and all higher bits clear (`n = 0..32`). Used by `ext`/`ins` to
mask out a `size`-bit field (`ext_spec_raw`/`ins_spec_raw` below). -/
def lowBitsMaskSpec (n : Nat) : W32 :=
  ((1#32) <<< n) - 1#32


/-! ## Group 1 — global invariants preserved by one step -/

/-- A `writeReg` call never moves the program counter: it only ever touches
the register file. Used throughout to simplify the "next state" shape that
`step` produces after an instruction writes a register. -/
theorem writeReg_pc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).pc = s.pc := by
  unfold writeReg; split <;> rfl

/-- A `writeReg` call never changes `hi`, `lo`, `mem`, or `out` — only the
register file. -/
theorem writeReg_hi (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).hi = s.hi := by
  unfold writeReg; split <;> rfl

theorem writeReg_lo (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).lo = s.lo := by
  unfold writeReg; split <;> rfl

theorem writeReg_out (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).out = s.out := by
  unfold writeReg; split <;> rfl

/-- **`$zero` is never actually written.** Writing any value to any register
never changes what register `0` reads back: either the write targets `0`
itself (ignored outright, INSTRUCTION-REF Global rule §2) or it targets a
different register, which cannot disturb slot `0`. This is the building
block for "`$zero` always reads `0`" as a full-run invariant: every write in
the simulator goes through `writeReg`, so register `0` can never pick up a
nonzero value no matter how many steps run, as long as it started at `0`
(which `initialState` guarantees — see `State.lean`). -/
theorem writeReg_preserves_zero_slot (s : State) (i : Fin 32) (v : W32) :
    readReg (writeReg s i v) 0 = readReg s 0 := by
  unfold writeReg readReg
  split
  · rfl
  · next h =>
    have hne : i ≠ (0 : Fin 32) := by
      intro heq; exact h (by simp [heq])
    simp [Array.set!, Array.getD_eq_getD_getElem?, hne]

/-- Writing `v` to a nonzero register `i` and immediately reading `i` back
gives exactly `v` (the one register `writeReg` actually changes). -/
theorem writeReg_reads_back (s : State) (i : Fin 32) (v : W32) (hne : i ≠ 0)
    (hsize : s.regs.size = 32) :
    readReg (writeReg s i v) i = v := by
  unfold writeReg readReg
  rw [if_neg (by simpa using hne)]
  simp [Array.set!, Array.getD_eq_getD_getElem?, hsize, i.isLt]

/-- **Global invariant: `$zero` always reads `0`.** If `step` produces a
next state, register `0` reads the same thing after the step as before.
Combined with `initialState` seeding register `0` to `0` (`State.lean`),
this shows `$zero` reads `0` at every point in every run, matching
INSTRUCTION-REF Global rule 2 ("writes to `$zero` are a no-op").

STALL NOTE (original, written when only a handful of `_spec_raw` theorems
existed): a fully generic proof needs `step` unfolded and then every one of
the `Instruction` constructors handled uniformly. The arithmetic/logic/
mult/div instructions (no memory access, no branching) close cleanly with
`cases instr <;> simp_all [writeReg_preserves_zero_slot]`-style reasoning,
but the instructions whose body is itself a `match`/`if` on a memory read
or a branch condition need that inner match/if exposed before the
combinator can see register-file structure, and `dsimp`/`split` refuse to
expose it uniformly across all of them in one tactic script.

UPDATE: this file has since grown a `_spec_raw` theorem for nearly every
instruction family, which changes the picture completely \u2014 see
`step_preserves_zero_register_nontrivial` below (Group 6), which closes the
invariant for every instruction that has a `_spec_raw` theorem (around 70
of the ~112 `Instruction` constructors, including every memory access,
branch, and jump instruction the old note above singled out as
problematic) by dispatching on the decoded instruction and `rw`ing with
that instruction's own `_spec_raw` equation \u2014 one case per instruction
rather than one generic combinator, exactly the "cost of one lemma per
instruction" this note predicted, except it turns out that cost was already
mostly paid by Group 2's per-instruction lemmas. The remaining gap (`clo
clz mul seb seh wsbh ext ins`, `lwl lwr swl swr`, the REGIMM trap-immediate
family, `syscall`, the CP0 family, and the entire COP1/FPU subset) has no
`_spec_raw` theorem yet to dispatch to; left `sorry` here and in
`step_preserves_zero_register_nontrivial`'s own trailing case. -/
theorem step_preserves_zero_register (p : Program) (s s' : State)
    (hstep : step p s = StepResult.next s') : readReg s' 0 = readReg s 0 := by
  sorry


/-! ## Group 2 — per-instruction specs (semantics-critical subset) -/

/-- **`add` computes the exact sum, or traps exactly on signed overflow.**
This is `step`'s own code, restated with public names: the raw sum is
formed, `addOverflowsSpec` is INSTRUCTION-REF's Java-derived overflow test
("add" section), and the instruction either halts with
`arithmeticOverflow` or writes the sum and advances the program counter by
4. Every other `add`-related theorem is a corollary of this one. -/
theorem add_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        StepResult.halt .arithmeticOverflow
      else
        StepResult.next
          { (writeReg s (regIdxSpec rd) sumBV) with
            pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Closed weaker version of `step_preserves_zero_register`, for the
representative case of `add` (the trickiest arithmetic instruction, since it
has both a halting branch and a register-writing branch): whichever branch
`step` takes, register `0` reads the same value before and after. -/
theorem step_add_preserves_zero_register (p : Program) (s s' : State) (w rs rt rd : W32)
    (hfw : fetchWord p s.pc = some w) (hdw : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none)
    (hstep : step p s = StepResult.next s') : readReg s' 0 = readReg s 0 := by
  rw [add_spec_raw p s w rs rt rd hfw hdw hpb] at hstep
  dsimp only at hstep
  split at hstep
  · cases hstep
  · injection hstep with hs
    rw [← hs]
    exact writeReg_preserves_zero_slot s _ _

/-- **`sub` computes the exact difference, or traps exactly on signed
overflow.** Mirrors `add_spec_raw`; `subOverflowsSpec` is INSTRUCTION-REF's
"sub" overflow test. -/
theorem sub_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let diffBV := av - bv
      if subOverflowsSpec (asSigned av) (asSigned bv) (asSigned diffBV) then
        StepResult.halt .arithmeticOverflow
      else
        StepResult.next
          { (writeReg s (regIdxSpec rd) diffBV) with
            pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`addi` computes `$rs + sext16(imm)` exactly, or traps exactly on
signed overflow.** The immediate is sign-extended first (INSTRUCTION-REF
"addi" section), then the same overflow test as `add` applies. -/
theorem addi_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addi rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let av := readReg s (regIdxSpec rs)
      let bv := signExt16 imm
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        StepResult.halt .arithmeticOverflow
      else
        StepResult.next
          { (writeReg s (regIdxSpec rt) sumBV) with
            pc := (writeReg s (regIdxSpec rt) sumBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`div` by a nonzero divisor truncates toward zero; the remainder takes
the dividend's sign** (Lean's `Int.tdiv`/`Int.tmod`, matching Java's `/`/`%`
used by MARS — INSTRUCTION-REF "div" section). **`div` by zero leaves `hi`
and `lo` untouched and does not halt** (SPEC-NOTES §9.2 / INSTRUCTION-REF
"div" MARS-note: this is a deliberate MIPS32-spec reading, not a MARS bug).
Both cases always advance the program counter by 4. -/
theorem div_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      if b == 0 then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b), pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `div_spec_raw`: dividing by `0` leaves `hi`/`lo` exactly as
they were and does not halt — INSTRUCTION-REF "div" MARS-note, SPEC-NOTES
§9.2. -/
theorem div_by_zero_spec (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [div_spec_raw p s w rs rt hfetch hdecode hpb, hzero]
  rfl

/-- Corollary of `div_spec_raw`: with a negative dividend and a nonzero
divisor, the remainder (`hi`) takes the dividend's sign, since `Int.tmod`
truncates toward zero (same as Java's `%`, which Java-derived MARS uses —
INSTRUCTION-REF "div" section, "remainder takes the sign of the dividend"). -/
theorem div_negative_dividend_spec (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hpb : s.pendingBranch = none)
    (hnz : asSigned (readReg s (regIdxSpec rt)) ≠ 0)
    (hneg : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s =
      StepResult.next
        { s with
          lo := ofInt32 ((asSigned (readReg s (regIdxSpec rs))).tdiv (asSigned (readReg s (regIdxSpec rt))))
          hi := ofInt32 ((asSigned (readReg s (regIdxSpec rs))).tmod (asSigned (readReg s (regIdxSpec rt))))
          pc := s.pc + 4#32 } := by
  rw [div_spec_raw p s w rs rt hfetch hdecode hpb]
  have : ¬ (asSigned (readReg s (regIdxSpec rt)) == 0) := by
    simp [hnz]
  rw [if_neg (by simpa using this)]

/-- **`beq`/`bne` branch target and condition, in one equation — real
MIPS32 one-delay-slot semantics.** Mirrors `step`'s own code: the
comparison `$rs == $rt` picks between an ordinary fallthrough to `PC_next`
and *scheduling* (not jumping to) `PC_next + (sext16(offset) << 2)` via
`pendingBranch`, with `beq` and `bne` using the comparison the opposite way
around. A taken branch never updates `pc` past `PC_next` in this same step
— the delay-slot instruction at `PC_next` always executes first; the
schedule is committed by the *next* step's `advance` (`Step.lean`), see
`beq_taken_delay_slot_lands_on_target` below for the two-step composition
(SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3 — this supersedes the
old no-delay-slot MARS-default behavior). The hypothesis `hpb` restricts
this equation to the ordinary case where `s` is not itself sitting in
another pending delay slot; see `branch_in_delay_slot_halts` for that other
case. -/
theorem beq_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

theorem bne_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`beq`, taken**: when `$rs = $rt`, `beq` schedules
`PC_next + (offset << 2)` as the pending delay-slot transfer and itself
falls through to `PC_next` — it does **not** jump immediately
(INSTRUCTION-REF Global rule 3: real MIPS32 always executes one delay-slot
instruction first). -/
theorem beq_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [beq_spec_raw p s w rs rt imm hfetch hdecode hpb, if_pos (by simpa using htaken)]

/-- **`beq`, not taken**: when `$rs ≠ $rt`, control simply falls through to
`PC_next`, exactly as an ordinary instruction — no `pendingBranch` is ever
set (INSTRUCTION-REF "beq" section). -/
theorem beq_not_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [beq_spec_raw p s w rs rt imm hfetch hdecode hpb, if_neg (by simpa using hnot)]

/-- **`bne`, taken**: when `$rs ≠ $rt`, schedules `PC_next + (offset << 2)`
— the mirror image of `beq`, same one-delay-slot discipline. -/
theorem bne_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bne_spec_raw p s w rs rt imm hfetch hdecode hpb, if_neg (by simpa using htaken)]

/-- **`bne`, not taken**: when `$rs = $rt`, falls through to `PC_next`. -/
theorem bne_not_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [bne_spec_raw p s w rs rt imm hfetch hdecode hpb, if_pos (by simpa using hnot)]

/-- **Two-step delay-slot composition for a taken `beq`**: the branch's own
step only schedules the target (`beq_taken_spec`); it is the *following*
step — executing the delay-slot instruction — that actually lands `pc` on
it (`advance` in `Step.lean`, triggered by any ordinary, non-branch-like
instruction; demonstrated concretely here with `sll $zero,$zero,0` i.e.
`nop` as the delay-slot filler). This is the theorem that directly
witnesses "real MIPS32 branch delay slot" as a two-instruction behavior,
matching the task's exact semantics rather than only the one-step schedule
captured by `beq_taken_spec`. -/
theorem beq_taken_delay_slot_lands_on_target (p : Program) (s : State) (w w2 rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt))
    (hfetch2 : fetchWord p (s.pc + 4#32) = some w2)
    (hdecode2 : decode w2 = some (.sll 0#32 0#32 0#32)) :
    ∃ s1 s2,
      step p s = StepResult.next s1 ∧
      step p s1 = StepResult.next s2 ∧
      s2.pc = (s.pc + 4#32) + (signExt16 imm <<< 2) := by
  have h1 := beq_taken_spec p s w rs rt imm hfetch hdecode hpb htaken
  have h2 : step p { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } = StepResult.next { s with pc := (s.pc + 4#32) + (signExt16 imm <<< 2), pendingBranch := none } := by
    unfold step
    rw [show fetchWord p ({ s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } : State).pc = some w2 from hfetch2]
    dsimp only
    rw [hdecode2]
    dsimp only
    rfl
  exact ⟨_, _, h1, h2, rfl⟩

/-- **`jal` links `$ra` to `pc + 8` — past the delay slot, not `PC_next`
(`pc + 4`) — and schedules a jump to a target whose top 4 bits come from
`PC_next`, not from `jal`'s own address** (INSTRUCTION-REF Global rule 3:
real MIPS32's `jal` link value is the address of the instruction *after*
the delay slot, since the delay-slot instruction itself still executes
before control can return to `$ra`). Like `beq`/`bne`, `jal` schedules the
jump via `pendingBranch` and itself falls through to `PC_next`; it never
jumps in the same step. -/
theorem jal_spec_raw (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { (writeReg s 31 (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `jal_spec_raw`: `$ra` (register 31) reads back exactly
`pc + 8`, i.e. the address of the instruction *after* the delay slot
(`jal`'s own address plus 8), not `pc + 4`. -/
theorem jal_sets_ra (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none)
    (hsize32 : s.regs.size = 32) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  refine ⟨_, jal_spec_raw p s w target hfetch hdecode hpb, ?_⟩
  show readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32,
    BitVec.add_assoc]
  congr 1

/-- **A branch/jump occurring in another's delay slot halts.** Real MIPS32
leaves this architecturally discouraged/implementation-defined; rather than
pick an arbitrary behavior, `step` reports `HaltReason.branchInDelaySlot`
whenever the incoming state already has a scheduled transfer
(`s.pendingBranch = some _`) and the instruction about to execute is itself
one of the six branch/jump instructions (`isBranchLikeSpec`)
(SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3). -/
theorem branch_in_delay_slot_halts (p : Program) (s : State) (w : W32) (instr : Instruction)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some instr)
    (hpb : s.pendingBranch.isSome = true) (hbr : isBranchLikeSpec instr = true) :
    step p s = StepResult.halt .branchInDelaySlot := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  cases pb with
  | none => simp at hpb
  | some t =>
    unfold step
    rw [hfetch]
    dsimp only
    rw [hdecode]
    dsimp only
    cases instr <;> simp_all [isBranchLikeSpec] <;> rfl

/-- **`lw` composes a big-endian word from memory at `$rs + sext16(offset)`,
or halts with `addressError` on a misaligned effective address**
(INSTRUCTION-REF "lw" section; SPEC-NOTES §9.3 — the offset is
sign-extended, unlike MARS's own latent zero-extension bug for raw-decoded
binaries). -/
theorem lw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => StepResult.halt (.addressError addr)
      | some v =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `lw_spec_raw`: a misaligned effective address halts with
`addressError`, naming that exact address. -/
theorem lw_misaligned_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step p s = StepResult.halt (.addressError (readReg s (regIdxSpec rs) + signExt16 imm)) := by
  rw [lw_spec_raw p s w rs rt imm hfetch hdecode hpb]
  dsimp only
  rw [show readMemWord s (readReg s (regIdxSpec rs) + signExt16 imm) = none by
    unfold readMemWord
    rw [if_pos hmisaligned]]

/-- **`lb` sign-extends the loaded byte; `lbu` zero-extends it** — same
effective address, same byte, different widening (INSTRUCTION-REF "lb" /
"lbu" sections). This single theorem packages both, since comparing them
side by side is the whole point of the spec. -/
theorem lb_lbu_spec_raw (p : Program) (s : State) (wb wbu rs rt imm : W32)
    (hfetchB : fetchWord p s.pc = some wb) (hdecodeB : decode wb = some (.lb rs rt imm))
    (hfetchBU : fetchWord p s.pc = some wbu) (hdecodeBU : decode wbu = some (.lbu rs rt imm))
    (hpb : s.pendingBranch = none) :
    (step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => StepResult.halt (.addressError addr)
      | some b =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) ((BitVec.ofNat 8 b.toNat).signExtend 32)) with
            pc := (writeReg s (regIdxSpec rt) ((BitVec.ofNat 8 b.toNat).signExtend 32)).pc + 4#32 })
    ∧
    (step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => StepResult.halt (.addressError addr)
      | some b =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) (BitVec.ofNat 32 b.toNat)) with
            pc := (writeReg s (regIdxSpec rt) (BitVec.ofNat 32 b.toNat)).pc + 4#32 }) := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  constructor
  · unfold step
    rw [hfetchB]
    dsimp only
    rw [hdecodeB]
    dsimp only
    rfl
  · unfold step
    rw [hfetchBU]
    dsimp only
    rw [hdecodeBU]
    dsimp only
    rfl

/-- **syscall 1 (`PrintInt`) appends the signed decimal rendering of `$a0`
to `out`, with no trailing newline**, and advances the program counter by 4
(INSTRUCTION-REF "syscall 1 — PrintInt": `Integer.toString`, decimal,
signed; no other state changes). -/
theorem syscall1_spec (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .syscall)
    (hv0 : readReg s (regIdxSpec 2#32) = 1#32) (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next { s with out := s.out ++ toString (asSigned (readReg s (regIdxSpec 4#32))), pc := s.pc + 4#32 } := by
  sorry

/-- **syscall 10 (`Exit`) halts the program cleanly**, ignoring every
register — modeled as `HaltReason.exit`, distinct from every error halt
(INSTRUCTION-REF "syscall 10 — Exit"). -/
theorem syscall10_spec (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .syscall)
    (hv0 : readReg s (regIdxSpec 2#32) = 10#32) :
    step p s = StepResult.halt .exit := by
  sorry

/-! STALL NOTE on `syscall1_spec`/`syscall10_spec` (updated after a fresh
attempt following the house "`obtain`/`subst`/`unfold step`" recipe, with
`hv0` substituted in before `unfold step` as suggested):

**`syscall1_spec` is not just hard to prove — as stated, it is false.**
Every other `mkNext`-based `_spec_raw` theorem in this file (every
arithmetic/logic/load/store/trap instruction) carries a
`hpb : s.pendingBranch = none` hypothesis, because `mkNext`'s `advance` call
resolves a pending delay-slot transfer when one is scheduled: if
`s.pendingBranch = some target`, the *next* `pc` is `target` (and
`pendingBranch` is cleared to `none`), not `s.pc + 4#32`. `syscall1_spec`'s
statement has no such hypothesis, and `syscall`'s `1` case **does** go
through `mkNext`. Concretely, for `s.pendingBranch = some 0xabcd#32` and
`$v0 = 1`, `step` actually produces `pc = 0xabcd#32` and
`pendingBranch = none`, whereas the theorem's claimed right-hand side
`{ s with out := ..., pc := s.pc + 4#32 }` keeps
`pendingBranch = some 0xabcd#32` unchanged and sets `pc := s.pc + 4#32` —
these disagree (checked directly: build `s` via `setRegsSpec` with
`pendingBranch := some 0xabcd#32`, `$v0 := 1`, and `#eval`-compare
`step (prog1Spec .syscall) s` against the theorem's claimed RHS — the `pc`/
`pendingBranch` components differ). So no amount of tactic cleverness
closes `syscall1_spec` as currently stated — it is missing a `hpb`-style
hypothesis every other `mkNext`-based theorem has. Per this task's scope
(no weakening/changing an existing claim), this is reported rather than
"fixed" by adding the missing hypothesis.

**`syscall10_spec`'s claim, by contrast, is true** (its `10 => halt .exit`
case never calls `mkNext`/`advance`, so it is independent of
`pendingBranch`; verified concretely by `#eval` on states with
`pendingBranch := none` and `:= some _` alike, both giving `.exit`), but it
still does not close with the tools available here, for a *different*,
purely proof-engineering reason than the original note's "`regs.size`
invariant" diagnosis (which turned out not to be the real obstacle). The
actual blocker: `readReg s (regIdxSpec 2#32) = 10#32` (`hv0`) is a
hypothesis *about* `s`, not a term that appears syntactically anywhere in
the goal until `step`/`execInstr` is unfolded all the way down to the
`match (readReg s 2).toNat with | 1 => ... | 10 => .exit | ...` dispatch —
but reaching that point requires delta-unfolding the *private* `execInstr`
(and, for a normal form `rw`/`dsimp` can match against, its sibling
branches' `mkNext`/`readCString`/`printStringFuel` helpers too, also
private), which `unfold`/`simp [name]` cannot do from this file at all (the
names are not visible outside `Step.lean`), and which `rw`/`dsimp only`
(syntactic tactics, not delta-unfolding ones) do not do automatically
either. Only a whole-term `rfl`/`decide` performs the kernel-level
delta-unfolding needed to get through private definitions (that is how
every other `_spec_raw` theorem in this file closes, including ones that
change `pendingBranch`/`hi`/`lo`/`mem`) — but `rfl`/`decide` only
*computes*, it does not consult hypotheses, so it cannot use `hv0` to turn
the symbolic `(readReg s 2).toNat` into the literal `10` the match needs in
order to reduce. This is a genuine chicken-and-egg: exposing the match for
`rw [hv0]` requires unfolding, but unfolding far enough to expose it
requires already knowing which branch to reduce to. (Confirmed
experimentally: `unfold step; rw [hfetch]; dsimp only; rw [hdecode]` leaves
the goal as the fully opaque `execInstr✝ {...} w Instruction.syscall =
StepResult.halt HaltReason.exit` — zero progress into `execInstr`'s body —
and both `rw [hv0]` and `simp only [hv0]` against that goal fail, with "did
not find an occurrence"/"made no progress" respectively.) Reconstructing
`execInstr`'s syscall dispatch by hand via `show`/`change` (to get an
explicit term `rw`/`simp` can see into) is blocked the same way as naming
`execInstr` directly: cases `1`/`4`/`11` of the dispatch call the private
`mkNext`/`readCString`/`printStringFuel`, whose names cannot be typed in
this file either, so not even an approximate reconstruction parses, let
alone type-checks as definitionally equal. Left `sorry` on both. The closed
weaker versions below pin `s` down to a fully concrete, well-formed state
(via `initialState`) and verify the same claims by `#guard` (compiled
evaluation — required for anything that touches `Program`/`State.mem`,
which are backed by `cbv_opaque` `Std.HashMap`s and are not
kernel-reducible by `decide`/`rfl`). -/

/-! ADDENDUM (post-merge, orchestrator pass): `syscall1_spec` was also found
(separately, on the `proof/proof-stalls` branch) to be missing a
`hpb : s.pendingBranch = none` hypothesis every other `mkNext`-based
theorem in this file carries -- without it, the claimed right-hand side is
simply false whenever a delay-slot transfer is pending (checked
concretely: for `s.pendingBranch = some 0xabcd#32`, `step` actually
produces `pc = 0xabcd#32`, not `s.pc + 4#32`). That hypothesis has been
added to the statement above, fixing the false claim regardless of
provability. Tried closing it with the added hypothesis via the standard
recipe plus a final `rw [hv0]`: it fails with the exact same "did not find
an occurrence" error described above for `syscall10_spec` -- confirming
this is the identical chicken-and-egg blocker, not a second, independent
issue, and that fixing the missing hypothesis alone does not unstall the
proof. Left `sorry`. -/


/-- One-instruction program containing `instr` at `textBase`, for building
concrete examples below. -/
def prog1Spec (instr : Instruction) : Program := (∅ : Program).insert textBase (encode instr)

/-- Apply a list of register writes to a state, for building concrete
examples below. -/
def setRegsSpec (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeReg acc kv.1 kv.2) s

/-- A sequential program starting at `base`, for building concrete
delay-slot examples below (mirrors `Step.lean`'s test-only `buildProg`). -/
def buildProgSpec (base : W32) (instrs : List Instruction) : Program :=
  instrs.zipIdx.foldl (fun acc (instr, i) => acc.insert (base + BitVec.ofNat 32 (4 * i)) (encode instr))
    (∅ : Program)

-- Closed weaker version of `syscall1_spec`: a concrete syscall-1 call
-- appends the decimal rendering of `$a0`, with no trailing newline.
#guard (match step (prog1Spec .syscall) (setRegsSpec (initialState textBase) [(2, 1#32), (4, 5#32)]) with
        | .next s => s.out
        | .halt _ => "unreachable") = "5"

-- Closed weaker version of `syscall10_spec`: a concrete syscall-10 call
-- halts with `.exit`.
#guard (match step (prog1Spec .syscall) (setRegsSpec (initialState textBase) [(2, 10#32)]) with
        | .next _ => false
        | .halt r => r == .exit) = true

/-! ## Group 3 — satisfiable examples

Each theorem above is instantiated on a concrete program/state with every
hypothesis discharged, confirming the hypotheses are not vacuous. Anything
that runs `step` on a concrete `Program`/`State.mem` is checked with
`#guard` (compiled evaluation): `Program`/`State.mem` are `Std.HashMap`s
marked `cbv_opaque`, so `decide`/`rfl` get stuck on them, but the pure
arithmetic side conditions (`decode`, overflow tests, register indices) are
checked with `by decide`. -/

-- `add_spec_raw`: 5 + 7 does not overflow, giving a `.next` state with
-- `$t2 = 12` and `pc` advanced by 4.
example : decode (encode (Instruction.add 8#32 9#32 10#32)) = some (.add 8#32 9#32 10#32) := by decide
#guard (match step (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with
        | .next s => readReg s 10 == 12#32 && s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `step_add_preserves_zero_register`: a concrete non-overflowing `add`
-- leaves register `0` at `0`.
#guard (match step (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with
        | .next s => readReg s 0 == 0#32
        | .halt _ => false) = true

-- `sub_spec_raw`: `0x80000000 - 1` overflows (INT_MIN minus a positive is
-- itself non-negative after wraparound), so `sub` halts.
#guard (match step (prog1Spec (.sub 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 1#32)]) with
        | .next _ => false
        | .halt r => r == .arithmeticOverflow) = true

-- `addi_spec_raw`: `addi $t1, $zero, 5` does not overflow.
#guard (match step (prog1Spec (.addi 0#32 9#32 5#32)) (initialState textBase) with
        | .next s => readReg s 9 == 5#32
        | .halt _ => false) = true

-- `div_by_zero_spec`: dividing by `0` leaves a pre-seeded `hi`/`lo` alone.
#guard (match step (prog1Spec (.div 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 10#32), (9, 0#32)]) with
            hi := 0xdeadbeef#32, lo := 0xcafef00d#32 } with
        | .next s => s.hi == 0xdeadbeef#32 && s.lo == 0xcafef00d#32
        | .halt _ => false) = true

-- `div_negative_dividend_spec`: `-17 / 5` truncates to `-3`; the remainder
-- `-2` carries the dividend's sign (`tdiv`/`tmod`, not Euclidean division).
#guard (match step (prog1Spec (.div 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffef#32), (9, 5#32)]) with
        | .next s => s.lo == 0xfffffffd#32 && s.hi == 0xfffffffe#32
        | .halt _ => false) = true

-- `beq_taken_spec`/`beq_not_taken_spec`: equal registers schedule the
-- target via `pendingBranch` and fall through to the delay slot first
-- (real MIPS32 one-delay-slot semantics); unequal registers fall through
-- exactly as an ordinary instruction.
#guard (match step (prog1Spec (.beq 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.beq 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `bne_taken_spec`/`bne_not_taken_spec`: the mirror image of `beq`.
#guard (match step (prog1Spec (.bne 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true

-- `beq_taken_delay_slot_lands_on_target`: the delay-slot instruction's own
-- step is what actually lands `pc` on the scheduled target.
#guard (match step (buildProgSpec textBase [.beq 8#32 9#32 3#32, .sll 0#32 0#32 0#32])
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s1 =>
          (match step (buildProgSpec textBase [.beq 8#32 9#32 3#32, .sll 0#32 0#32 0#32]) s1 with
            | .next s2 => s2.pc == textBase + 4#32 + 12#32
            | .halt _ => false)
        | .halt _ => false) = true

-- `jal_sets_ra`: `$ra` ends up exactly `pc + 8` (past the delay slot), and
-- the jump is scheduled (not immediate) with its target's top 4 bits
-- coming from `pc + 4`, not from `jal`'s own address.
#guard (match step (prog1Spec (.jal 0x1000#32)) (initialState textBase) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some 0x4000#32
        | .halt _ => false) = true

-- `lw_spec_raw`: a big-endian word loaded back out.
#guard (match
          (writeMemWord (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
            0x10010000#32 0x12345678#32).bind
          (fun s => some (step (prog1Spec (.lw 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x12345678#32
        | _ => false) = true

-- `lw_misaligned_spec`: an unaligned effective address halts with the
-- exact failing address.
#guard (match step (prog1Spec (.lw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next _ => false
        | .halt r => r == .addressError 0x10010001#32) = true

-- `lb_lbu_spec_raw`: the same high-bit byte sign-extends under `lb` and
-- zero-extends under `lbu`.
#guard (match (writeMemByte (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x80).bind (fun s => some (step (prog1Spec (.lb 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0xffffff80#32
        | _ => false) = true
#guard (match (writeMemByte (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x80).bind (fun s => some (step (prog1Spec (.lbu 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x00000080#32
        | _ => false) = true

-- `syscall1_concrete_example`/`syscall10`: already given above as the
-- closed weaker versions of `syscall1_spec`/`syscall10_spec`.

/-! ## Group 4 — bad-output rejection

The spec also rejects known-wrong behaviors: outcomes a buggy
implementation might plausibly produce, but which `step` provably does
not. -/

/-- **Overflow does not silently wrap.** A buggy `add` might wrap
`0x7fffffff + 1` to `0x80000000` and continue; the real `add` halts with
`arithmeticOverflow` instead, so it can *never* reach a `.next` state on
these operands. -/
theorem add_overflow_not_wrapped (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add 8#32 9#32 10#32))
    (hpb : s.pendingBranch = none)
    (ha : readReg s (regIdxSpec 8#32) = 0x7fffffff#32)
    (hb : readReg s (regIdxSpec 9#32) = 1#32) :
    ¬ ∃ s', step p s = StepResult.next s' := by
  rintro ⟨s', hs'⟩
  rw [add_spec_raw p s w 8#32 9#32 10#32 hfetch hdecode hpb] at hs'
  dsimp only at hs'
  rw [ha, hb] at hs'
  rw [if_pos (by decide)] at hs'
  cases hs'

-- Concrete witness: `0x7fffffff + 1` really does halt, not wrap to
-- `0x80000000`.
#guard (match step (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x7fffffff#32), (9, 1#32)]) with
        | .next _ => false
        | .halt r => r == .arithmeticOverflow) = true

/-- **A write to `$zero` is never observable.** No matter what value gets
"written" to register `0`, reading it straight back always gives `0` —
exactly INSTRUCTION-REF Global rule 2, stated as a rejection of the bad
behavior "the write took effect". -/
theorem zero_write_not_observable (s : State) (v : W32) (hv : readReg s 0 ≠ v) :
    readReg (writeReg s 0 v) 0 ≠ v := by
  rw [writeReg_preserves_zero_slot]
  exact hv

#guard decide (readReg (writeReg (initialState textBase) 0 0xdeadbeef#32) 0 ≠ 0xdeadbeef#32) = true

/-- **A misaligned `lw` never produces a next state.** A buggy
implementation might round the address down (or up) and load anyway; the
real `lw` always halts on a misaligned effective address, so there is no
state `s'` it could step to. -/
theorem lw_misaligned_no_next (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    ¬ ∃ s', step p s = StepResult.next s' := by
  rintro ⟨s', hs'⟩
  rw [lw_misaligned_spec p s w rs rt imm hfetch hdecode hpb hmisaligned] at hs'
  cases hs'

-- Concrete witness: `lw` from a `+1`-misaligned address halts, it never
-- "succeeds anyway" with some rounded value.
#guard (match step (prog1Spec (.lw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next _ => false
        | .halt _ => true) = true

/-! ## Group 5 — R-type logic/compare specs (`addu`,`subu`,`and`,`or`,`xor`,
`nor`,`slt`,`sltu`,`movn`,`movz`)

These ten R-type instructions round out Group 2's arithmetic/logic coverage.
`addu`/`subu` are `add`/`sub` with the overflow trap removed entirely — plain
two's-complement wraparound, never a halt (INSTRUCTION-REF "addu"/"subu"
sections). `and`/`or`/`xor`/`nor` are the four bitwise ops, with no overflow
concept whatsoever (INSTRUCTION-REF "and"/"or"/"xor"/"nor" sections).
`slt`/`sltu` write a `0`/`1` comparison result, signed vs. unsigned
(INSTRUCTION-REF "slt"/"sltu" sections). `movn`/`movz` are MIPS32r2
conditional moves whose defining feature — `$rd` left genuinely untouched
(not zeroed) when the condition fails — is exactly what the corollaries
after their raw specs pin down, per this project's CLAUDE.md §4 ("the spec
must reject bad behaviour"): a buggy always-overwrite implementation would
fail `movn_not_taken_unchanged`/`movz_not_taken_unchanged` below. -/

/-- **`addu` computes `$rs + $rt` with plain wraparound and never traps** —
same formula as `add_spec_raw` minus the overflow check entirely
(INSTRUCTION-REF "addu" section). -/
theorem addu_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addu rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let sumBV := readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) sumBV) with
          pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`subu` computes `$rs - $rt` with plain wraparound and never traps**
(INSTRUCTION-REF "subu" section). -/
theorem subu_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.subu rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let diffBV := readReg s (regIdxSpec rs) - readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) diffBV) with
          pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`and` computes the bitwise AND of `$rs`/`$rt`** — no overflow concept
at all (INSTRUCTION-REF "and" section). -/
theorem and_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.and rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := readReg s (regIdxSpec rs) &&& readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`or` computes the bitwise OR of `$rs`/`$rt`** (INSTRUCTION-REF "or"
section). -/
theorem or_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.or rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := readReg s (regIdxSpec rs) ||| readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`xor` computes the bitwise XOR of `$rs`/`$rt`** (INSTRUCTION-REF "xor"
section). -/
theorem xor_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.xor rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := readReg s (regIdxSpec rs) ^^^ readReg s (regIdxSpec rt)
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`nor` computes the bitwise NOR (`~($rs | $rt)`) of `$rs`/`$rt`**
(INSTRUCTION-REF "nor" section). -/
theorem nor_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.nor rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := ~~~(readReg s (regIdxSpec rs) ||| readReg s (regIdxSpec rt))
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`slt` writes `1` to `$rd` iff `$rs < $rt` as a signed comparison, else
`0`** (INSTRUCTION-REF "slt" section). -/
theorem slt_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.slt rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := if asSigned (readReg s (regIdxSpec rs)) < asSigned (readReg s (regIdxSpec rt))
               then 1#32 else 0#32
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sltu` writes `1` to `$rd` iff `$rs < $rt` as an unsigned comparison,
else `0`** (INSTRUCTION-REF "sltu" section). -/
theorem sltu_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sltu rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := if (readReg s (regIdxSpec rs)).toNat < (readReg s (regIdxSpec rt)).toNat
               then 1#32 else 0#32
      StepResult.next
        { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`movn` moves `$rs` into `$rd` iff `$rt ≠ 0`; otherwise `$rd` is left
completely unchanged** — a true conditional no-op, not "write `0`"
(INSTRUCTION-REF "movn" section). This is the full case split; see
`movn_taken_spec`/`movn_not_taken_spec`/`movn_not_taken_unchanged` below for
the two branches isolated. -/
theorem movn_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movn rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rt) != 0#32 then
        StepResult.next
          { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))) with
            pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))).pc + 4#32 }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`movn`, condition true (`$rt ≠ 0`)**: `$rd` actually receives `$rs`'s
value. -/
theorem movn_taken_spec (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movn rs rt rd))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rt) ≠ 0#32) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))).pc + 4#32 } := by
  rw [movn_spec_raw p s w rs rt rd hfetch hdecode hpb, if_pos (by simpa using htaken)]

/-- **`movn`, condition false (`$rt = 0`)**: the state advances with no
register write at all — `$rd` is not touched, not zeroed. -/
theorem movn_not_taken_spec (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movn rs rt rd))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rt) = 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [movn_spec_raw p s w rs rt rd hfetch hdecode hpb, if_neg (by simp [hnot])]

/-- **"Bad output rejection" for `movn`**: whenever the condition fails
(`$rt = 0`), the resulting state's `$rd` reads back *exactly* its pre-step
value — a buggy implementation that always overwrote `$rd` regardless of
`$rt` could never satisfy this. -/
theorem movn_not_taken_unchanged (p : Program) (s s' : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movn rs rt rd))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rt) = 0#32)
    (hstep : step p s = StepResult.next s') :
    readReg s' (regIdxSpec rd) = readReg s (regIdxSpec rd) := by
  rw [movn_not_taken_spec p s w rs rt rd hfetch hdecode hpb hnot] at hstep
  injection hstep with hs
  rw [← hs]
  rfl

/-- **`movz` moves `$rs` into `$rd` iff `$rt = 0`; otherwise `$rd` is left
completely unchanged** — the mirror image of `movn` (INSTRUCTION-REF "movz"
section). -/
theorem movz_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movz rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rt) == 0#32 then
        StepResult.next
          { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))) with
            pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))).pc + 4#32 }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`movz`, condition true (`$rt = 0`)**: `$rd` actually receives `$rs`'s
value. -/
theorem movz_taken_spec (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movz rs rt rd))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rt) = 0#32) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs))).pc + 4#32 } := by
  rw [movz_spec_raw p s w rs rt rd hfetch hdecode hpb, if_pos (by simpa using htaken)]

/-- **`movz`, condition false (`$rt ≠ 0`)**: the state advances with no
register write at all. -/
theorem movz_not_taken_spec (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movz rs rt rd))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rt) ≠ 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [movz_spec_raw p s w rs rt rd hfetch hdecode hpb, if_neg (by simpa using hnot)]

/-- **"Bad output rejection" for `movz`**: whenever the condition fails
(`$rt ≠ 0`), the resulting state's `$rd` reads back *exactly* its pre-step
value — a buggy implementation that always overwrote `$rd` regardless of
`$rt` could never satisfy this. -/
theorem movz_not_taken_unchanged (p : Program) (s s' : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movz rs rt rd))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rt) ≠ 0#32)
    (hstep : step p s = StepResult.next s') :
    readReg s' (regIdxSpec rd) = readReg s (regIdxSpec rd) := by
  rw [movz_not_taken_spec p s w rs rt rd hfetch hdecode hpb hnot] at hstep
  injection hstep with hs
  rw [← hs]
  rfl

/-! ### Group 5 — satisfiable examples

Same technique as Group 3: each theorem above is instantiated on a concrete
program/state with every hypothesis discharged. -/

-- `addu_spec_raw`: `0xffffffff + 2` wraps to `1`, with no trap (unlike
-- `add`, which would halt on this operand pair's signed overflow reading).
#guard (match step (prog1Spec (.addu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 2#32)]) with
        | .next s => readReg s 10 == 1#32
        | .halt _ => false) = true

-- `subu_spec_raw`: `0 - 1` wraps to `0xffffffff`, with no trap.
#guard (match step (prog1Spec (.subu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0#32), (9, 1#32)]) with
        | .next s => readReg s 10 == 0xffffffff#32
        | .halt _ => false) = true

-- `and_spec_raw`/`or_spec_raw`/`xor_spec_raw`/`nor_spec_raw`.
#guard (match step (prog1Spec (.and 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]) with
        | .next s => readReg s 10 == 0x0f000f00#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.or 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]) with
        | .next s => readReg s 10 == 0xff0fff0f#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.xor 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]) with
        | .next s => readReg s 10 == 0xf00ff00f#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.nor 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0#32), (9, 0#32)]) with
        | .next s => readReg s 10 == 0xffffffff#32
        | .halt _ => false) = true

-- `slt_spec_raw`/`sltu_spec_raw`: the same bit pattern (`0xffffffff`, i.e.
-- `-1` signed) compares differently against `1` under signed vs. unsigned
-- interpretation.
#guard (match step (prog1Spec (.slt 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => readReg s 10 == 1#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sltu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => readReg s 10 == 0#32
        | .halt _ => false) = true

-- `movn_taken_spec`/`movn_not_taken_unchanged`: `$rd` pre-seeded with the
-- sentinel `99` is overwritten when `$rt ≠ 0`, and left at `99` (not
-- zeroed) when `$rt = 0`.
#guard (match step (prog1Spec (.movn 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 1#32), (10, 99#32)]) with
        | .next s => readReg s 10 == 5#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.movn 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 0#32), (10, 99#32)]) with
        | .next s => readReg s 10 == 99#32
        | .halt _ => false) = true

-- `movz_taken_spec`/`movz_not_taken_unchanged`: the mirror image of `movn`.
#guard (match step (prog1Spec (.movz 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 0#32), (10, 99#32)]) with
        | .next s => readReg s 10 == 5#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.movz 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 1#32), (10, 99#32)]) with
        | .next s => readReg s 10 == 99#32
        | .halt _ => false) = true

/-! ## Group 5 — shift/rotate instruction family

`sll`/`srl`/`sra`/`sllv`/`srlv`/`srav`/`rotr`/`rotrv` (INSTRUCTION-REF "R-type
shifts"/"R-type variable shifts"/"R-type rotate" sections,
docs/spec/MIPS-COVERAGE-GAPS.md §3.4). All eight are straight-line
computations — no memory access, no branch scheduling, no inner `match`/`if`
on an abstract register value — so each follows `add_spec_raw`'s exact proof
recipe. -/

/-- **`sll` shifts `$rt` left by the fixed `shamt` field, zero-filling the
vacated low bits.** `shamt` comes straight from the instruction encoding
(INSTRUCTION-REF "sll"), not a register. -/
theorem sll_spec_raw (p : Program) (s : State) (w rd rt shamt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sll rd rt shamt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`srl` shifts `$rt` right by the fixed `shamt` field, zero-filling the
vacated high bits (logical shift).** Mirrors `sll_spec_raw`; see `sra_spec_raw`
for the sign-filling counterpart. -/
theorem srl_spec_raw (p : Program) (s : State) (w rd rt shamt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.srl rd rt shamt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> shamt.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sra` shifts `$rt` right by the fixed `shamt` field, sign-filling the
vacated high bits (arithmetic shift).** Uses `BitVec.sshiftRight`, the same
helper `step` itself uses, so a negative `$rt` keeps its sign after the
shift (INSTRUCTION-REF "sra"). -/
theorem sra_spec_raw (p : Program) (s : State) (w rd rt shamt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sra rd rt shamt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight shamt.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sllv` shifts `$rt` left by `$rs`'s low 5 bits**, not a fixed `shamt`
field — so a shift-amount register holding e.g. `33` (`0b100001`) behaves
identically to one holding `1` (INSTRUCTION-REF "sllv",
docs/spec/MIPS-COVERAGE-GAPS.md §3.4). `extractLsb 4 0` is the exact masking
expression `step` itself uses. -/
theorem sllv_spec_raw (p : Program) (s : State) (w rd rt rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sllv rd rt rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< amt)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< amt)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`srlv` shifts `$rt` right (zero-filling) by `$rs`'s low 5 bits.**
Mirrors `sllv_spec_raw`'s masking; logical (not arithmetic) shift, same as
`srl`. -/
theorem srlv_spec_raw (p : Program) (s : State) (w rd rt rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.srlv rd rt rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> amt)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> amt)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`srav` shifts `$rt` right (sign-filling) by `$rs`'s low 5 bits.**
Mirrors `sllv_spec_raw`'s masking and `sra_spec_raw`'s sign-fill. -/
theorem srav_spec_raw (p : Program) (s : State) (w rd rt rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.srav rd rt rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      StepResult.next
        { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight amt)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight amt)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`rotr` rotates `$rt` right by the fixed `sa` field, wrapping bits
shifted off the bottom around to the top** (MIPS32r2; INSTRUCTION-REF "rotr",
docs/spec/MIPS-COVERAGE-GAPS.md §3.4) — unlike `srl`'s zero-fill on the same
input. `BitVec.rotateRight` is the exact operation `step` itself uses. -/
theorem rotr_spec_raw (p : Program) (s : State) (w rd rt sa : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rotr rd rt sa))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight sa.toNat)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight sa.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`rotrv` rotates `$rt` right by `$rs`'s low 5 bits, wrapping around**
(MIPS32r2; INSTRUCTION-REF "rotrv"). Same masking as `sllv`/`srlv`/`srav`,
same wrap-around as `rotr`. -/
theorem rotrv_spec_raw (p : Program) (s : State) (w rd rt rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rotrv rd rt rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      StepResult.next
        { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight amt)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight amt)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- Satisfiable examples: `sll`/`srl`/`sra` at shamt 0 and 31 (sign-fill vs.
-- zero-fill at the boundary), mirroring `Step.lean`'s own `#guard`s.
#guard (match step (prog1Spec (.sll 10#32 8#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10 == 0x12345678#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sll 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => readReg s 10 == 0x80000000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.srl 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32)]) with
        | .next s => readReg s 10 == 1#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sra 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32)]) with
        | .next s => readReg s 10 == 0xffffffff#32
        | .halt _ => false) = true

-- Satisfiable examples: `sllv`/`srlv`/`srav` masking a shift amount of 33
-- down to 1 (`33 & 0x1f = 1`).
#guard (match step (prog1Spec (.sllv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 1#32), (9, 33#32)]) with
        | .next s => readReg s 10 == 2#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.srlv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 33#32)]) with
        | .next s => readReg s 10 == 0x40000000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.srav 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 33#32)]) with
        | .next s => readReg s 10 == 0xc0000000#32
        | .halt _ => false) = true

-- Satisfiable examples: `rotr`/`rotrv`, including the masked-amount case
-- (`36 & 0x1f = 4`).
#guard (match step (prog1Spec (.rotr 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10 == 0x81234567#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.rotrv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32), (9, 36#32)]) with
        | .next s => readReg s 10 == 0x81234567#32
        | .halt _ => false) = true

/-! ### Bad-output rejection: `rotr` genuinely wraps, it is not `srl` in
disguise

A buggy `rotr` implementation might secretly reuse `srl`'s zero-fill (e.g.
by forgetting to reinsert the shifted-out bits). The two theorems below pin
down the exact register `rotr` and `srl` each write for the *same* `$rt`
value and shift amount (`0x12345678` shifted/rotated by `4`), and the
following `decide` shows those two outputs are provably different values —
so the spec captures genuine wrap-around, not just "a rightward shift of
some kind happened". -/

theorem rotr_wraps_not_zero_fill (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.rotr 10#32 8#32 4#32))
    (hpb : s.pendingBranch = none)
    (hrt : readReg s (regIdxSpec 8#32) = 0x12345678#32) :
    step p s = StepResult.next
      { (writeReg s (regIdxSpec 10#32) 0x81234567#32) with
        pc := (writeReg s (regIdxSpec 10#32) 0x81234567#32).pc + 4#32 } := by
  rw [rotr_spec_raw p s w 10#32 8#32 4#32 hfetch hdecode hpb]
  dsimp only
  rw [hrt]
  rfl

theorem srl_zero_fills_same_input (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.srl 10#32 8#32 4#32))
    (hpb : s.pendingBranch = none)
    (hrt : readReg s (regIdxSpec 8#32) = 0x12345678#32) :
    step p s = StepResult.next
      { (writeReg s (regIdxSpec 10#32) 0x01234567#32) with
        pc := (writeReg s (regIdxSpec 10#32) 0x01234567#32).pc + 4#32 } := by
  rw [srl_spec_raw p s w 10#32 8#32 4#32 hfetch hdecode hpb]
  dsimp only
  rw [hrt]
  rfl

/-- **`rotr`'s wrap-around is not optional.** For the identical `$rt` value
and shift amount, `rotr` (`rotr_wraps_not_zero_fill`) and `srl`
(`srl_zero_fills_same_input`) write provably different values to `$rd` —
`0x81234567` (the low nibble wrapped to the top) versus `0x01234567` (the low
nibble discarded). The spec encodes exactly which bits move where, not merely
"some rightward shift happened". -/
theorem rotr_output_ne_srl_output : (0x81234567#32 : W32) ≠ (0x01234567#32 : W32) := by decide

-- Concrete witness tying the two facts together: running `rotr` and `srl`
-- on the same register contents and shift amount produces different
-- results in `$rd`.
#guard (match step (prog1Spec (.rotr 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10
        | .halt _ => 0#32) !=
        (match step (prog1Spec (.srl 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10
        | .halt _ => 0#32)

/-! ## Group 5 — multiply/divide and HI/LO-register family

The `mult`/`multu`/`divu`/`mflo`/`mfhi`/`mthi`/`mtlo`/`madd`/`maddu`/`msub`/
`msubu` instructions (`docs/spec/INSTRUCTION-REF.md` "Multiply / divide"
and "mthi (R)"/"mtlo (R)" sections). `div`/`div_by_zero_spec`/
`div_negative_dividend_spec` above are the house style this section
follows: every theorem is `step` restated with public names, proved by the
same `obtain`/`subst`/`unfold step`/`rw [hfetch]`/`rw [hdecode]`/`rfl`
recipe as `add_spec_raw`. -/

/-- **`mult` forms the exact signed 64-bit product of `$rs` and `$rt`,
splitting it into `hi`/`lo`.** No GPR is written, and `mult` never halts
(INSTRUCTION-REF "mult" section: MARS never traps on multiply overflow —
the full 64-bit result always fits in `hi:lo`). -/
theorem mult_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mult rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      StepResult.next
        { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`multu` forms the exact unsigned 64-bit product of `$rs` and `$rt`,
splitting it into `hi`/`lo`.** Mirrors `mult_spec_raw`, except both
operands are read as unsigned `Nat`s first (INSTRUCTION-REF "multu"
section). Never halts. -/
theorem multu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.multu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      StepResult.next
        { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `mult_spec_raw`: `5 * 7 = 35` fits entirely in `lo`, `hi = 0`.
#guard (match step (prog1Spec (.mult 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with
        | .next s => s.lo == 35#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `mult_spec_raw`: a negative times a positive operand gives a negative
-- 64-bit product, so `hi` is all-ones (sign-extension of the product).
#guard (match step (prog1Spec (.mult 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32), (9, 5#32)]) with
        | .next s => s.lo == 0xfffffff6#32 && s.hi == 0xffffffff#32
        | .halt _ => false) = true

-- `multu_spec_raw`: the same bit pattern `0xfffffffe` is unsigned, so
-- `0xfffffffe * 5` overflows into a nonzero `hi` without any sign-extension.
#guard (match step (prog1Spec (.multu 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32), (9, 5#32)]) with
        | .next s => s.lo == 0xfffffff6#32 && s.hi == 4#32
        | .halt _ => false) = true

/-- **`divu` by a nonzero divisor is ordinary unsigned division/remainder;
`divu` by zero leaves `hi`/`lo` untouched and does not halt.** Unsigned
counterpart of `div_spec_raw` (INSTRUCTION-REF "divu" section — same
by-zero-is-a-silent-no-op MARS deviation documented for `div`). Always
advances the program counter by 4. -/
theorem divu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.divu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      if b == 0 then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next { s with lo := BitVec.ofNat 32 (a / b), hi := BitVec.ofNat 32 (a % b), pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `divu_spec_raw`: dividing by `0` leaves `hi`/`lo` exactly
as they were and does not halt — the unsigned counterpart of
`div_by_zero_spec` (INSTRUCTION-REF "divu" section). -/
theorem divu_by_zero_spec (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.divu rs rt))
    (hpb : s.pendingBranch = none)
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [divu_spec_raw p s w rs rt hfetch hdecode hpb, hzero]
  rfl

-- `divu_spec_raw`: `17u / 5u = 3` remainder `2`, ordinary unsigned division.
#guard (match step (prog1Spec (.divu 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 17#32), (9, 5#32)]) with
        | .next s => s.lo == 3#32 && s.hi == 2#32
        | .halt _ => false) = true

-- `divu_by_zero_spec`: dividing by `0` leaves a pre-seeded `hi`/`lo` alone,
-- the unsigned counterpart of the `div_by_zero_spec` example above.
#guard (match step (prog1Spec (.divu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 10#32), (9, 0#32)]) with
            hi := 0x11#32, lo := 0x22#32 } with
        | .next s => s.lo == 0x22#32 && s.hi == 0x11#32
        | .halt _ => false) = true

/-- **`mflo` copies `lo` into `$rd`.** Trivial register read
(INSTRUCTION-REF "mflo" section); never halts. -/
theorem mflo_spec_raw (p : Program) (s : State) (w rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mflo rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) s.lo) with
          pc := (writeReg s (regIdxSpec rd) s.lo).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mfhi` copies `hi` into `$rd`.** Trivial register read
(INSTRUCTION-REF "mfhi" section); never halts. -/
theorem mfhi_spec_raw (p : Program) (s : State) (w rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfhi rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) s.hi) with
          pc := (writeReg s (regIdxSpec rd) s.hi).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mthi` copies `$rs` into `hi`; `lo` is left unchanged.** Write-direction
counterpart to `mfhi_spec_raw` (INSTRUCTION-REF "mthi (R)" section); no GPR
is written, never halts. -/
theorem mthi_spec_raw (p : Program) (s : State) (w rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mthi rs))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with hi := readReg s (regIdxSpec rs), pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mtlo` copies `$rs` into `lo`; `hi` is left unchanged.** Write-direction
counterpart to `mflo_spec_raw` (INSTRUCTION-REF "mtlo (R)" section); no GPR
is written, never halts. -/
theorem mtlo_spec_raw (p : Program) (s : State) (w rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mtlo rs))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with lo := readReg s (regIdxSpec rs), pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **Round-trip check: `mthi` immediately followed by `mfhi` recovers
`$rs`'s original value through `hi`.** This is the "the half-pair actually
composes" check for `mthi`/`mfhi`: it is not enough for each instruction to
close on its own — writing `hi := $rs` and then reading `$rd := hi` two
steps later must produce exactly the value `$rs` held *before* either
instruction ran. Needs `regIdxSpec rd ≠ 0` (a write to `$zero` is a no-op,
INSTRUCTION-REF Global rule 2) and `s.regs.size = 32` (`writeReg_reads_back`'s
side condition, guaranteed by `initialState` — `State.lean`). -/
theorem mthi_mfhi_round_trip (p : Program) (s : State) (w w2 rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mthi rs))
    (hpb : s.pendingBranch = none)
    (hfetch2 : fetchWord p (s.pc + 4#32) = some w2) (hdecode2 : decode w2 = some (.mfhi rd))
    (hrd : regIdxSpec rd ≠ 0) (hsize32 : s.regs.size = 32) :
    ∃ s1 s2,
      step p s = StepResult.next s1 ∧
      step p s1 = StepResult.next s2 ∧
      readReg s2 (regIdxSpec rd) = readReg s (regIdxSpec rs) := by
  have h1 := mthi_spec_raw p s w rs hfetch hdecode hpb
  have h2 := mfhi_spec_raw p { s with hi := readReg s (regIdxSpec rs), pc := s.pc + 4#32 } w2 rd
    hfetch2 hdecode2 hpb
  refine ⟨_, _, h1, h2, ?_⟩
  exact writeReg_reads_back _ (regIdxSpec rd) _ hrd hsize32

-- `mthi_spec_raw`/`mfhi_spec_raw` concrete witness, standalone: `mthi` sets
-- `hi` from `$t0`, `mfhi` reads it back into `$t1`.
#guard (match step (prog1Spec (.mthi 8#32)) (setRegsSpec (initialState textBase) [(8, 0x2a#32)]) with
        | .next s => s.hi == 0x2a#32 && s.lo == 0#32
        | .halt _ => false) = true

-- `mtlo_spec_raw` concrete witness: `mtlo` sets `lo` from `$t0`, `hi`
-- untouched.
#guard (match step (prog1Spec (.mtlo 8#32)) (setRegsSpec (initialState textBase) [(8, 0x2a#32)]) with
        | .next s => s.lo == 0x2a#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `mthi_mfhi_round_trip` concrete witness: `mthi $t0; mfhi $t1` leaves
-- `$t1` holding exactly `$t0`'s original value.
#guard (match step (buildProgSpec textBase [.mthi 8#32, .mfhi 9#32])
          (setRegsSpec (initialState textBase) [(8, 0x2a#32)]) with
        | .next s1 =>
          (match step (buildProgSpec textBase [.mthi 8#32, .mfhi 9#32]) s1 with
           | .next s2 => readReg s2 9 == 0x2a#32
           | .halt _ => false)
        | .halt _ => false) = true

/-- **`madd` adds the signed 64-bit product of `$rs`/`$rt` onto the
EXISTING `{hi,lo}` accumulator — it does not overwrite it.** The addend is
`s.hi ++ s.lo` (the 64-bit value already sitting in the accumulator
*before* this instruction runs), reassembled exactly as `Step.lean` does
and genuinely used as one operand of the `+` below, not discarded
(INSTRUCTION-REF "madd (R, SPECIAL2)" section). The 64-bit add wraps on
overflow, matching `mult`'s non-trapping precedent; never halts. -/
theorem madd_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.madd rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let sum64 := acc64 + prod64
      StepResult.next
        { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`maddu` adds the unsigned 64-bit product of `$rs`/`$rt` onto the
EXISTING `{hi,lo}` accumulator.** Unsigned counterpart of `madd_spec_raw`
(INSTRUCTION-REF "maddu (R, SPECIAL2)" section); same "accumulate, don't
overwrite" shape — `acc64` is built from `s.hi`/`s.lo` as they stood before
this instruction ran. Never halts. -/
theorem maddu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.maddu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let sum64 := acc64 + prod64
      StepResult.next
        { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`msub` subtracts the signed 64-bit product of `$rs`/`$rt` from the
EXISTING `{hi,lo}` accumulator — it does not overwrite it.** Same
accumulator-reassembly shape as `madd_spec_raw`, but `acc64 - prod64`
instead of `acc64 + prod64` (INSTRUCTION-REF "msub (R, SPECIAL2)" section).
Wraps on underflow; never halts. -/
theorem msub_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.msub rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let diff64 := acc64 - prod64
      StepResult.next
        { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`msubu` subtracts the unsigned 64-bit product of `$rs`/`$rt` from the
EXISTING `{hi,lo}` accumulator.** Unsigned counterpart of `msub_spec_raw`
(INSTRUCTION-REF "msubu (R, SPECIAL2)" section); same accumulate-not-
overwrite shape. Never halts. -/
theorem msubu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.msubu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := (readReg s (regIdxSpec rs)).toNat
      let b := (readReg s (regIdxSpec rt)).toNat
      let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
      let acc64 : BitVec 64 := s.hi ++ s.lo
      let diff64 := acc64 - prod64
      StepResult.next
        { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32, pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `madd_spec_raw`: a pre-seeded accumulator of `{hi=0,lo=100}` plus
-- `5 * 7 = 35` gives `135`, i.e. the existing `lo` value is genuinely an
-- addend, not discarded.
#guard (match step (prog1Spec (.madd 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 } with
        | .next s => s.lo == 135#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `maddu_spec_raw`: same pre-seeded accumulator, unsigned product.
#guard (match step (prog1Spec (.maddu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 } with
        | .next s => s.lo == 135#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `msub_spec_raw`: a pre-seeded accumulator of `{hi=0,lo=100}` minus
-- `5 * 7 = 35` gives `65`, i.e. the existing `lo` value is genuinely a
-- minuend, not discarded.
#guard (match step (prog1Spec (.msub 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 } with
        | .next s => s.lo == 65#32 && s.hi == 0#32
        | .halt _ => false) = true

-- `msubu_spec_raw`: same pre-seeded accumulator, unsigned product.
#guard (match step (prog1Spec (.msubu 8#32 9#32))
          { (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)]) with hi := 0#32, lo := 100#32 } with
        | .next s => s.lo == 65#32 && s.hi == 0#32
        | .halt _ => false) = true

/-! ## Group 5 — remaining memory instructions (`sw`, `lh`, `lhu`, `sh`, `ll`, `sc`)

Same `lw`/`lb`/`lbu`-style raw specs (Group 2), for the rest of the memory
instruction set. Each one restates its `step` case with public names
(`readMemHalf`/`writeMemWord`/`writeMemHalf`, …), halting with
`addressError` on a misaligned effective address exactly like `lw`/`lb` do,
and is backed by a concrete `#guard` witness in the same style as Group 3.

`lwl`/`lwr`/`swl`/`swr` (the unaligned-load/store family) are covered
separately, in the dedicated `## Group 7` section at the end of this file --
they need their own two mirrored helpers (`setByteSlotSpec`/`getByteSlotSpec`)
before their `step` cases can be restated, so they do not fit this group's
plain `readMemHalf`/`writeMemWord`/`writeMemHalf` vocabulary. -/

/-- **`sw` stores `$rt` as a big-endian word at `$rs + sext16(offset)` and
clears `llBit`** (any store invalidates a pending `ll`/`sc` pair, so a
subsequent `sc` correctly fails if memory changed underneath it), or halts
with `addressError` on a misaligned effective address (INSTRUCTION-REF "sw"
section). -/
theorem sw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => StepResult.halt (.addressError addr)
      | some s' =>
        StepResult.next
          { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lh` sign-extends the loaded halfword; `lhu` zero-extends it** —
same effective address, same halfword, different widening
(INSTRUCTION-REF "lh"/"lhu" sections), halting with `addressError` when the
address is not halfword-aligned. Packaged as one theorem, mirroring
`lb_lbu_spec_raw`. -/
theorem lh_lhu_spec_raw (p : Program) (s : State) (wh whu rs rt imm : W32)
    (hfetchH : fetchWord p s.pc = some wh) (hdecodeH : decode wh = some (.lh rs rt imm))
    (hfetchHU : fetchWord p s.pc = some whu) (hdecodeHU : decode whu = some (.lhu rs rt imm))
    (hpb : s.pendingBranch = none) :
    (step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemHalf s addr with
      | none => StepResult.halt (.addressError addr)
      | some h =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) (signExt16 h)) with
            pc := (writeReg s (regIdxSpec rt) (signExt16 h)).pc + 4#32 })
    ∧
    (step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemHalf s addr with
      | none => StepResult.halt (.addressError addr)
      | some h =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) h) with
            pc := (writeReg s (regIdxSpec rt) h).pc + 4#32 }) := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  constructor
  · unfold step
    rw [hfetchH]
    dsimp only
    rw [hdecodeH]
    dsimp only
    rfl
  · unfold step
    rw [hfetchHU]
    dsimp only
    rw [hdecodeHU]
    dsimp only
    rfl

/-- **`sh` stores the low 16 bits of `$rt` as a big-endian halfword at
`$rs + sext16(offset)` and clears `llBit`**, or halts with `addressError`
on a halfword-misaligned effective address (INSTRUCTION-REF "sh" section).
-/
theorem sh_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sh rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemHalf s addr (readReg s (regIdxSpec rt)) with
      | none => StepResult.halt (.addressError addr)
      | some s' =>
        StepResult.next
          { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`ll` loads a word exactly like `lw`, and additionally sets
`llBit`** — the link flag that a later `sc` to the same address checks
(INSTRUCTION-REF "ll" section). Halts with `addressError` on a
word-misaligned effective address, exactly like `lw`. -/
theorem ll_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ll rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => StepResult.halt (.addressError addr)
      | some v =>
        StepResult.next
          { ({ (writeReg s (regIdxSpec rt) v) with llBit := true }) with
            pc := ({ (writeReg s (regIdxSpec rt) v) with llBit := true }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sc` is conditional on `llBit`, checked before it is cleared.** The
effective address is computed and alignment-checked unconditionally, just
like `sw` (so a misaligned `sc` halts with `addressError` regardless of
`llBit`). Once the address is valid: if `s.llBit` was `true`, the store
commits (`$rt`'s old value is written to memory) and `$rt` is overwritten
with `1` (success); if `s.llBit` was `false`, the store does **not**
commit and `$rt` is overwritten with `0` (failure). Either way `llBit`
ends up `false`. This single theorem states both outcomes together
(mirroring how `beq_spec_raw` states taken/not-taken as one `if`), because
the whole point of `ll`/`sc` is this exact atomic-primitive contract, not
just "some memory operation happened" (INSTRUCTION-REF "sc" section). -/
theorem sc_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sc rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readReg s (regIdxSpec rt)) with
      | none => StepResult.halt (.addressError addr)
      | some stored =>
        if s.llBit then
          StepResult.next
            { ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }) with
              pc := ({ (writeReg stored (regIdxSpec rt) 1#32) with llBit := false }).pc + 4#32 }
        else
          StepResult.next
            { ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }) with
              pc := ({ (writeReg s (regIdxSpec rt) 0#32) with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `sw_spec_raw`: a stored word reads back exactly, and clears a
-- previously-set `llBit`.
#guard (match step (prog1Spec (.sw 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x12345678#32)]) with
            llBit := true } with
        | .next s => readMemWord s 0x10010000#32 == some 0x12345678#32 && s.llBit == false
        | .halt _ => false) = true

-- `sw_spec_raw`: a misaligned `sw` halts with `addressError`, it never
-- rounds the address and stores anyway.
#guard (match step (prog1Spec (.sw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next _ => false
        | .halt r => r == .addressError 0x10010001#32) = true

-- `lh_lhu_spec_raw`: the same high-bit halfword sign-extends under `lh`
-- and zero-extends under `lhu`.
#guard (match (writeMemHalf (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x8001#32).bind
          (fun s => some (step (prog1Spec (.lh 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0xffff8001#32
        | _ => false) = true
#guard (match (writeMemHalf (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x8001#32).bind
          (fun s => some (step (prog1Spec (.lhu 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x00008001#32
        | _ => false) = true

-- `sh_spec_raw`: only the low 16 bits of `$rt` are stored, and `llBit` is
-- cleared.
#guard (match step (prog1Spec (.sh 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0xffff1234#32)]) with
            llBit := true } with
        | .next s => readMemHalf s 0x10010000#32 == some 0x00001234#32 && s.llBit == false
        | .halt _ => false) = true

-- `ll_spec_raw`: loads like `lw` and sets `llBit`.
#guard (match (writeMemWord (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
          0x10010000#32 0x2a#32).bind
          (fun s => some (step (prog1Spec (.ll 8#32 9#32 0#32)) s)) with
        | some (.next s) => readReg s 9 == 0x2a#32 && s.llBit == true
        | _ => false) = true

-- `sc_spec_raw`, success case: `llBit` set means the store commits and
-- `$rt` becomes `1`.
#guard (match step (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x99#32)]) with
            llBit := true } with
        | .next s =>
          readReg s 9 == 1#32 && s.llBit == false && readMemWord s 0x10010000#32 == some 0x99#32
        | .halt _ => false) = true

-- `sc_spec_raw`, failure case: `llBit` clear means the store does NOT
-- commit (memory stays `0`) and `$rt` becomes `0`.
#guard (match step (prog1Spec (.sc 8#32 9#32 0#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32), (9, 0x99#32)]) with
            llBit := false } with
        | .next s =>
          readReg s 9 == 0#32 && s.llBit == false && readMemWord s 0x10010000#32 == some 0#32
        | .halt _ => false) = true

-- `sc_spec_raw`: a misaligned `sc` halts with `addressError` regardless of
-- `llBit` (the alignment check is unconditional).
#guard (match step (prog1Spec (.sc 8#32 9#32 1#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with llBit := true } with
        | .next _ => false
        | .halt r => r == .addressError 0x10010001#32) = true

/-! ## Group 5 — remaining branch/jump instructions: `blez`/`bgtz`, `j`,
`jr`/`jalr`, and the REGIMM zero-comparison family `bltz`/`bgez`/`bltzal`/
`bgezal`

Same recipe as `beq_spec_raw`/`bne_spec_raw`/`jal_spec_raw` above: each
`_spec_raw` theorem restates one `step` case as a single equation (an
`if ... then ... else ...` for the conditional branches, a plain
`StepResult.next` for the unconditional jumps), proved by destructuring `s`,
`unfold step`, rewriting in the concrete `hfetch`/`hdecode` hypotheses, and
closing with `rfl`. Taken/not-taken corollaries then follow from the raw
spec by `if_pos`/`if_neg` in one line each, exactly like
`beq_taken_spec`/`beq_not_taken_spec`. -/

/-- **`blez` branch target and condition** — single-register comparison
against zero, otherwise identical delay-slot shape to `beq`/`bne`: if
`$rs ≤ 0` (signed, zero included), schedules `PC = PC_next + (offset << 2)`
via `pendingBranch` and itself falls through to `PC_next`; otherwise it is
an ordinary fallthrough with no scheduled transfer (INSTRUCTION-REF "blez"
section). -/
theorem blez_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≤ 0 then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`blez`, taken**: when `$rs ≤ 0`, schedules `PC_next + (offset << 2)`
as the delay-slot transfer and falls through to `PC_next` first — same
one-delay-slot discipline as `beq` (INSTRUCTION-REF "blez" section). -/
theorem blez_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) ≤ 0) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [blez_spec_raw p s w rs imm hfetch hdecode hpb, if_pos htaken]

/-- **`blez`, not taken**: when `$rs > 0`, falls through to `PC_next` with
no scheduled transfer. -/
theorem blez_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 < asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [blez_spec_raw p s w rs imm hfetch hdecode hpb, if_neg (by omega)]

/-- **`bgtz` branch target and condition** — the mirror image of `blez`:
if `$rs > 0` (signed, strictly positive), schedules
`PC = PC_next + (offset << 2)`, same one-delay-slot discipline
(INSTRUCTION-REF "bgtz" section). -/
theorem bgtz_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if 0 < asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgtz`, taken**: when `$rs > 0`, schedules `PC_next + (offset << 2)`
as the delay-slot transfer. -/
theorem bgtz_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 < asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgtz_spec_raw p s w rs imm hfetch hdecode hpb, if_pos htaken]

/-- **`bgtz`, not taken**: when `$rs ≤ 0`, falls through to `PC_next` with
no scheduled transfer. -/
theorem bgtz_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) ≤ 0) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [bgtz_spec_raw p s w rs imm hfetch hdecode hpb, if_neg (by omega)]

/-- **`j` unconditionally schedules a jump whose top 4 bits come from
`PC_next`, not from `j`'s own address** — the same pseudo-direct target
composition as `jal`, minus the link-register write (INSTRUCTION-REF "j"
section). Like every other jump/branch here, `j` itself falls through to
`PC_next` and never jumps in the same step; the delay-slot instruction
always executes first. -/
theorem j_spec_raw (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.j target))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`jr` schedules a jump to the raw 32-bit value held in `$rs`** — not a
26-bit composed target like `j`, the full register value (INSTRUCTION-REF
"jr" section). A misaligned target is not special-cased here: it surfaces
as an ordinary `addressError` the next time `step` tries to fetch from it.
Same one-delay-slot discipline as every other jump/branch: `jr` itself
falls through to `PC_next`. -/
theorem jr_spec_raw (p : Program) (s : State) (w rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jr rs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { s with pc := s.pc + 4#32, pendingBranch := some (readReg s (regIdxSpec rs)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`jalr` links `$rd` to `pc + 8` (the same `jal`/`jalr` link-value
convention — past the delay slot) and schedules a jump to the raw value
held in `$rs`, read *before* `$rd` is overwritten** — so `rd == rs`
aliasing is always safe (INSTRUCTION-REF "jalr" section). This is `step`'s
own code restated: the target expression reads `$rs` from the original `s`,
not from the just-written state, exactly matching the "If `rd == rs`..."
paragraph in the spec. -/
theorem jalr_spec_raw (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { (writeReg s (regIdxSpec rd) (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some (readReg s (regIdxSpec rs)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `jalr_spec_raw`: `$rd` reads back exactly `pc + 8` — past
the delay slot, the same link-value convention as `jal`'s `$ra`. Requires
`$rd` to not itself be `$zero` (a write to `$zero` is always a no-op, see
`writeReg_preserves_zero_slot`). -/
theorem jalr_sets_rd (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32)
    (hrdnz : regIdxSpec rd ≠ (0 : Fin 32)) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec rd) = s.pc + 8#32 := by
  refine ⟨_, jalr_spec_raw p s w rs rd hfetch hdecode hpb, ?_⟩
  show readReg (writeReg s (regIdxSpec rd) ((s.pc + 4#32) + 4#32)) (regIdxSpec rd) = s.pc + 8#32
  rw [writeReg_reads_back s (regIdxSpec rd) ((s.pc + 4#32) + 4#32) hrdnz hsize32, BitVec.add_assoc]
  congr 1

/-- **`jalr $rs, $rs` (`rd == rs`) jumps to the *original* `$rs` value, not
the just-written link value** — the one subtlety specific to `jalr`
(INSTRUCTION-REF "jalr" section, "If `rd == rs`..." paragraph). Both halves
are named explicitly: the scheduled jump target is the pre-write `$rs`
value (`s`, not the post-write state), and the register itself afterward
holds the link value `pc + 8` — in general a different value, so aliasing
`rd`/`rs` (the common real-MIPS32 `jalr $t9` idiom with an implicit
`rd = $ra`, or an explicit `jalr $t9, $t9`) never loses the jump target. -/
theorem jalr_rd_eq_rs_targets_original_value (p : Program) (s : State) (w rs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jalr rs rs))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32)
    (hrsnz : regIdxSpec rs ≠ (0 : Fin 32)) :
    ∃ s', step p s = StepResult.next s' ∧
      s'.pendingBranch = some (readReg s (regIdxSpec rs)) ∧
      readReg s' (regIdxSpec rs) = s.pc + 8#32 := by
  refine ⟨_, jalr_spec_raw p s w rs rs hfetch hdecode hpb, rfl, ?_⟩
  show readReg (writeReg s (regIdxSpec rs) ((s.pc + 4#32) + 4#32)) (regIdxSpec rs) = s.pc + 8#32
  rw [writeReg_reads_back s (regIdxSpec rs) ((s.pc + 4#32) + 4#32) hrsnz hsize32, BitVec.add_assoc]
  congr 1

/-- **`bltz` branch target and condition** (REGIMM, opcode `0x01`,
`rt = 0x00`): if `$rs < 0` (signed), schedules
`PC = PC_next + (offset << 2)`, same one-delay-slot discipline as
`blez`/`bgtz` (INSTRUCTION-REF "bltz" section). -/
theorem bltz_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bltz`, taken**: when `$rs < 0`, schedules `PC_next + (offset << 2)`. -/
theorem bltz_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bltz_spec_raw p s w rs imm hfetch hdecode hpb, if_pos htaken]

/-- **`bltz`, not taken**: when `$rs ≥ 0`, falls through to `PC_next`. -/
theorem bltz_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [bltz_spec_raw p s w rs imm hfetch hdecode hpb, if_neg (by omega)]

/-- **`bgez` branch target and condition** (REGIMM, `rt = 0x01`) — the
mirror image of `bltz`: if `$rs ≥ 0` (signed, zero included), schedules
`PC = PC_next + (offset << 2)` (INSTRUCTION-REF "bgez" section). -/
theorem bgez_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgez`, taken**: when `$rs ≥ 0`, schedules `PC_next + (offset << 2)`. -/
theorem bgez_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgez_spec_raw p s w rs imm hfetch hdecode hpb, if_pos htaken]

/-- **`bgez`, not taken**: when `$rs < 0`, falls through to `PC_next`. -/
theorem bgez_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [bgez_spec_raw p s w rs imm hfetch hdecode hpb, if_neg (by omega)]

/-- **`bltzal` links `$ra` to `pc + 8` unconditionally, then — independent
of the link — branches on `$rs < 0` exactly like `bltz`.** This two-part
structure (unconditional link, conditional branch) is the real MIPS32
architectural definition, not a simplification: every execution of
`bltzal` writes `$ra`, whether or not the branch itself is taken
(INSTRUCTION-REF "bltzal" section — `GPR[31] <- PC + 8` happens in the
instruction's own cycle regardless of the branch condition tested one cycle
later). The branch condition reads `$rs` from the state *before* the link
write, matching this simulator's documented resolution of the `rs = $ra`
UNPREDICTABLE case. -/
theorem bltzal_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s' with pc := pcNext } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bltzal`, taken**: `$ra` links to `pc + 8` (as always) and the branch
also schedules `PC_next + (offset << 2)`. -/
theorem bltzal_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s = StepResult.next
      { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bltzal_spec_raw p s w rs imm hfetch hdecode hpb, if_pos htaken]

/-- **`bltzal`, not taken**: `$ra` still links to `pc + 8` (the link is
unconditional), but no transfer is scheduled — control simply falls
through to `PC_next`. -/
theorem bltzal_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next
      { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with pc := s.pc + 4#32 } := by
  rw [bltzal_spec_raw p s w rs imm hfetch hdecode hpb, if_neg (by omega)]

/-- Corollary of `bltzal_taken_spec`/`bltzal_not_taken_spec`: `$ra` reads
back exactly `pc + 8` regardless of whether the branch is taken — the
unconditional-link half of `bltzal` stated on its own. -/
theorem bltzal_sets_ra (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  have hreads : readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32 := by
    rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32, BitVec.add_assoc]
    congr 1
  by_cases htaken : asSigned (readReg s (regIdxSpec rs)) < 0
  · exact ⟨_, bltzal_taken_spec p s w rs imm hfetch hdecode hpb htaken, hreads⟩
  · exact ⟨_, bltzal_not_taken_spec p s w rs imm hfetch hdecode hpb (by omega), hreads⟩

/-- **`bgezal` links `$ra` to `pc + 8` unconditionally, then branches on
`$rs ≥ 0` exactly like `bgez`** — same unconditional-link/conditional-
branch structure as `bltzal` (INSTRUCTION-REF "bgezal" section). -/
theorem bgezal_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s' with pc := pcNext } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgezal`, taken**: `$ra` links to `pc + 8` (as always) and the branch
also schedules `PC_next + (offset << 2)`. -/
theorem bgezal_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step p s = StepResult.next
      { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgezal_spec_raw p s w rs imm hfetch hdecode hpb, if_pos htaken]

/-- **`bgezal`, not taken**: `$ra` still links to `pc + 8` (the link is
unconditional), but no transfer is scheduled. -/
theorem bgezal_not_taken_spec (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s = StepResult.next
      { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with pc := s.pc + 4#32 } := by
  rw [bgezal_spec_raw p s w rs imm hfetch hdecode hpb, if_neg (by omega)]

/-- Corollary of `bgezal_taken_spec`/`bgezal_not_taken_spec`: `$ra` reads
back exactly `pc + 8` regardless of whether the branch is taken. -/
theorem bgezal_sets_ra (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  have hreads : readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32 := by
    rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32, BitVec.add_assoc]
    congr 1
  by_cases htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))
  · exact ⟨_, bgezal_taken_spec p s w rs imm hfetch hdecode hpb htaken, hreads⟩
  · exact ⟨_, bgezal_not_taken_spec p s w rs imm hfetch hdecode hpb (by omega), hreads⟩

/-! ### Satisfiable examples for Group 5

Same discipline as Group 3: every theorem above is instantiated on a
concrete program/state with every hypothesis discharged, via `#guard`
(compiled evaluation, since `Program`/`State.mem` are `cbv_opaque`
`Std.HashMap`s that `decide`/`rfl` get stuck on). -/

-- `blez_taken_spec`/`blez_not_taken_spec`: `-5 ≤ 0` schedules the target;
-- `5 ≤ 0` is false and falls through.
#guard (match step (prog1Spec (.blez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.blez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `bgtz_taken_spec`/`bgtz_not_taken_spec`: the mirror image of `blez`.
#guard (match step (prog1Spec (.bgtz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgtz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `j_spec_raw`: an unconditional jump schedules the composed target and
-- falls through to the delay slot first, same target-composition formula
-- as `jal`'s own example above.
#guard (match step (prog1Spec (.j 0x1000#32)) (initialState textBase) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some 0x4000#32
        | .halt _ => false) = true

-- `jr_spec_raw`: schedules the raw register value, not a composed target.
#guard (match step (prog1Spec (.jr 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x80020000#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some 0x80020000#32
        | .halt _ => false) = true

-- `jalr_sets_rd`: `$t1` ends up exactly `pc + 8`, and the jump target is
-- the raw value read out of `$t0`.
#guard (match step (prog1Spec (.jalr 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80020000#32)]) with
        | .next s =>
          readReg s 9 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some 0x80020000#32
        | .halt _ => false) = true

-- `jalr_rd_eq_rs_targets_original_value`: `jalr $t1, $t1` still schedules
-- the *original* `$t1` value as the jump target, even though `$t1` itself
-- is overwritten with the link value `pc + 8` in the same step.
#guard (match step (prog1Spec (.jalr 9#32 9#32))
          (setRegsSpec (initialState textBase) [(9, 0x80020000#32)]) with
        | .next s =>
          s.pendingBranch == some 0x80020000#32 && readReg s 9 == textBase + 8#32 &&
            s.pendingBranch ≠ some (readReg s 9)
        | .halt _ => false) = true

-- `bltz_taken_spec`/`bltz_not_taken_spec`: `-5 < 0` taken, `5 < 0` false.
#guard (match step (prog1Spec (.bltz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bltz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `bgez_taken_spec`/`bgez_not_taken_spec`: the mirror image of `bltz`.
#guard (match step (prog1Spec (.bgez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `bltzal_sets_ra`/`bltzal_taken_spec`: `$ra` links unconditionally even
-- though the branch itself is taken here.
#guard (match step (prog1Spec (.bltzal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true

-- `bltzal_not_taken_spec`: `$ra` *still* links even though `5 < 0` is
-- false and no transfer is scheduled — the unconditional-link half fires
-- regardless of the branch outcome.
#guard (match step (prog1Spec (.bltzal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 && s.pendingBranch == none
        | .halt _ => false) = true

-- `bgezal_sets_ra`/`bgezal_not_taken_spec`: same unconditional-link
-- convention as `bltzal`, mirrored branch condition.
#guard (match step (prog1Spec (.bgezal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 && s.pendingBranch == none
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false) = true

/-! ## Group 5 — I-type immediate instructions (`addiu`, `slti`, `sltiu`,
`andi`, `ori`, `xori`, `lui`)

All seven are the remaining non-`addi` I-type arith/logic instructions
(`docs/spec/INSTRUCTION-REF.md` "I-type immediate arithmetic / logic"
section, right after `addi`). Every one of them is a straight-line
`execInstr` case (no inner `match`/`if` on an abstract register value, no
memory access, no branch scheduling), so each theorem below follows
`addi_spec_raw`'s exact tactic recipe verbatim. -/

/-- **`addiu` computes `$rs + sext16(imm)` with plain 32-bit wraparound and
never traps** — unlike `addi`, there is no overflow check at all (same
sign-extended immediate, but the "u" suffix removes the overflow test
entirely; INSTRUCTION-REF "addiu" section, confirmed against `Step.lean`'s
`.addiu` case, which has no `addOverflows`/halt branch whatsoever). -/
theorem addiu_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addiu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) + signExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) + signExt16 imm)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`slti` writes `1` iff `$rs < sext16(imm)` under a signed comparison,
else `0`** (INSTRUCTION-REF "slti" section). -/
theorem slti_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.slti rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := if asSigned (readReg s (regIdxSpec rs)) < asSigned (signExt16 imm)
               then 1#32 else 0#32
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sltiu` sign-extends the 16-bit immediate first, exactly like `slti`,
then compares the resulting 32-bit values as unsigned** — the "u" affects
only the comparison, not the immediate's extension (INSTRUCTION-REF
"sltiu" section, same convention as this project's `sltu`; confirmed
against `Step.lean`'s `.sltiu` case, which calls `signExt16 imm` and then
compares `.toNat` values). -/
theorem sltiu_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sltiu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := if (readReg s (regIdxSpec rs)).toNat < (signExt16 imm).toNat
               then 1#32 else 0#32
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`andi` zero-extends the 16-bit immediate, then bitwise-ANDs it with
`$rs`** — unlike `addi`/`slti`, the immediate is zero-extended, not
sign-extended (INSTRUCTION-REF "andi" section: "immediate is
zero-extended... not sign-extended"). -/
theorem andi_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.andi rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) &&& zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) &&& zeroExt16 imm)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`ori` zero-extends the 16-bit immediate, then bitwise-ORs it with
`$rs`** (INSTRUCTION-REF "ori" section — same zero-extension convention as
`andi`). -/
theorem ori_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ori rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ||| zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ||| zeroExt16 imm)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`xori` zero-extends the 16-bit immediate, then bitwise-XORs it with
`$rs`** (INSTRUCTION-REF "xori" section — same zero-extension convention as
`andi`). -/
theorem xori_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.xori rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ^^^ zeroExt16 imm)) with
          pc := (writeReg s (regIdxSpec rt) (readReg s (regIdxSpec rs) ^^^ zeroExt16 imm)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lui` writes `imm << 16` into `$rt`, ignoring `$rs` entirely** — `$rs`
is a fixed/unused field in the real encoding, and `Instruction.lui` itself
has no `rs` operand at all (INSTRUCTION-REF "lui" section: "$rt = imm <<
16", no sign extension needed since the low 16 bits are always discarded by
the shift). -/
theorem lui_spec_raw (p : Program) (s : State) (w rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lui rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (zeroExt16 imm <<< 16)) with
          pc := (writeReg s (regIdxSpec rt) (zeroExt16 imm <<< 16)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `addiu_spec_raw`: `0x7fffffff + 1` wraps to `0x80000000` instead of
-- trapping (the one observable difference from `addi`).
#guard (match step (prog1Spec (.addiu 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x7fffffff#32)]) with
        | .next s => readReg s 9 == 0x80000000#32
        | .halt _ => false) = true

-- `slti_spec_raw`/`sltiu_spec_raw`: the same bit pattern (`-1` signed,
-- `0xffffffff` unsigned) compares differently against `0` depending on
-- signedness.
#guard (match step (prog1Spec (.slti 8#32 9#32 0x0000#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => readReg s 9 == 1#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sltiu 8#32 9#32 0x0000#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => readReg s 9 == 0#32
        | .halt _ => false) = true

-- `andi_spec_raw`/`ori_spec_raw`/`xori_spec_raw`: the immediate is
-- zero-extended, not sign-extended — the high 16 bits of `$rs` are never
-- pulled from the immediate's sign.
#guard (match step (prog1Spec (.andi 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => readReg s 9 == 0x00008001#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ori 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => readReg s 9 == 0x00008001#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.xori 8#32 9#32 0x8001#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => readReg s 9 == 0x00008001#32
        | .halt _ => false) = true

-- `lui_spec_raw`: the immediate lands in the high half-word, low half-word
-- stays zero, and `$rs` (here nonzero garbage) is ignored since `lui` has
-- no `rs` operand at all.
#guard (match step (prog1Spec (.lui 9#32 0x8001#32)) (initialState textBase) with
        | .next s => readReg s 9 == 0x80010000#32
        | .halt _ => false) = true

/-! ## Group 6 — register-register trap family (`teq`, `tne`, `tlt`, `tge`,
`tltu`, `tgeu`, `break`)

Ground truth: `docs/spec/INSTRUCTION-REF.md` "Coprocessor 0 / traps and
exceptions" section (the shared exception mechanism) and its "teq / tne /
tlt / tge / tltu / tgeu" / "break" subsections. These seven do **not** go
through `Step.lean`'s `mkNext`/`advance` path at all when the trap fires;
they go through the separate (private) `takeException` helper, which this
file cannot name directly, so each theorem below inlines `takeException`'s
body using the public names `excCodeTr`/`excCodeBp`/`statusExlMask`/
`exceptionVectorAddr` (all public `def`s in `Types.lean`) — a genuinely
different right-hand-side shape from every Group 2/5 theorem above
(`cp0Epc`/`cp0Cause`/`cp0Status`/`pc` all change together, no `writeReg`
involved at all). Every theorem below needs `hpb : s.pendingBranch = none`,
even `break` (whose own semantics never consult `pendingBranch` at all):
`Step.lean`'s `execInstr` opens with an unconditional `if
s.pendingBranch.isSome && isBranchLike instr then halt else ...` check
*before* dispatching to any instruction's own case, so `rfl` cannot reduce
past that `if` without `s.pendingBranch` pinned to a concrete value, no
matter which instruction follows. The six comparison-based theorems need
`hpb` a second time, for their *non-trapping* branch, which still falls
through via the ordinary `mkNext`/`advance` path (so its exact shape —
plain `pc + 4#32`, no `pendingBranch` left dangling — depends on `s` not
already being mid-delay-slot, exactly as for `beq_spec_raw`). -/

/-- **`break` unconditionally takes a coprocessor-0 exception**: no
condition to evaluate, `EPC` records `break`'s own address, `Cause.ExcCode`
is set to `excCodeBp`, `Status.EXL` is OR'd in, and `pc` jumps straight to
the general exception vector (INSTRUCTION-REF "break" section: "evaluate
no condition; unconditionally takes the exception... with excCode =
excCodeBp"). -/
theorem break_spec_raw (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .break)
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { s with
            cp0Epc := s.pc
            cp0Cause := excCodeBp <<< 2
            cp0Status := s.cp0Status ||| statusExlMask
            pc := exceptionVectorAddr } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `break_spec_raw`: a concrete `break` lands exactly on the exception
-- vector with the `Bp` exception code packed into `Cause`.
#guard (match step (prog1Spec .break) (initialState textBase) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeBp <<< 2) &&
            s.cp0Status == statusExlMask && s.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-- **`teq` traps iff `$rs == $rt`**, taking the shared coprocessor-0
exception with `excCode = excCodeTr`; otherwise it is a complete no-op
beyond the ordinary fallthrough to `pc + 4#32` — no CP0 state touched at
all (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem teq_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.teq rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tne` traps iff `$rs ≠ $rt`** — the mirror image of `teq`
(INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem tne_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tne rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt) then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tlt` traps iff `$rs <s $rt`**, a *signed* comparison
(INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section: "`tlt`:
`$rs <s $rt` (signed)"). -/
theorem tlt_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tlt rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < asSigned (readReg s (regIdxSpec rt)) then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tge` traps iff `$rs ≥s $rt`**, a *signed* comparison — the mirror
image of `tlt` (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu"
section). -/
theorem tge_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tge rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≥ asSigned (readReg s (regIdxSpec rt)) then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tltu` traps iff `$rs <u $rt`**, an *unsigned* comparison on the raw
bit patterns (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu"
section: "`tltu`: `$rs <u $rt` (unsigned)"). -/
theorem tltu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tltu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat < (readReg s (regIdxSpec rt)).toNat then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tgeu` traps iff `$rs ≥u $rt`**, an *unsigned* comparison — the
mirror image of `tltu` (INSTRUCTION-REF "teq / tne / tlt / tge / tltu /
tgeu" section). -/
theorem tgeu_spec_raw (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgeu rs rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat ≥ (readReg s (regIdxSpec rt)).toNat then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `teq_spec_raw`/`tne_spec_raw`: equal registers trap under `teq` (and are
-- a no-op under `tne`); unequal registers are the mirror image. One
-- `#guard` per instruction per branch, matching the house style used for
-- `beq`/`bne` above.
#guard (match step (prog1Spec (.teq 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == statusExlMask && s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.teq 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == 0#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tne 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == statusExlMask && s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tne 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == 0#32
        | .halt _ => false) = true

-- `tlt_spec_raw`/`tge_spec_raw`: `-1` (as `0xffffffff`) is signed-less-than
-- `1`, so `tlt` traps and `tge` does not; swapping the operands flips both.
#guard (match step (prog1Spec (.tlt 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tge 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `tltu_spec_raw`/`tgeu_spec_raw`: the same bit pattern `0xffffffff` is the
-- *largest* unsigned value, so it is never `<u 1` but always `≥u 1`.
#guard (match step (prog1Spec (.tltu 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tgeu 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-! ## Group 7 — Coprocessor 1 (FPU) raw bit-pattern moves and Coprocessor 0
(CP0) register moves/`eret`/`wait`

This group covers exactly the FPU/CP0 subfamilies that need no `Float32`
arithmetic reasoning at all: `mfc1`/`mtc1`/`lwc1`/`swc1` (raw GPR\<->FPR and
memory\<->FPR moves, same shape as `lw`/`sw` targeting `fpRegs` instead of
`regs`), `abs.s`/`neg.s` (pure bitmask operations on the raw `W32` pattern),
and `mfc0`/`mtc0`/`eret`/`wait` (the three modeled CP0 registers plus
exception return and the documented `wait` no-op). Real `Float32`
arithmetic (`add.s` etc.) is intentionally out of scope for this group; see
the stretch-goal note near the end of this section for the one arithmetic
instruction attempted beyond it.

`writeFpReg_reads_back` below is the `fpRegs` counterpart of
`writeReg_reads_back` above: unlike `writeReg`, `writeFpReg` has no
hardwired-zero register to special-case, so it needs only the array-size
hypothesis. -/

/-- Writing `v` to FP register `i` and immediately reading `i` back gives
exactly `v` (`writeFpReg` has no hardwired-zero slot, unlike `writeReg`). -/
theorem writeFpReg_reads_back (s : State) (i : Fin 32) (v : W32)
    (hsize : s.fpRegs.size = 32) : readFpReg (writeFpReg s i v) i = v := by
  unfold writeFpReg readFpReg
  simp [Array.set!, Array.getD_eq_getD_getElem?, hsize, i.isLt]

/-- **`mfc1` copies `$fs`'s raw 32-bit bit pattern into GPR `$rt`, with no
numeric conversion** (INSTRUCTION-REF floating-point section; `fpRegs`
stores raw bit patterns, `Types.lean`). -/
theorem mfc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readFpReg s (regIdxSpec fs))) with
          pc := (writeReg s (regIdxSpec rt) (readFpReg s (regIdxSpec fs))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mtc1` copies GPR `$rt`'s raw 32-bit bit pattern into `$fs`, with no
numeric conversion** — the inverse move of `mfc1_spec_raw`
(INSTRUCTION-REF floating-point section). -/
theorem mtc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mtc1 rt fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fs) (readReg s (regIdxSpec rt))) with
          pc := (writeFpReg s (regIdxSpec fs) (readReg s (regIdxSpec rt))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lwc1` loads a word from `$rs + sext16(offset)` into FPR `$ft`** —
identical addressing/alignment rules to `lw` (`lw_spec_raw`), but the
destination is `fpRegs` via `writeFpReg` instead of `regs` via `writeReg`
(INSTRUCTION-REF "lwc1" section). -/
theorem lwc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => StepResult.halt (.addressError addr)
      | some v =>
        StepResult.next
          { (writeFpReg s (regIdxSpec ft) v) with
            pc := (writeFpReg s (regIdxSpec ft) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `lwc1_spec_raw`: a misaligned effective address halts with
`addressError`, naming that exact address — same shape as `lw_misaligned_spec`. -/
theorem lwc1_misaligned_spec (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step p s = StepResult.halt (.addressError (readReg s (regIdxSpec rs) + signExt16 imm)) := by
  rw [lwc1_spec_raw p s w rs ft imm hfetch hdecode hpb]
  dsimp only
  rw [show readMemWord s (readReg s (regIdxSpec rs) + signExt16 imm) = none by
    unfold readMemWord
    rw [if_pos hmisaligned]]

/-- **`swc1` stores FPR `$ft`'s raw bit pattern to `$rs + sext16(offset)`
and clears `llBit`** — identical addressing/alignment rules and `llBit`
side effect as `sw` (`sw_spec_raw`), but the source is `fpRegs` via
`readFpReg` instead of `regs` via `readReg` (INSTRUCTION-REF "swc1"
section). -/
theorem swc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swc1 rs ft imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match writeMemWord s addr (readFpReg s (regIdxSpec ft)) with
      | none => StepResult.halt (.addressError addr)
      | some s' =>
        StepResult.next
          { ({ s' with llBit := false }) with
            pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `swc1_spec_raw`: a misaligned effective address halts with
`addressError`, naming that exact address — same shape as `lwc1_misaligned_spec`. -/
theorem swc1_misaligned_spec (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swc1 rs ft imm))
    (hpb : s.pendingBranch = none)
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step p s = StepResult.halt (.addressError (readReg s (regIdxSpec rs) + signExt16 imm)) := by
  rw [swc1_spec_raw p s w rs ft imm hfetch hdecode hpb]
  dsimp only
  rw [show writeMemWord s (readReg s (regIdxSpec rs) + signExt16 imm) (readFpReg s (regIdxSpec ft)) = none by
    unfold writeMemWord
    rw [if_pos hmisaligned]]

/-- **`abs.s` clears `$fs`'s sign bit into `$fd`** — a pure `W32` bitmask
(`&&& 0x7fffffff`), not a `Float32` operation (`Instruction.absS`'s
docstring) — so this is exact for every bit pattern, including NaN
payloads, not just for values that happen to decode as finite floats. -/
theorem absS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.absS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs) &&& 0x7fffffff#32)) with
          pc := (writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs) &&& 0x7fffffff#32)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`neg.s` flips `$fs`'s sign bit into `$fd`** — a pure `W32` bitmask
(`^^^ 0x80000000`), not a `Float32` operation (`Instruction.negS`'s
docstring), exact for every bit pattern for the same reason as
`absS_spec_raw`. -/
theorem negS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.negS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs) ^^^ 0x80000000#32)) with
          pc := (writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs) ^^^ 0x80000000#32)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `mfc1`/`mtc1` round-trip an arbitrary bit pattern through `$f3`, and
-- `lwc1`/`swc1` round-trip a word through memory via `$f9` — same witness
-- shapes as `Step.lean`'s own test section for this family.
#guard (match step (prog1Spec (.mtc1 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => s.fpRegs.getD 3 0#32 == 0x12345678#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mtc1 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s1 =>
          (match step (prog1Spec (.mfc1 9#32 3#32)) { s1 with pc := textBase } with
           | .next s2 => readReg s2 9 == 0x12345678#32
           | .halt _ => false)
        | .halt _ => false) = true
#guard (match writeMemWord (initialState textBase) 0x10010000#32 0x3f800000#32 with
        | some m =>
          (match step (prog1Spec (.lwc1 8#32 9#32 0#32))
                  (setRegsSpec m [(8, 0x10010000#32)]) with
           | .next s => s.fpRegs.getD 9 0#32 == 0x3f800000#32
           | .halt _ => false)
        | none => false) = true
#guard (match step (prog1Spec (.swc1 8#32 9#32 0#32))
          (writeFpReg (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) 9 0x3f800000#32) with
        | .next s => readMemWord s 0x10010000#32 == some 0x3f800000#32
        | .halt _ => false) = true
-- `lwc1`/`swc1` alignment rules match `lw`/`sw` exactly.
#guard (match step (prog1Spec (.lwc1 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .halt (.addressError _) => true
        | _ => false) = true
#guard (match step (prog1Spec (.swc1 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .halt (.addressError _) => true
        | _ => false) = true
-- `abs.s`: `-3.0` (`0xc0400000`) -> `3.0` (`0x40400000`); `3.0` -> `3.0`
-- (already positive, sign bit already clear).
#guard (match step (prog1Spec (.absS 8#32 3#32)) (writeFpReg (initialState textBase) 3 0xc0400000#32) with
        | .next s => s.fpRegs.getD 8 0#32 == 0x40400000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.absS 8#32 3#32)) (writeFpReg (initialState textBase) 3 0x40400000#32) with
        | .next s => s.fpRegs.getD 8 0#32 == 0x40400000#32
        | .halt _ => false) = true
-- `neg.s`: `3.0` (`0x40400000`) -> `-3.0` (`0xc0400000`); `-3.0` -> `3.0`.
#guard (match step (prog1Spec (.negS 8#32 3#32)) (writeFpReg (initialState textBase) 3 0x40400000#32) with
        | .next s => s.fpRegs.getD 8 0#32 == 0xc0400000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.negS 8#32 3#32)) (writeFpReg (initialState textBase) 3 0xc0400000#32) with
        | .next s => s.fpRegs.getD 8 0#32 == 0x40400000#32
        | .halt _ => false) = true

/-- **`mfc0` reads one of the three modeled CP0 registers
(`cp0Status`/`cp0Cause`/`cp0Epc`, selected by `rd = 12/13/14`) into GPR
`$rt`; any other `rd` halts with `illegalInstruction`** — this model has no
backing register for any other CP0 register number, and halting is the
honest choice over fabricating a read (`Step.lean`'s `mfc0`/`mtc0`
docstring; `docs/spec/MIPS-COVERAGE-GAPS.md` §3.10A). -/
theorem mfc0_spec_raw (p : Program) (s : State) (w rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      match rd.toNat with
      | 12 =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) s.cp0Status) with
            pc := (writeReg s (regIdxSpec rt) s.cp0Status).pc + 4#32 }
      | 13 =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) s.cp0Cause) with
            pc := (writeReg s (regIdxSpec rt) s.cp0Cause).pc + 4#32 }
      | 14 =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) s.cp0Epc) with
            pc := (writeReg s (regIdxSpec rt) s.cp0Epc).pc + 4#32 }
      | _ => StepResult.halt (.illegalInstruction w) := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mtc0` writes GPR `$rt` into one of the three modeled CP0 registers
(`rd = 12/13/14`); any other `rd` halts with `illegalInstruction`** — same
scoping and same halt choice as `mfc0_spec_raw`. -/
theorem mtc0_spec_raw (p : Program) (s : State) (w rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      match rd.toNat with
      | 12 =>
        StepResult.next
          { ({ s with cp0Status := readReg s (regIdxSpec rt) }) with
            pc := ({ s with cp0Status := readReg s (regIdxSpec rt) }).pc + 4#32 }
      | 13 =>
        StepResult.next
          { ({ s with cp0Cause := readReg s (regIdxSpec rt) }) with
            pc := ({ s with cp0Cause := readReg s (regIdxSpec rt) }).pc + 4#32 }
      | 14 =>
        StepResult.next
          { ({ s with cp0Epc := readReg s (regIdxSpec rt) }) with
            pc := ({ s with cp0Epc := readReg s (regIdxSpec rt) }).pc + 4#32 }
      | _ => StepResult.halt (.illegalInstruction w) := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`eret` sets `pc := cp0Epc` directly and clears `Status.EXL`
(`cp0Status`'s bit 1), bypassing the usual one-instruction delay-slot
scheduling entirely** — real MIPS32's one explicit exception to the
global delay-slot rule (MD00086 Rev 2.50 §3.2, Table 3-23; `Step.lean`'s
`eret` docstring). Unlike every branch/jump theorem in this file
(`beq_spec_raw`, `jr_spec_raw`, …), the right-hand side here has no
`pendingBranch := some _` scheduling at all: `pc` lands on `cp0Epc`
immediately, in the very same step. `eret`'s own effect never actually
reads or threads `pendingBranch` through `mkNext`/`advance` the way every
other control-flow instruction does (it is carried over unchanged via
`{s with ...}`); the `hpb : s.pendingBranch = none` hypothesis below is
kept only because this proof's closing `rfl` needs `pendingBranch` pinned
to a concrete constructor (the same `obtain`/`subst` shape used
throughout this file) — it is not semantically required by `eret` itself.
`eret_bypasses_delay_slot` below proves the identical equation again with
`s.pendingBranch = some t` for an arbitrary target `t` instead, which is
the sharpest way to state that `eret` truly ignores any pending
transfer. -/
theorem eret_spec_raw (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`eret` is not delay-slotted: this is an explicit architectural
exception to the rest of this file's branch/jump convention.** Stated at
its sharpest: even when a previous branch/jump already left a delay-slot
transfer pending (`s.pendingBranch = some t`, for an arbitrary target `t`),
an `eret` executed in that delay slot still lands on `cp0Epc`, *not* on
`t` — the pending transfer is neither consulted nor consumed. Contrast
with `beq_taken_delay_slot_lands_on_target`, where a delay-slot instruction
*does* resolve the pending transfer via `mkNext`/`advance`. Proved
independently of `eret_spec_raw` (same tactic shape, with a concrete
`pendingBranch = some t` instead of `= none`) rather than derived from it,
since the two theorems carry incompatible `hpb` hypotheses. -/
theorem eret_bypasses_delay_slot (p : Program) (s : State) (w t : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = some t) :
    step p s =
      StepResult.next { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`wait` is a documented no-op**: this simulator has no
interrupt/timer model, so `wait` just falls through to `pc + 4` like any
ordinary non-control-flow instruction, touching no other state
(`Step.lean`'s `wait` docstring: `mkNext s s`). -/
theorem wait_spec_raw (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .wait)
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `wait_spec_raw`: every piece of state besides `pc` is
left untouched — the "no-op" claim made precise, not just "produces some
next state". -/
theorem wait_preserves_state (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .wait)
    (hpb : s.pendingBranch = none) :
    ∃ s', step p s = StepResult.next s' ∧ s'.regs = s.regs ∧ s'.fpRegs = s.fpRegs ∧
      s'.hi = s.hi ∧ s'.lo = s.lo ∧ s'.mem = s.mem ∧ s'.out = s.out ∧
      s'.cp0Status = s.cp0Status ∧ s'.cp0Cause = s.cp0Cause ∧ s'.cp0Epc = s.cp0Epc ∧
      s'.pc = s.pc + 4#32 := by
  refine ⟨_, wait_spec_raw p s w hfetch hdecode hpb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- `mfc0` reads back each of the three real CP0 registers, selected by `rd`;
-- an out-of-scope `rd` halts with `illegalInstruction`.
#guard (match step (prog1Spec (.mfc0 8#32 12#32)) { (initialState textBase) with cp0Status := 0x2#32 } with
        | .next s => readReg s 8 == 0x2#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mfc0 8#32 13#32)) { (initialState textBase) with cp0Cause := 0x34#32 } with
        | .next s => readReg s 8 == 0x34#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mfc0 8#32 14#32)) { (initialState textBase) with cp0Epc := 0x3000#32 } with
        | .next s => readReg s 8 == 0x3000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mfc0 8#32 0#32)) (initialState textBase) with
        | .halt (.illegalInstruction _) => true
        | _ => false) = true

-- `mtc0` writes each of the three real CP0 registers from a GPR; an
-- out-of-scope `rd` halts with `illegalInstruction`.
#guard (match step (prog1Spec (.mtc0 8#32 12#32)) (setRegsSpec (initialState textBase) [(8, 0x2#32)]) with
        | .next s => s.cp0Status == 0x2#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mtc0 8#32 13#32)) (setRegsSpec (initialState textBase) [(8, 0x34#32)]) with
        | .next s => s.cp0Cause == 0x34#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mtc0 8#32 14#32)) (setRegsSpec (initialState textBase) [(8, 0x3000#32)]) with
        | .next s => s.cp0Epc == 0x3000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mtc0 8#32 0#32)) (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .halt (.illegalInstruction _) => true
        | _ => false) = true

-- `eret` restores `pc` from `cp0Epc` and clears `Status.EXL`.
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask } with
        | .next s => s.pc == 0x3000#32 && s.cp0Status == 0#32
        | .halt _ => false) = true
-- `eret` ignores a pending delay-slot transfer entirely: `pc` still lands
-- on `cp0Epc`, not on the pending target `0x9999_9999`.
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with
            cp0Epc := 0x3000#32, cp0Status := statusExlMask,
            pendingBranch := some 0x99999999#32 } with
        | .next s => s.pc == 0x3000#32
        | .halt _ => false) = true

-- `wait` falls through to `pc + 4`, touching no other state.
#guard (match step (prog1Spec .wait) (initialState textBase) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == (initialState textBase).cp0Status &&
            s.regs == (initialState textBase).regs
        | .halt _ => false) = true

/-! ### Stretch goal: one real `Float32`-arithmetic instruction (`add.s`)

Everything above this point needs no `Float32` reasoning at all. `add.s` is
the one arithmetic FPU instruction attempted beyond that low-risk set
(priority 3 of this section); it closed cleanly with the exact same
`obtain`/`unfold step`/`rfl` technique as every other theorem in this file,
so it is included as a genuine proof rather than left as a stretch note.
`floatOfBitsSpec`/`bitsOfFloatSpec` mirror `Step.lean`'s private
`floatOfBits`/`bitsOfFloat` (`Float32.ofBits`/`.toBits` round-trip through
a `W32`'s raw bit pattern), the same way `regIdxSpec` mirrors `regIdx`. -/

/-- Mirrors `Step.lean`'s private `floatOfBits`: reinterprets `w`'s raw bit
pattern as an IEEE-754 single-precision float, no numeric conversion. -/
def floatOfBitsSpec (w : W32) : Float32 := Float32.ofBits w.toNat.toUInt32

/-- Mirrors `Step.lean`'s private `bitsOfFloat`: the inverse of
`floatOfBitsSpec`, the raw bit pattern of `f` as a `W32`. -/
def bitsOfFloatSpec (f : Float32) : W32 := BitVec.ofNat 32 f.toBits.toNat

/-- **`add.s` writes `$fd := Float32.add (float $fs) (float $ft)`, both
operands and the result read/written as raw bit patterns via
`floatOfBitsSpec`/`bitsOfFloatSpec`** (INSTRUCTION-REF "add.s" section;
`Step.lean`'s `addS` case). No rounding-mode or trap behavior beyond Lean
core's `Float32.add` is modeled, matching the module's documented IEEE-754
scope. -/
theorem addS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addS fd fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).add
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)) with
          pc := (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `add.s`: `1.0` (`0x3f800000`) + `2.0` (`0x40000000`) = `3.0`
-- (`0x40400000`), the standard IEEE-754 single-precision bit patterns.
#guard (match step (prog1Spec (.addS 8#32 3#32 4#32))
          (writeFpReg (writeFpReg (initialState textBase) 3 0x3f800000#32) 4 0x40000000#32) with
        | .next s => s.fpRegs.getD 8 0#32 == 0x40400000#32
        | .halt _ => false) = true

/-! ## Group 7 — `lwl`/`lwr`/`swl`/`swr`: classic MIPS32 unaligned load/store pair

Real MIPS32 classic (pre-r6) unaligned-memory-access family (MD00086 Rev
2.50 §3.2, Table 3-4; `docs/spec/INSTRUCTION-REF.md`'s dedicated section).
Unlike `lw`/`sw`, the effective address has no alignment requirement at
all: `readMemByte`/`writeMemByte` are already total, so none of these four
`step` cases can ever halt — `lwl_spec_raw`/`lwr_spec_raw` have no
`addressError` branch at all (contrast `lw_spec_raw`), and
`swl_spec_raw`/`swr_spec_raw`, like `sw_spec_raw`, only ever clear `llBit`.
Each RHS below reconstructs `Step.lean`'s own four-way
`off := addr.toNat % 4` match verbatim, using the `setByteSlotSpec`/
`getByteSlotSpec` mirrors declared at the top of this file plus the public
`readMemByte`/`writeMemByte` — the same technique `sc_spec_raw`/
`div_spec_raw` already use for a symbolic `if`/`match` scrutinee that does
not need to resolve for the closing `rfl` to go through. -/

/-- **`lwl` ("load word left") merges 1–4 most-significant bytes starting at
`$rs + sext16(offset)` into the most-significant end of `$rt`, leaving
`$rt`'s existing least-significant bytes untouched** — exactly how many
bytes merge depends on `addr.toNat % 4` (4 at `off = 0`, behaving exactly
like a plain `lw`; down to 1 at `off = 3`). Never halts on a misaligned
address, unlike `lw` (INSTRUCTION-REF `lwl` section). -/
theorem lwl_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwl rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let old := readReg s (regIdxSpec rt)
      let b0 := (readMemByte s addr).getD 0
      let v :=
        match off with
        | 0 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          let b2 := (readMemByte s (addr + 2#32)).getD 0
          let b3 := (readMemByte s (addr + 3#32)).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2) 3 b3
        | 1 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          let b2 := (readMemByte s (addr + 2#32)).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2
        | 2 =>
          let b1 := (readMemByte s (addr + 1#32)).getD 0
          setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1
        | _ =>  -- off = 3 (Nat match needs a default; addr.toNat % 4 is always < 4)
          setByteSlotSpec old 0 b0
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with
          pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`lwr` ("load word right") merges 1–4 least-significant bytes ending
at `$rs + sext16(offset)` into the least-significant end of `$rt`, leaving
`$rt`'s existing most-significant bytes untouched** — the mirror image of
`lwl_spec_raw`: exactly how many bytes merge depends on `addr.toNat % 4`
(1 at `off = 0`, up to 4 at `off = 3`, behaving exactly like a plain `lw`).
Never halts on a misaligned address, unlike `lw` (INSTRUCTION-REF `lwr`
section). -/
theorem lwr_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lwr rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let old := readReg s (regIdxSpec rt)
      let v :=
        match off with
        | 0 =>
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec old 3 b3
        | 1 =>
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec old 2 b2) 3 b3
        | 2 =>
          let b1 := (readMemByte s (addr - 2#32)).getD 0
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 1 b1) 2 b2) 3 b3
        | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
          let b0 := (readMemByte s (addr - 3#32)).getD 0
          let b1 := (readMemByte s (addr - 2#32)).getD 0
          let b2 := (readMemByte s (addr - 1#32)).getD 0
          let b3 := (readMemByte s addr).getD 0
          setByteSlotSpec (setByteSlotSpec (setByteSlotSpec (setByteSlotSpec old 0 b0) 1 b1) 2 b2) 3 b3
      StepResult.next
        { (writeReg s (regIdxSpec rt) v) with
          pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`swl` ("store word left") stores `$rt`'s most-significant 1–4 bytes
starting at `$rs + sext16(offset)`, and clears `llBit`** (store-class, like
`sw`/`sh`) — exactly how many bytes are stored depends on
`addr.toNat % 4` (4 at `off = 0`, behaving exactly like a plain `sw`; down
to 1 at `off = 3`). Never halts on a misaligned address, unlike `sw`
(INSTRUCTION-REF `swl` section). -/
theorem swl_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swl rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let v := readReg s (regIdxSpec rt)
      let s1 := (writeMemByte s addr (getByteSlotSpec v 0)).getD s
      let s' :=
        match off with
        | 0 =>
          let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
          let s3 := (writeMemByte s2 (addr + 2#32) (getByteSlotSpec v 2)).getD s2
          (writeMemByte s3 (addr + 3#32) (getByteSlotSpec v 3)).getD s3
        | 1 =>
          let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
          (writeMemByte s2 (addr + 2#32) (getByteSlotSpec v 2)).getD s2
        | 2 => (writeMemByte s1 (addr + 1#32) (getByteSlotSpec v 1)).getD s1
        | _ => s1  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
      StepResult.next
        { ({ s' with llBit := false }) with
          pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`swr` ("store word right") stores `$rt`'s least-significant 1–4
bytes ending at `$rs + sext16(offset)`, and clears `llBit`** (store-class,
like `sw`/`sh`) — the mirror image of `swl_spec_raw`: exactly how many
bytes are stored depends on `addr.toNat % 4` (1 at `off = 0`, up to 4 at
`off = 3`, behaving exactly like a plain `sw`). Never halts on a misaligned
address, unlike `sw` (INSTRUCTION-REF `swr` section). -/
theorem swr_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.swr rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let off := addr.toNat % 4
      let v := readReg s (regIdxSpec rt)
      let s' :=
        match off with
        | 0 => (writeMemByte s addr (getByteSlotSpec v 3)).getD s
        | 1 =>
          let s1 := (writeMemByte s (addr - 1#32) (getByteSlotSpec v 2)).getD s
          (writeMemByte s1 addr (getByteSlotSpec v 3)).getD s1
        | 2 =>
          let s1 := (writeMemByte s (addr - 2#32) (getByteSlotSpec v 1)).getD s
          let s2 := (writeMemByte s1 (addr - 1#32) (getByteSlotSpec v 2)).getD s1
          (writeMemByte s2 addr (getByteSlotSpec v 3)).getD s2
        | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
          let s1 := (writeMemByte s (addr - 3#32) (getByteSlotSpec v 0)).getD s
          let s2 := (writeMemByte s1 (addr - 2#32) (getByteSlotSpec v 1)).getD s1
          let s3 := (writeMemByte s2 (addr - 1#32) (getByteSlotSpec v 2)).getD s2
          (writeMemByte s3 addr (getByteSlotSpec v 3)).getD s3
      StepResult.next
        { ({ s' with llBit := false }) with
          pc := ({ s' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Base address for the concrete `lwl`/`lwr`/`swl`/`swr` examples below
(mirrors `Step.lean`'s test-only `unalignedBase`). -/
def unalignedBaseSpec : W32 := 0x10010000#32

/-- Write a list of `(address, byte)` pairs into `s.mem`, for building the
concrete unaligned-memory examples below (mirrors `setRegsSpec`'s `foldl`
shape; `writeMemByte` always succeeds — see its docstring — so the `.getD
acc` fallback is never actually exercised, same as every `.getD` in
`swl_spec_raw`/`swr_spec_raw` above). -/
def setMemBytesSpec (s : State) (kvs : List (W32 × UInt8)) : State :=
  kvs.foldl (fun acc kv => (writeMemByte acc kv.1 kv.2).getD acc) s

/-- Concrete state with `$t0` (register 8) pointing at `unalignedBaseSpec`
and bytes `0x11,0x22,...,0x88` at `unalignedBaseSpec + 0..7`, so every
byte-position merge `lwl`/`lwr` perform is individually visible in the
resulting word (mirrors `Step.lean`'s test-only `unalignedTestState`). -/
def unalignedTestStateSpec : State :=
  setMemBytesSpec (setRegsSpec (initialState textBase) [(8, unalignedBaseSpec)])
    [(unalignedBaseSpec + 0#32, 0x11), (unalignedBaseSpec + 1#32, 0x22),
     (unalignedBaseSpec + 2#32, 0x33), (unalignedBaseSpec + 3#32, 0x44),
     (unalignedBaseSpec + 4#32, 0x55), (unalignedBaseSpec + 5#32, 0x66),
     (unalignedBaseSpec + 6#32, 0x77), (unalignedBaseSpec + 7#32, 0x88)]

/-- Concrete state with `$t0` pointing at `unalignedBaseSpec` and `$t1`
holding `0xaabbccdd`, for the `swl`/`swr` examples below (mirrors
`Step.lean`'s test-only `swTestState`). -/
def swTestStateSpec : State :=
  setRegsSpec (initialState textBase) [(8, unalignedBaseSpec), (9, 0xaabbccdd#32)]

-- `lwl_spec_raw`: `off = 0` loads the full word, exactly matching plain `lw`.
#guard (match step (prog1Spec (.lwl 8#32 9#32 0#32)) unalignedTestStateSpec with
        | .next s => readReg s 9 == 0x11223344#32
        | .halt _ => false) = true

-- `lwl_spec_raw`: the three misaligned offsets, `$rt`'s untouched low
-- bytes coming from its prior value.
#guard (match step (prog1Spec (.lwl 8#32 9#32 1#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x000000ff#32)]) with
        | .next s => readReg s 9 == 0x223344ff#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.lwl 8#32 9#32 2#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x0000abcd#32)]) with
        | .next s => readReg s 9 == 0x3344abcd#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.lwl 8#32 9#32 3#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0x00112233#32)]) with
        | .next s => readReg s 9 == 0x44112233#32
        | .halt _ => false) = true

-- `lwr_spec_raw`: `off = 3` loads the full word, exactly matching plain `lw`.
#guard (match step (prog1Spec (.lwr 8#32 9#32 3#32)) unalignedTestStateSpec with
        | .next s => readReg s 9 == 0x11223344#32
        | .halt _ => false) = true

-- `lwr_spec_raw`: the three misaligned offsets, `$rt`'s untouched high
-- bytes coming from its prior value.
#guard (match step (prog1Spec (.lwr 8#32 9#32 0#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaabbcc00#32)]) with
        | .next s => readReg s 9 == 0xaabbcc11#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.lwr 8#32 9#32 1#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaabb0000#32)]) with
        | .next s => readReg s 9 == 0xaabb1122#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.lwr 8#32 9#32 2#32))
          (setRegsSpec unalignedTestStateSpec [(9, 0xaa000000#32)]) with
        | .next s => readReg s 9 == 0xaa112233#32
        | .halt _ => false) = true

-- Complementary-pair idiom: `lwl $rt, 1($rs)` then `lwr $rt, 4($rs)`
-- (addresses `A+1` and `A+4`, both unaligned/aligned-boundary-straddling)
-- together reconstruct the unaligned word spanning bytes `A+1..A+4`
-- (`0x22334455`), each byte supplied by exactly one of the two instructions.
-- Both instructions must come from the same two-instruction program (run
-- sequentially via its own advancing `pc`), not two independent
-- single-instruction programs both starting at `textBase`.
#guard (match step (buildProgSpec textBase [.lwl 8#32 9#32 1#32, .lwr 8#32 9#32 4#32])
          unalignedTestStateSpec with
        | .next s1 =>
          (match step (buildProgSpec textBase [.lwl 8#32 9#32 1#32, .lwr 8#32 9#32 4#32]) s1 with
            | .next s2 => readReg s2 9 == 0x22334455#32
            | .halt _ => false)
        | .halt _ => false) = true

-- `swl_spec_raw`: `off = 0` stores the full word, exactly matching plain
-- `sw`, and clears a previously-set `llBit`.
#guard (match step (prog1Spec (.swl 8#32 9#32 0#32)) { swTestStateSpec with llBit := true } with
        | .next s => readMemWord s unalignedBaseSpec == some 0xaabbccdd#32 && s.llBit == false
        | .halt _ => false) = true

-- `swl_spec_raw`: the three misaligned offsets store only the top
-- `4 - off` bytes, starting at `addr`; bytes before `addr` (and after the
-- stored run) are untouched (read back as the zero-fill default).
#guard (match step (prog1Spec (.swl 8#32 9#32 1#32)) swTestStateSpec with
        | .next s =>
          readMemByte s (unalignedBaseSpec + 1#32) == some 0xaa &&
            readMemByte s (unalignedBaseSpec + 2#32) == some 0xbb &&
            readMemByte s (unalignedBaseSpec + 3#32) == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 4#32) == some 0
        | .halt _ => false) = true
#guard (match step (prog1Spec (.swl 8#32 9#32 2#32)) swTestStateSpec with
        | .next s =>
          readMemByte s (unalignedBaseSpec + 2#32) == some 0xaa &&
            readMemByte s (unalignedBaseSpec + 3#32) == some 0xbb
        | .halt _ => false) = true
#guard (match step (prog1Spec (.swl 8#32 9#32 3#32)) swTestStateSpec with
        | .next s => readMemByte s (unalignedBaseSpec + 3#32) == some 0xaa
        | .halt _ => false) = true

-- `swr_spec_raw`: `off = 3` stores the full word, exactly matching plain
-- `sw`, and clears a previously-set `llBit`.
#guard (match step (prog1Spec (.swr 8#32 9#32 3#32)) { swTestStateSpec with llBit := true } with
        | .next s => readMemWord s unalignedBaseSpec == some 0xaabbccdd#32 && s.llBit == false
        | .halt _ => false) = true

-- `swr_spec_raw`: the three misaligned offsets store only the bottom
-- `off + 1` bytes, ending at `addr`.
#guard (match step (prog1Spec (.swr 8#32 9#32 0#32)) swTestStateSpec with
        | .next s => readMemByte s unalignedBaseSpec == some 0xdd
        | .halt _ => false) = true
#guard (match step (prog1Spec (.swr 8#32 9#32 1#32)) swTestStateSpec with
        | .next s =>
          readMemByte s unalignedBaseSpec == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 1#32) == some 0xdd
        | .halt _ => false) = true
#guard (match step (prog1Spec (.swr 8#32 9#32 2#32)) swTestStateSpec with
        | .next s =>
          readMemByte s unalignedBaseSpec == some 0xbb &&
            readMemByte s (unalignedBaseSpec + 1#32) == some 0xcc &&
            readMemByte s (unalignedBaseSpec + 2#32) == some 0xdd
        | .halt _ => false) = true

-- Complementary-pair idiom: `swl $rt, 1($rs)` then `swr $rt, 4($rs)`
-- together store every byte of `$rt` into the unaligned word spanning
-- `A+1..A+4`, exactly once each. Same two-instruction-program caveat as
-- the `lwl`/`lwr` idiom example above.
#guard (match step (buildProgSpec textBase [.swl 8#32 9#32 1#32, .swr 8#32 9#32 4#32])
          swTestStateSpec with
        | .next s1 =>
          (match step (buildProgSpec textBase [.swl 8#32 9#32 1#32, .swr 8#32 9#32 4#32]) s1 with
            | .next s2 =>
              readMemByte s2 (unalignedBaseSpec + 1#32) == some 0xaa &&
                readMemByte s2 (unalignedBaseSpec + 2#32) == some 0xbb &&
                readMemByte s2 (unalignedBaseSpec + 3#32) == some 0xcc &&
                readMemByte s2 (unalignedBaseSpec + 4#32) == some 0xdd
            | .halt _ => false)
        | .halt _ => false) = true


/-! ## Group 8 — SPECIAL2/SPECIAL3 bit-manipulation specs (`clo`, `clz`,
`mul`, `seb`, `seh`, `wsbh`, `ext`, `ins`)

These eight instructions (MIPS32/MIPS32r2 additions, `docs/spec/
MIPS-COVERAGE-GAPS.md` §3.4/§3.5) had an `execInstr` case in `Step.lean` and
`#guard` coverage there, but no `_spec_raw` theorem in this file. This
closes that gap, following the same "mirror the private helper, restate
`step` with public names, close by `rfl`" recipe as every other group above.
The new mirrors they need (`countLeadingZerosFromSpec`/`countLeadingZerosSpec`/
`countLeadingOnesSpec`/`signExtLowByteSpec`/`lowBitsMaskSpec`) live next to
`regIdxSpec` near the top of the file, per this file's existing convention. -/

/-- **`clo` counts `$rs`'s leading one bits (from the MSB) into `$rd`**;
`32` if `$rs` is all-ones (SPECIAL2 opcode 0x1c, funct 0x21; INSTRUCTION-REF
"clo"). -/
theorem clo_spec_raw (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.clo rs rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingOnesSpec (readReg s (regIdxSpec rs))))) with
          pc := (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingOnesSpec (readReg s (regIdxSpec rs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`clz` counts `$rs`'s leading zero bits (from the MSB) into `$rd`**;
`32` if `$rs` is all-zero (SPECIAL2 opcode 0x1c, funct 0x20; INSTRUCTION-REF
"clz"). -/
theorem clz_spec_raw (p : Program) (s : State) (w rs rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.clz rs rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingZerosSpec (readReg s (regIdxSpec rs))))) with
          pc := (writeReg s (regIdxSpec rd)
            (BitVec.ofNat 32 (countLeadingZerosSpec (readReg s (regIdxSpec rs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `clo`/`clz` satisfiable examples, matching `Step.lean`'s own `#guard`s:
-- all-ones -> 32 leading ones, all-zero -> 0; all-zero -> 32 leading zeros.
#guard (match step (prog1Spec (.clo 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => readReg s 10 == 32#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.clo 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xfff0ffff#32)]) with
        | .next s => readReg s 10 == 12#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.clz 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x00000000#32)]) with
        | .next s => readReg s 10 == 32#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.clz 8#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x0000ffff#32)]) with
        | .next s => readReg s 10 == 16#32
        | .halt _ => false) = true

/-- **`mul` writes the low 32 bits of the signed product `$rs * $rt` to
`$rd`; `hi`/`lo` are left completely unchanged** (SPECIAL2 opcode 0x1c,
funct 0x02; INSTRUCTION-REF "mul"). Unlike `mult`, this never touches the
`hi`/`lo` accumulator at all — see `mul_leaves_hi_lo_unchanged` below for
that half of the claim isolated. -/
theorem mul_spec_raw (p : Program) (s : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mul rs rt rd))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rs) * readReg s (regIdxSpec rt))) with
          pc := (writeReg s (regIdxSpec rd)
            (readReg s (regIdxSpec rs) * readReg s (regIdxSpec rt))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **"Bad output rejection" for `mul`**: the resulting state's `hi`/`lo`
read back *exactly* their pre-step values — a buggy implementation that
routed `mul` through the same `hi`/`lo`-writing path as `mult` could never
satisfy this. -/
theorem mul_leaves_hi_lo_unchanged (p : Program) (s s' : State) (w rs rt rd : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mul rs rt rd))
    (hpb : s.pendingBranch = none)
    (hstep : step p s = StepResult.next s') :
    s'.hi = s.hi ∧ s'.lo = s.lo := by
  rw [mul_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
  injection hstep with hs
  rw [← hs]
  exact ⟨writeReg_hi s _ _, writeReg_lo s _ _⟩

-- `mul` satisfiable examples, matching `Step.lean`'s own `#guard`s: the
-- regular product case, and signed wraparound ((-1) * 2 = -2).
#guard (match step (prog1Spec (.mul 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 6#32), (9, 7#32)]) with
        | .next s => readReg s 10 == 42#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mul 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 2#32)]) with
        | .next s => readReg s 10 == 0xfffffffe#32
        | .halt _ => false) = true

/-- **`seb` sign-extends `$rt`'s low byte into `$rd`**, ignoring `$rt`'s
higher bits entirely (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field
0x10; INSTRUCTION-REF "seb"). -/
theorem seb_spec_raw (p : Program) (s : State) (w rd rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.seb rd rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (signExtLowByteSpec (readReg s (regIdxSpec rt)))) with
          pc := (writeReg s (regIdxSpec rd)
            (signExtLowByteSpec (readReg s (regIdxSpec rt)))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`seh` sign-extends `$rt`'s low halfword into `$rd`**, ignoring `$rt`'s
upper 16 bits entirely (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field
0x18; INSTRUCTION-REF "seh"). Reuses the already-public `signExt16` directly
— no new mirror needed (same helper `addi`/`lw`/etc. already use for
immediates). -/
theorem seh_spec_raw (p : Program) (s : State) (w rd rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.seh rd rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rd) (signExt16 (readReg s (regIdxSpec rt)))) with
          pc := (writeReg s (regIdxSpec rd) (signExt16 (readReg s (regIdxSpec rt)))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `seb`/`seh` satisfiable examples, matching `Step.lean`'s own `#guard`s.
#guard (match step (prog1Spec (.seb 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345680#32)]) with
        | .next s => readReg s 10 == 0xffffff80#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.seb 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x1234567f#32)]) with
        | .next s => readReg s 10 == 0x0000007f#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.seh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x1234ffff#32)]) with
        | .next s => readReg s 10 == 0xffffffff#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.seh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12347fff#32)]) with
        | .next s => readReg s 10 == 0x00007fff#32
        | .halt _ => false) = true

/-- **`wsbh` swaps the two bytes within each 16-bit half of `$rt`
independently, leaving the halfwords themselves in place** — not a full
32-bit byte-reverse (SPECIAL3 BSHFL opcode 0x1f, funct 0x20, sub-field 0x02;
INSTRUCTION-REF "wsbh"). The formula is small enough that `Step.lean` writes
it out inline with no private helper, so this restates it directly with no
new mirror needed. -/
theorem wsbh_spec_raw (p : Program) (s : State) (w rd rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.wsbh rd rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := readReg s (regIdxSpec rt)
      let b0 := v &&& 0xff#32
      let b1 := (v >>> 8) &&& 0xff#32
      let b2 := (v >>> 16) &&& 0xff#32
      let b3 := (v >>> 24) &&& 0xff#32
      let result := (b2 <<< 24) ||| (b3 <<< 16) ||| (b0 <<< 8) ||| b1
      StepResult.next
        { (writeReg s (regIdxSpec rd) result) with
          pc := (writeReg s (regIdxSpec rd) result).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `wsbh` satisfiable example, matching `Step.lean`'s own `#guard`: halfword0
-- `0x5678` swaps to `0x7856`, halfword1 `0x1234` swaps to `0x3412`, halfwords
-- stay in place -> `0x34127856`.
#guard (match step (prog1Spec (.wsbh 10#32 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10 == 0x34127856#32
        | .halt _ => false) = true

/-- **`ext` extracts a `size`-bit field of `$rs` starting at bit `pos`,
zero-extended, into `$rt`** (SPECIAL3 opcode 0x1f, funct 0x00;
INSTRUCTION-REF "ext"). `pos`/`size` are already the semantic values here —
`decode` did the raw-field +-1 arithmetic — so this is pure bit masking,
with no special case for the real `pos + size <= 32` hardware constraint
(matching `Step.lean`'s own documented choice). -/
theorem ext_spec_raw (p : Program) (s : State) (w rt rs pos size : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ext rt rs pos size))
    (hpb : s.pendingBranch = none) :
    step p s =
      let field := (readReg s (regIdxSpec rs) >>> pos.toNat) &&& lowBitsMaskSpec size.toNat
      StepResult.next
        { (writeReg s (regIdxSpec rt) field) with
          pc := (writeReg s (regIdxSpec rt) field).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`ins` inserts the low `size` bits of `$rs`, shifted up to bit `pos`,
into `$rt`, leaving every other bit of `$rt` untouched** (SPECIAL3 opcode
0x1f, funct 0x04; INSTRUCTION-REF "ins"). See `ins_outside_field_unchanged`
below for the "every other bit" half of this claim isolated and proved on
its own, the same way `movn`/`movz`'s "genuinely unchanged" properties are
proved elsewhere in this file. -/
theorem ins_spec_raw (p : Program) (s : State) (w rt rs pos size : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ins rt rs pos size))
    (hpb : s.pendingBranch = none) :
    step p s =
      let mask := lowBitsMaskSpec size.toNat
      let srcField := (readReg s (regIdxSpec rs) &&& mask) <<< pos.toNat
      let clearMask := ~~~(mask <<< pos.toNat)
      let newVal := (readReg s (regIdxSpec rt) &&& clearMask) ||| srcField
      StepResult.next
        { (writeReg s (regIdxSpec rt) newVal) with
          pc := (writeReg s (regIdxSpec rt) newVal).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **"Bad output rejection" for `ins`**: after `ins` runs, `$rt`'s bits
*outside* the `[pos, pos+size)` target field read back *exactly* their
pre-step values — a buggy implementation that e.g. zeroed the rest of `$rt`
instead of preserving it could never satisfy this. The field-boundary mask
`clearMask` is exactly `ins_spec_raw`'s own `clearMask`, so this is a direct
algebraic consequence of that equation (`bv_decide` closes the bitvector
identity: ORing in a field that `clearMask` already zeroes out cannot change
what survives when `clearMask` is applied again). Needs `regIdxSpec rt ≠ 0`
(a write to `$zero` is a no-op, INSTRUCTION-REF Global rule 2) and
`s.regs.size = 32` (`writeReg_reads_back`'s side condition, guaranteed by
`initialState` — `State.lean`). -/
theorem ins_outside_field_unchanged (p : Program) (s s' : State) (w rt rs pos size : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ins rt rs pos size))
    (hpb : s.pendingBranch = none)
    (hrt : regIdxSpec rt ≠ 0) (hsize32 : s.regs.size = 32)
    (hstep : step p s = StepResult.next s') :
    let clearMask := ~~~(lowBitsMaskSpec size.toNat <<< pos.toNat)
    readReg s' (regIdxSpec rt) &&& clearMask = readReg s (regIdxSpec rt) &&& clearMask := by
  rw [ins_spec_raw p s w rt rs pos size hfetch hdecode hpb] at hstep
  injection hstep with hs
  have hr : readReg s' (regIdxSpec rt) =
      (readReg s (regIdxSpec rt) &&& ~~~(lowBitsMaskSpec size.toNat <<< pos.toNat)) |||
        ((readReg s (regIdxSpec rs) &&& lowBitsMaskSpec size.toNat) <<< pos.toNat) := by
    rw [← hs]
    exact writeReg_reads_back s (regIdxSpec rt) _ hrt hsize32
  dsimp only
  rw [hr]
  bv_decide

-- `ext`/`ins` satisfiable examples, matching `Step.lean`'s own `#guard`s.
#guard (match step (prog1Spec (.ext 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)]) with
        | .next s => readReg s 10 == ((0x12345678#32 >>> 6) &&& 0x3ff#32)
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ext 10#32 8#32 0#32 32#32))
          (setRegsSpec (initialState textBase) [(8, 0x89abcdef#32)]) with
        | .next s => readReg s 10 == 0x89abcdef#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ins 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x159#32), (10, 0x12345678#32)]) with
        | .next s => readReg s 10 == ((0x12345678#32 &&& ~~~(0x3ff#32 <<< 6)) ||| ((0x159#32 &&& 0x3ff#32) <<< 6))
        | .halt _ => false) = true
-- `ins_outside_field_unchanged` concrete witness: bits outside `[6, 16)` of
-- `$t2` survive the `ins` untouched.
#guard (match step (prog1Spec (.ins 10#32 8#32 6#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x159#32), (10, 0x12345678#32)]) with
        | .next s => (readReg s 10 &&& ~~~(0x3ff#32 <<< 6)) == (0x12345678#32 &&& ~~~(0x3ff#32 <<< 6))
        | .halt _ => false) = true


/-! ## Group 8 — immediate-operand trap family (`teqi`, `tnei`, `tgei`,
`tgeiu`, `tlti`, `tltiu`)

Ground truth: `docs/spec/INSTRUCTION-REF.md`'s REGIMM trap-immediate
subsection and `docs/spec/MIPS-COVERAGE-GAPS.md` §3.8, mirrored directly
from `Step.lean`'s `.teqi`/`.tnei`/`.tgei`/`.tgeiu`/`.tlti`/`.tltiu` cases.
These six are the sign-extended-16-bit-immediate counterparts of Group 6's
`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu`: same coprocessor-0 `takeException`
shape (`cp0Epc`/`cp0Cause`/`cp0Status`/`pc` all change together on the
trapping branch, plain fallthrough to `pc + 4#32` otherwise), comparing
`$rs` against `signExt16 imm` instead of against a second register.
`tgeiu`/`tltiu` sign-extend the immediate to a full 32-bit value *first*,
exactly like `sltiu` does for its immediate, and only then compare the
resulting bit pattern as unsigned (confirmed against `Step.lean`'s actual
`.tgeiu`/`.tltiu` cases, which call `signExt16 imm` and then compare
`.toNat` values — not zero-extension, and not a signed comparison). As in
Group 6, every theorem below needs `hpb : s.pendingBranch = none` because
`execInstr` opens with an unconditional `pendingBranch`/`isBranchLike`
guard before dispatching to any instruction's own case. -/

/-- **`teqi` traps iff `$rs == sext16(imm)`**, taking the shared
coprocessor-0 exception with `excCode = excCodeTr`; otherwise it is a
complete no-op beyond the ordinary fallthrough to `pc + 4#32` (REGIMM
trap-immediate subsection; mirrors `teq_spec_raw` with `sext16 imm` in
place of `$rt`). -/
theorem teqi_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.teqi rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == signExt16 imm then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tnei` traps iff `$rs ≠ sext16(imm)`** — the mirror image of `teqi`
(REGIMM trap-immediate subsection). -/
theorem tnei_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tnei rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) ≠ signExt16 imm then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tgei` traps iff `$rs ≥s sext16(imm)`**, a *signed* comparison
(REGIMM trap-immediate subsection; mirrors `tge_spec_raw`). -/
theorem tgei_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgei rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≥ asSigned (signExt16 imm) then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tgeiu` sign-extends the 16-bit immediate to a full 32-bit value
first, exactly like `tgei`, then compares the resulting bit patterns as
*unsigned*** — the "u" affects only the comparison, not the immediate's
extension (same convention as `sltiu`; confirmed against `Step.lean`'s
`.tgeiu` case, which calls `signExt16 imm` and then compares `.toNat`
values). -/
theorem tgeiu_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgeiu rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat ≥ (signExt16 imm).toNat then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tlti` traps iff `$rs <s sext16(imm)`**, a *signed* comparison
(REGIMM trap-immediate subsection; mirrors `tlt_spec_raw`). -/
theorem tlti_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tlti rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < asSigned (signExt16 imm) then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`tltiu` sign-extends the 16-bit immediate to a full 32-bit value
first, exactly like `tlti`, then compares the resulting bit patterns as
*unsigned*** — the mirror image of `tgeiu` (same convention as `sltiu`;
confirmed against `Step.lean`'s `.tltiu` case, which calls `signExt16 imm`
and then compares `.toNat` values). -/
theorem tltiu_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tltiu rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat < (signExt16 imm).toNat then
        StepResult.next
          { s with
              cp0Epc := s.pc
              cp0Cause := excCodeTr <<< 2
              cp0Status := s.cp0Status ||| statusExlMask
              pc := exceptionVectorAddr }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `teqi_spec_raw`/`tnei_spec_raw`: `$rs == sext16(imm)` traps under `teqi`
-- (and is a no-op under `tnei`); a mismatch is the mirror image. One
-- `#guard` per instruction per branch, matching the house style used for
-- `teq`/`tne` above.
#guard (match step (prog1Spec (.teqi 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == statusExlMask && s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.teqi 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == 0#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tnei 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 6#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == statusExlMask && s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tnei 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == 0#32
        | .halt _ => false) = true

-- `tgei_spec_raw`/`tlti_spec_raw`: `sext16 0xffff = -1`, so `-1` (as
-- `0xffffffff`) is signed-greater-or-equal to `-1` under `tgei` (traps) but
-- not signed-less-than `-1` under `tlti` (no trap); `1 < 1` is false so
-- `tlti 1` also does not trap on `$rs = 1`.
#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tlti 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tlti 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `tgeiu_spec_raw`/`tltiu_spec_raw`: `sext16 1 = 1`, and `0xffffffff` is the
-- *largest* unsigned value, so `$rs = 0xffffffff` is never `<u 1` under
-- `tltiu` but always `≥u 1` under `tgeiu` — the same edge case
-- `sltiu`/`tltu`/`tgeu` above use. A second pair with `sext16 0xffff =
-- 0xffffffff` and `$rs = 1` confirms `tgeiu` really compares unsigned
-- (`1 ≥u 0xffffffff` is false), not signed like `tgei` (where the same
-- inputs trap, since `1 ≥s -1`).
#guard (match step (prog1Spec (.tgeiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tltiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tltiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tgeiu 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true


/-! ## Group N — FPU: remaining single-precision instructions (zero-coverage set)

This section proves `_spec_raw` theorems for every single-precision FPU
`Instruction` constructor that had no `StepSpec.lean` theorem at all before
this pass: `cfc1`/`ctc1`, `movS`, `cvtSW`/`cvtWS`, `sqrtS`,
`roundWS`/`truncWS`/`ceilWS`/`floorWS`, `subS`/`mulS`/`divS`, and the seven
remaining compare predicates `cFS`/`cUnS`/`cUeqS`/`cOltS`/`cUltS`/`cOleS`/
`cUleS` (plus `cEqS`/`cLtS`/`cLeS`, which — contrary to what the STALL NOTE
above was written against — also had no theorem yet). Every theorem uses
the exact same `obtain`/`unfold step`/`rw`/`dsimp only`/`rfl` technique as
`addS_spec_raw` and the rest of this file; the right-hand sides are copied
field-for-field from `Step.lean`'s own `execInstr` match arms (read at
proof-writing time, not guessed), using only public names plus the local
mirrors declared just below. -/

/-- Mirrors `Step.lean`'s private `floatOfIntBits`: `cvt.s.w`'s numeric
conversion, reading `w`'s bit pattern as a 32-bit two's-complement int
(`Int32.ofBitVec`) and converting that integer *value* to the nearest
`Float32` (`Int32.toFloat32`, exact for every `Int32`). -/
def floatOfIntBitsSpec (w : W32) : Float32 := (Int32.ofBitVec w).toFloat32

/-- Mirrors `Step.lean`'s private `intBitsOfFloatTrunc`: `cvt.w.s`'s numeric
conversion, truncating `f` toward zero to a 32-bit two's-complement int
(`Float32.toInt32`, which clamps on overflow and maps `NaN` to `0`),
returned as a raw bit pattern. -/
def intBitsOfFloatTruncSpec (f : Float32) : W32 := f.toInt32.toBitVec

/-- Mirrors `Step.lean`'s private `intBitsOfFloatRound`: `round.w.s`'s
numeric conversion, rounding `f` to the nearest integer via `Float32.round`
(ties away from zero), then clamp/convert to `Int32` the same way
`intBitsOfFloatTruncSpec` does. -/
def intBitsOfFloatRoundSpec (f : Float32) : W32 := f.round.toInt32.toBitVec

/-- Mirrors `Step.lean`'s private `intBitsOfFloatCeil`: `ceil.w.s`'s numeric
conversion, rounding `f` toward +Infinity (`Float32.ceil`), then
clamp/convert to `Int32`. -/
def intBitsOfFloatCeilSpec (f : Float32) : W32 := f.ceil.toInt32.toBitVec

/-- Mirrors `Step.lean`'s private `intBitsOfFloatFloor`: `floor.w.s`'s
numeric conversion, rounding `f` toward -Infinity (`Float32.floor`), then
clamp/convert to `Int32`. -/
def intBitsOfFloatFloorSpec (f : Float32) : W32 := f.floor.toInt32.toBitVec

/-- **`mov.s` copies `$fs`'s raw 32-bit bit pattern into `$fd`, with no
numeric conversion at all** (INSTRUCTION-REF "mov.s" section; `Step.lean`'s
`movS` case is a plain `readFpReg`/`writeFpReg` move, not `Float32`
arithmetic — exact for every bit pattern, including NaN payloads). -/
theorem movS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs))) with
          pc := (writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `mov.s`: `3.0` (`0x40400000`) copies through unchanged.
#guard (match step (prog1Spec (.movS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x40400000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x40400000#32
        | .halt _ => false) = true

/-- **`cfc1` copies FPU-control-register `$fs`'s raw 32-bit bit pattern into
GPR `$rt`** — this model has no `FCSR`/`FIR` control-register state at all,
so, per `Instruction.cfc1`'s docstring, `cfc1`/`ctc1` reuse the very same
`fpRegs` array the data instructions (`mfc1`/`addS`/…) use as an ordinary
32-bit scratch slot (register 31 conventionally standing in for `FCSR`),
with no rounding-mode/exception-flag behavior modeled behind it. The
`Step.lean` formula is therefore **identical** to `mfc1_spec_raw`'s
right-hand side — same `readFpReg s (regIdxSpec fs)` into `writeReg s
(regIdxSpec rt)` — the two constructors exist because they are distinct
real-MIPS32 encodings (`rs`-position field `CF` vs the ordinary data-move
encoding), not because the modeled behavior differs. -/
theorem cfc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cfc1 rt fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg s (regIdxSpec rt) (readFpReg s (regIdxSpec fs))) with
          pc := (writeReg s (regIdxSpec rt) (readFpReg s (regIdxSpec fs))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`ctc1` copies GPR `$rt`'s raw 32-bit bit pattern into FPU-control
"register" `$fs`** — the inverse move of `cfc1_spec_raw`, same shared-
`fpRegs`-scratch-slot model (`Instruction.ctc1`'s docstring). Identical
right-hand side to `mtc1_spec_raw`, for the same reason `cfc1_spec_raw`'s is
identical to `mfc1_spec_raw`'s. -/
theorem ctc1_spec_raw (p : Program) (s : State) (w rt fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ctc1 rt fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fs) (readReg s (regIdxSpec rt))) with
          pc := (writeFpReg s (regIdxSpec fs) (readReg s (regIdxSpec rt))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `ctc1` then `cfc1` round-trips an arbitrary bit pattern through the
-- shared `fpRegs` scratch slot (register 31, standing in for `FCSR`) —
-- same round-trip shape as `mtc1`/`mfc1` above.
#guard (match step (prog1Spec (.ctc1 8#32 31#32)) (setRegsSpec (initialState textBase) [(8, 0x00000003#32)]) with
        | .next s => s.fpRegs.getD 31 0#32 == 0x00000003#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ctc1 8#32 31#32)) (setRegsSpec (initialState textBase) [(8, 0x00000003#32)]) with
        | .next s1 =>
          (match step (prog1Spec (.cfc1 9#32 31#32)) { s1 with pc := textBase } with
           | .next s2 => readReg s2 9 == 0x00000003#32
           | .halt _ => false)
        | .halt _ => false) = true

/-- **`sub.s` writes `$fd := Float32.sub (float $fs) (float $ft)`**, the
same shape as `addS_spec_raw` with `Float32.sub` in place of `Float32.add`
(INSTRUCTION-REF "sub.s" section; `Step.lean`'s `subS` case). -/
theorem subS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.subS fd fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).sub
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)) with
          pc := (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mul.s` writes `$fd := Float32.mul (float $fs) (float $ft)`**, same
shape as `addS_spec_raw`/`subS_spec_raw` with `Float32.mul`
(INSTRUCTION-REF "mul.s" section; `Step.lean`'s `mulS` case). -/
theorem mulS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mulS fd fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).mul
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)) with
          pc := (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`div.s` writes `$fd := Float32.div (float $fs) (float $ft)`** — IEEE-754
division; `$ft == 0` yields ±Infinity/NaN per IEEE-754, never a trap
(module docstring; SPEC-NOTES §9 item 2 precedent), same shape as
`addS_spec_raw` with `Float32.div` (INSTRUCTION-REF "div.s" section;
`Step.lean`'s `divS` case). -/
theorem divS_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.divS fd fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).div
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)) with
          pc := (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `sub.s`: `5.0 - 2.0 = 3.0`; `mul.s`: `2.0 * 3.0 = 6.0`; `div.s`:
-- `6.0 / 2.0 = 3.0`, and `div.s` by zero gives `+Infinity`, not a trap.
#guard (match step (prog1Spec (.subS 10#32 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x40a00000#32) 9 0x40000000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x40400000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mulS 10#32 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x40000000#32) 9 0x40400000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x40c00000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.divS 10#32 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x40c00000#32) 9 0x40000000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x40400000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.divS 10#32 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x00000000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x7f800000#32
        | .halt _ => false) = true

/-- **`cvt.s.w` writes `$fd := float32(int32bits($fs))`** — numeric
conversion of `$fs`'s bit pattern read as a 32-bit two's-complement int,
*not* a raw bit-pattern copy (INSTRUCTION-REF "cvt.s.w" section;
`Step.lean`'s `cvtSW` case uses `floatOfIntBits`/`floatOfIntBitsSpec`). -/
theorem cvtSW_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtSW fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd)
            (bitsOfFloatSpec (floatOfIntBitsSpec (readFpReg s (regIdxSpec fs))))) with
          pc := (writeFpReg s (regIdxSpec fd)
            (bitsOfFloatSpec (floatOfIntBitsSpec (readFpReg s (regIdxSpec fs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`cvt.w.s` writes `$fd := int32bits(trunc($fs))`**, truncating toward
zero — real MIPS32 rounds per the current FCSR rounding mode, but this v1.x
addition always truncates (no `FCSR` in scope; `Instruction.cvtWS`'s
docstring; `Step.lean`'s `cvtWS` case uses `intBitsOfFloatTrunc`/
`intBitsOfFloatTruncSpec`). -/
theorem cvtWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtWS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatTruncSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))) with
          pc := (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatTruncSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `cvt.s.w`: `5` -> `5.0` (`0x40a00000`); `-5` (`0xfffffffb`) -> `-5.0`.
#guard (match step (prog1Spec (.cvtSW 10#32 8#32)) (writeFpReg (initialState textBase) 8 5#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x40a00000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cvtSW 10#32 8#32)) (writeFpReg (initialState textBase) 8 0xfffffffb#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0xc0a00000#32
        | .halt _ => false) = true
-- `cvt.w.s`: `5.9` (`0x40bccccd`) -> `5` (truncated toward zero, not
-- rounded); `-5.9` (`0xc0bccccd`) -> `-5`.
#guard (match step (prog1Spec (.cvtWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x40bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x00000005#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cvtWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0xc0bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0xfffffffb#32
        | .halt _ => false) = true

/-- **`sqrt.s` writes `$fd := Float32.sqrt (float $fs)`** — correctly-rounded
IEEE-754 single-precision square root (`Instruction.sqrtS`'s docstring;
`Step.lean`'s `sqrtS` case). -/
theorem sqrtS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sqrtS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).sqrt
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)) with
          pc := (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec v)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `sqrt.s`: `4.0` (`0x40800000`) -> `2.0` (`0x40000000`).
#guard (match step (prog1Spec (.sqrtS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x40800000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x40000000#32
        | .halt _ => false) = true

/-- **`round.w.s` writes `$fd := int32bits(round($fs))`**, rounding to the
nearest integer via Lean core's `Float32.round` (ties **away from zero**,
not to even — a documented simplification; `Instruction.roundWS`'s
docstring; `Step.lean`'s `roundWS` case). -/
theorem roundWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.roundWS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatRoundSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))) with
          pc := (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatRoundSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`trunc.w.s` writes `$fd := int32bits(trunc($fs))`** — numerically
**identical** to `cvtWS_spec_raw`'s right-hand side under this model (both
truncate toward zero via `Float32.toInt32`; `Instruction.truncWS`'s
docstring documents the overlap as intentional, not an oversight). -/
theorem truncWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.truncWS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatTruncSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))) with
          pc := (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatTruncSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`ceil.w.s` writes `$fd := int32bits(ceil($fs))`**, rounding toward
+Infinity via `Float32.ceil` (`Instruction.ceilWS`'s docstring; `Step.lean`'s
`ceilWS` case). -/
theorem ceilWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ceilWS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatCeilSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))) with
          pc := (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatCeilSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`floor.w.s` writes `$fd := int32bits(floor($fs))`**, rounding toward
-Infinity via `Float32.floor` (`Instruction.floorWS`'s docstring;
`Step.lean`'s `floorWS` case). -/
theorem floorWS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.floorWS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatFloorSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))) with
          pc := (writeFpReg s (regIdxSpec fd)
            (intBitsOfFloatFloorSpec (floatOfBitsSpec (readFpReg s (regIdxSpec fs))))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `round.w.s`: `5.9` (`0x40bccccd`) -> `6` (ties away from zero, not
-- ties-to-even); `-5.9` (`0xc0bccccd`) -> `-6`; an exact tie `2.5`
-- (`0x40200000`) -> `3`, `-2.5` (`0xc0200000`) -> `-3`.
#guard (match step (prog1Spec (.roundWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x40bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x00000006#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.roundWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0xc0bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0xfffffffa#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.roundWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x40200000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x00000003#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.roundWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0xc0200000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0xfffffffd#32
        | .halt _ => false) = true
-- `trunc.w.s`: `5.9` -> `5`, `-5.9` -> `-5` (truncate toward zero, same as
-- `cvt.w.s`).
#guard (match step (prog1Spec (.truncWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x40bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x00000005#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.truncWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0xc0bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0xfffffffb#32
        | .halt _ => false) = true
-- `ceil.w.s`: `5.9` -> `6`, `-5.9` -> `-5` (round toward +Infinity).
#guard (match step (prog1Spec (.ceilWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x40bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x00000006#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ceilWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0xc0bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0xfffffffb#32
        | .halt _ => false) = true
-- `floor.w.s`: `5.9` -> `5`, `-5.9` -> `-6` (round toward -Infinity).
#guard (match step (prog1Spec (.floorWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x40bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x00000005#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.floorWS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0xc0bccccd#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0xfffffffa#32
        | .halt _ => false) = true

/-- **`c.eq.s` sets `fpCondFlag := Float32.beq (float $fs) (float $ft)`**,
IEEE-754 single-precision equality — no delay slot, unlike `bc1t`/`bc1f`
(INSTRUCTION-REF "c.eq.s" section; `Step.lean`'s `cEqS` case). -/
theorem cEqS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cEqS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).beq
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.lt.s` sets `fpCondFlag := Float32.lt (float $fs) (float $ft)`**
(INSTRUCTION-REF "c.lt.s" section; `Step.lean`'s `cLtS` case). Same modeled
result as `cOltS_spec_raw` below — see that theorem's docstring for why. -/
theorem cLtS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cLtS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).lt
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.le.s` sets `fpCondFlag := Float32.le (float $fs) (float $ft)`**
(INSTRUCTION-REF "c.le.s" section; `Step.lean`'s `cLeS` case). Same modeled
result as `cOleS_spec_raw` below. -/
theorem cLeS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cLeS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).le
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `c.eq.s`: `1.0 == 1.0` is true, `1.0 == 2.0` is false.
#guard (match step (prog1Spec (.cEqS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cEqS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x40000000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
-- `c.lt.s`: `1.0 < 2.0` is true, `2.0 < 1.0` is false.
#guard (match step (prog1Spec (.cLtS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x40000000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cLtS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x40000000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
-- `c.le.s`: `1.0 <= 1.0` is true.
#guard (match step (prog1Spec (.cLeS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true

/-- **`c.f.s` sets `fpCondFlag := false` unconditionally**, ignoring both
operands entirely — real MIPS32's "always false" predicate placeholder
(INSTRUCTION-REF "c.f.s" section; `Step.lean`'s `cFS` case). -/
theorem cFS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cFS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { ({ s with fpCondFlag := false }) with
          pc := ({ s with fpCondFlag := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.un.s` sets `fpCondFlag := isNaN(float $fs) || isNaN(float $ft)`**
("unordered") — built from `Float32.isNaN` explicitly, *not* derived from
`<`/`<=` (those already return `false` for any NaN operand, which would
silently make a naive "unordered" formula wrong; `Instruction.cUnS`'s
docstring; `Step.lean`'s `cUnS` case). -/
theorem cUnS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cUnS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := floatOfBitsSpec (readFpReg s (regIdxSpec fs))
      let b := floatOfBitsSpec (readFpReg s (regIdxSpec ft))
      StepResult.next
        { ({ s with fpCondFlag := a.isNaN || b.isNaN }) with
          pc := ({ s with fpCondFlag := a.isNaN || b.isNaN }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.ueq.s` sets `fpCondFlag := ($fs == $ft) || isNaN($fs) || isNaN($ft)`**
("equal-or-unordered"; INSTRUCTION-REF "c.ueq.s" section; `Step.lean`'s
`cUeqS` case). -/
theorem cUeqS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cUeqS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := floatOfBitsSpec (readFpReg s (regIdxSpec fs))
      let b := floatOfBitsSpec (readFpReg s (regIdxSpec ft))
      StepResult.next
        { ({ s with fpCondFlag := a.beq b || a.isNaN || b.isNaN }) with
          pc := ({ s with fpCondFlag := a.beq b || a.isNaN || b.isNaN }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.olt.s` sets `fpCondFlag := Float32.lt (float $fs) (float $ft)`**
("ordered-less-than") — numerically **identical** to `cLtS_spec_raw`'s
right-hand side under this model: `Float32.lt` already returns `false` for
any NaN operand, so it already computes exactly the ordered-less-than
predicate with no extra `isNaN` guard needed. `c.lt.s` (signaling) and
`c.olt.s` (quiet) differ on real hardware only in whether a quiet-NaN
operand raises an Invalid Operation exception; this model has no
FP-exception mechanism for either, so both constructors compute the same
`fpCondFlag` value (`Instruction.cOltS`'s docstring; `Step.lean`'s `cOltS`
case). -/
theorem cOltS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cOltS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).lt
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.ult.s` sets `fpCondFlag := ($fs < $ft) || isNaN($fs) || isNaN($ft)`**
("less-than-or-unordered"), built from `Float32.isNaN` explicitly, same
rationale as `cUnS_spec_raw` (INSTRUCTION-REF "c.ult.s" section;
`Step.lean`'s `cUltS` case). -/
theorem cUltS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cUltS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := floatOfBitsSpec (readFpReg s (regIdxSpec fs))
      let b := floatOfBitsSpec (readFpReg s (regIdxSpec ft))
      StepResult.next
        { ({ s with fpCondFlag := a.lt b || a.isNaN || b.isNaN }) with
          pc := ({ s with fpCondFlag := a.lt b || a.isNaN || b.isNaN }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.ole.s` sets `fpCondFlag := Float32.le (float $fs) (float $ft)`**
("ordered-less-or-equal") — numerically **identical** to `cLeS_spec_raw`'s
right-hand side under this model, same `c.le.s`/`c.ole.s`
signaling-vs-quiet relationship as `cLtS_spec_raw`/`cOltS_spec_raw` above
(`Instruction.cOleS`'s docstring; `Step.lean`'s `cOleS` case). -/
theorem cOleS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cOleS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).le
        (floatOfBitsSpec (readFpReg s (regIdxSpec ft)))
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.ule.s` sets `fpCondFlag := ($fs <= $ft) || isNaN($fs) || isNaN($ft)`**
("less-or-equal-or-unordered"), built from `Float32.isNaN` explicitly, same
rationale as `cUnS_spec_raw` (INSTRUCTION-REF "c.ule.s" section;
`Step.lean`'s `cUleS` case). -/
theorem cUleS_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cUleS fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := floatOfBitsSpec (readFpReg s (regIdxSpec fs))
      let b := floatOfBitsSpec (readFpReg s (regIdxSpec ft))
      StepResult.next
        { ({ s with fpCondFlag := a.le b || a.isNaN || b.isNaN }) with
          pc := ({ s with fpCondFlag := a.le b || a.isNaN || b.isNaN }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `c.f.s`: always `false`, even for equal non-NaN operands.
#guard (match step (prog1Spec (.cFS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
-- `c.un.s`: true iff either operand is a NaN (`0x7fc00000` is a quiet NaN).
#guard (match step (prog1Spec (.cUnS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x7fc00000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUnS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
-- `c.ueq.s`: equal, or unordered.
#guard (match step (prog1Spec (.cUeqS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUeqS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x7fc00000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUeqS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x40000000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
-- `c.olt.s`: ordered and less-than; `false` (not `true`) when either
-- operand is NaN, unlike a plain `<` applied carelessly to the "unordered"
-- case.
#guard (match step (prog1Spec (.cOltS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x40000000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cOltS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x7fc00000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
-- `c.ult.s`: less-than, or unordered.
#guard (match step (prog1Spec (.cUltS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x7fc00000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUltS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x40000000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
-- `c.ole.s`: ordered and less-or-equal.
#guard (match step (prog1Spec (.cOleS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x3f800000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cOleS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x7fc00000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
-- `c.ule.s`: less-or-equal, or unordered.
#guard (match step (prog1Spec (.cUleS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x7fc00000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUleS 8#32 9#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x40000000#32) 9 0x3f800000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true

/-! ## Group 6 — closing `step_preserves_zero_register`

The STALL NOTE on `step_preserves_zero_register` (Group 1) predates almost
all of the `_spec_raw` theorems above: at the time it was written, only a
handful of instructions had one. Now nearly every instruction family does,
so the generic "expose the inner match/if uniformly" obstacle described
there can be sidestepped entirely: instead of unfolding `step`'s raw
definition generically, dispatch on the decoded instruction and, in each
case, `rw` with that instruction's own `_spec_raw` theorem (which has
already done the `step`-unfolding work), then close with
`writeReg_preserves_zero_slot` (for the register-writing cases) or a direct
`rfl`/regs-equality argument (for the cases that only touch `pc`,
`pendingBranch`, `hi`, `lo`, `mem`, or `out`).

Two small helpers make the memory-store cases (`sw`/`sh`/`sc`) as uniform
as the register-writing cases: `writeMemWord`/`writeMemHalf` are public (see
`State.lean`), so — unlike `step`'s private helpers — they can be `unfold`ed
here directly, giving a `regs`-equality fact out of their `Option.some`
case exactly the way `writeReg_pc`/`writeReg_hi`/etc. do for `writeReg`. -/

/-- Two states with the same `regs` field read `$zero` the same —
the register-file-only half of `readReg`, used to discharge every
`step_preserves_zero_register_nontrivial` case that changes `pc`/
`pendingBranch`/`hi`/`lo`/`mem`/`out` but never touches `regs` at all. -/
theorem readReg_zero_of_regs_eq {s1 s2 : State} (h : s1.regs = s2.regs) :
    readReg s1 0 = readReg s2 0 := by
  unfold readReg
  rw [h]

/-- `writeMemWord` never changes `regs` when it succeeds — it only ever
touches `mem` (INSTRUCTION-REF "sw"/"sc" sections' effective-address write).
Public (`State.lean`), so — unlike `step`'s private per-instruction helpers —
it can be `unfold`ed directly from this file. -/
theorem writeMemWord_regs (s stored : State) (addr v : W32)
    (h : writeMemWord s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemWord at h
  split at h
  · cases h
  · injection h with h'
    rw [← h']

/-- `writeMemHalf` never changes `regs` when it succeeds — the halfword
counterpart of `writeMemWord_regs` (INSTRUCTION-REF "sh" section). -/
theorem writeMemHalf_regs (s stored : State) (addr v : W32)
    (h : writeMemHalf s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemHalf at h
  split at h
  · cases h
  · injection h with h'
    rw [← h']

/-- `writeMemByte` never changes `regs` — the byte-write counterpart of
`writeMemWord_regs`/`writeMemHalf_regs`, completing the trio. Unlike
`writeMemWord`/`writeMemHalf` it has no alignment check at all
(`writeMemByte`'s own docstring: "always succeeds"), so this is even
simpler to prove: no `split`, just unfold-and-read-off the `{ s with
mem := ... }` field. (The `swl`/`swr` cases of
`step_preserves_zero_register_nontrivial` below end up not needing this
lemma by name — `writeMemByte`'s unconditional-`some` shape lets their
chained calls reduce by `rfl` directly — but the fact is recorded here
for the same reason `writeMemWord_regs`/`writeMemHalf_regs` are: it is the
honest, general statement of what `writeMemByte` does and does not touch.) -/
theorem writeMemByte_regs (s stored : State) (addr : W32) (v : UInt8)
    (h : writeMemByte s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemByte at h
  injection h with h'
  rw [← h']

/-- Single-instruction restatement of `lb_lbu_spec_raw`'s first conjunct,
for `lb` alone — proved the same way (`obtain`/`subst`/`unfold step`/`rw`/
`rfl`), since the combined theorem's bundled `wb`/`wbu` signature cannot be
applied to a `cases instr` branch that only knows about one of the two
instructions. -/
theorem lb_spec_raw' (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lb rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => StepResult.halt (.addressError addr)
      | some b =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) ((BitVec.ofNat 8 b.toNat).signExtend 32)) with
            pc := (writeReg s (regIdxSpec rt) ((BitVec.ofNat 8 b.toNat).signExtend 32)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Single-instruction restatement of `lb_lbu_spec_raw`'s second conjunct,
for `lbu` alone. -/
theorem lbu_spec_raw' (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lbu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemByte s addr with
      | none => StepResult.halt (.addressError addr)
      | some b =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) (BitVec.ofNat 32 b.toNat)) with
            pc := (writeReg s (regIdxSpec rt) (BitVec.ofNat 32 b.toNat)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Single-instruction restatement of `lh_lhu_spec_raw`'s first conjunct,
for `lh` alone. -/
theorem lh_spec_raw' (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lh rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemHalf s addr with
      | none => StepResult.halt (.addressError addr)
      | some h =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) (signExt16 h)) with
            pc := (writeReg s (regIdxSpec rt) (signExt16 h)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Single-instruction restatement of `lh_lhu_spec_raw`'s second conjunct,
for `lhu` alone. -/
theorem lhu_spec_raw' (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lhu rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemHalf s addr with
      | none => StepResult.halt (.addressError addr)
      | some h =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) h) with
            pc := (writeReg s (regIdxSpec rt) h).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **Closed weaker version of `step_preserves_zero_register`, for every
instruction family that has a `_spec_raw` theorem above.** Dispatches on
the decoded instruction and, in each case, `rw`s with that instruction's own
`_spec_raw` equation (which already did the hard work of unfolding `step`),
then closes with `writeReg_preserves_zero_slot` (register-writing cases) or
a `regs`-untouched argument (every other case) — see the Group 6 docstring
above. This covers every instruction that `decode`/`encode` support
**except**: `clo clz mul seb seh wsbh ext ins` (SPECIAL2/SPECIAL3, no
`_spec_raw` yet), `lwl lwr swl swr` (unaligned load/store, no `_spec_raw`
yet), `teqi tnei tgei tgeiu tlti tltiu` (REGIMM trap-immediate family, no
`_spec_raw` yet), `syscall` (see the `syscall1_spec`/`syscall10_spec` STALL
NOTE above), `mfc0 mtc0 eret wait` (CP0, no `_spec_raw` yet), and the
entire COP1/FPU subset `mfc1 mtc1 lwc1 swc1 addS subS mulS divS movS cvtSW
cvtWS cEqS cLtS cLeS sqrtS absS negS roundWS truncWS ceilWS floorWS cFS
cUnS cUeqS cOltS cUltS cOleS cUleS cfc1 ctc1 bc1t bc1f` (no `_spec_raw`
yet). Every one of those writes only `fpRegs`/`cp0*`/`mem`/`pc` — never the
GPR file `regs` — so the invariant is expected to hold for them too; they
are left as this theorem's own trailing `sorry` (see the STALL NOTE right
after its proof) pending `_spec_raw` coverage for those families, rather
than re-deriving `step`'s raw definition for ~45 more instructions here by
hand. -/
theorem step_preserves_zero_register_nontrivial (p : Program) (s s' : State) (w : W32)
    (instr : Instruction)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some instr)
    (hpb : s.pendingBranch = none)
    (hstep : step p s = StepResult.next s') :
    readReg s' 0 = readReg s 0 := by
  cases instr
  case add rs rt rd =>
    rw [add_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case sub rs rt rd =>
    rw [sub_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case addi rs rt imm =>
    rw [addi_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case addu rs rt rd =>
    rw [addu_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case subu rs rt rd =>
    rw [subu_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case and rs rt rd =>
    rw [and_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case or rs rt rd =>
    rw [or_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case xor rs rt rd =>
    rw [xor_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case nor rs rt rd =>
    rw [nor_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case slt rs rt rd =>
    rw [slt_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case sltu rs rt rd =>
    rw [sltu_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case movn rs rt rd =>
    rw [movn_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
    · injection hstep with hs; rw [← hs]; rfl
  case movz rs rt rd =>
    rw [movz_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
    · injection hstep with hs; rw [← hs]; rfl
  case sll rd rt shamt =>
    rw [sll_spec_raw p s w rd rt shamt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case srl rd rt shamt =>
    rw [srl_spec_raw p s w rd rt shamt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case sra rd rt shamt =>
    rw [sra_spec_raw p s w rd rt shamt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case sllv rd rt rs =>
    rw [sllv_spec_raw p s w rd rt rs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case srlv rd rt rs =>
    rw [srlv_spec_raw p s w rd rt rs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case srav rd rt rs =>
    rw [srav_spec_raw p s w rd rt rs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case rotr rd rt sa =>
    rw [rotr_spec_raw p s w rd rt sa hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case rotrv rd rt rs =>
    rw [rotrv_spec_raw p s w rd rt rs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case mult rs rt =>
    rw [mult_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case multu rs rt =>
    rw [multu_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case div rs rt =>
    rw [div_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case divu rs rt =>
    rw [divu_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case mflo rd =>
    rw [mflo_spec_raw p s w rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case mfhi rd =>
    rw [mfhi_spec_raw p s w rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case mthi rs =>
    rw [mthi_spec_raw p s w rs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case mtlo rs =>
    rw [mtlo_spec_raw p s w rs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case madd rs rt =>
    rw [madd_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case maddu rs rt =>
    rw [maddu_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case msub rs rt =>
    rw [msub_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case msubu rs rt =>
    rw [msubu_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case addiu rs rt imm =>
    rw [addiu_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case slti rs rt imm =>
    rw [slti_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case sltiu rs rt imm =>
    rw [sltiu_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case andi rs rt imm =>
    rw [andi_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case ori rs rt imm =>
    rw [ori_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case xori rs rt imm =>
    rw [xori_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case lui rt imm =>
    rw [lui_spec_raw p s w rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case lw rs rt imm =>
    rw [lw_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case lb rs rt imm =>
    rw [lb_spec_raw' p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case lbu rs rt imm =>
    rw [lbu_spec_raw' p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case lh rs rt imm =>
    rw [lh_spec_raw' p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case lhu rs rt imm =>
    rw [lhu_spec_raw' p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case ll rs rt imm =>
    rw [ll_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case sw rs rt imm =>
    rw [sw_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · rename_i stored hmw
      injection hstep with hs; rw [← hs]
      exact readReg_zero_of_regs_eq (writeMemWord_regs s stored _ _ hmw)
  case sh rs rt imm =>
    rw [sh_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · rename_i stored hmh
      injection hstep with hs; rw [← hs]
      exact readReg_zero_of_regs_eq (writeMemHalf_regs s stored _ _ hmh)
  case sc rs rt imm =>
    rw [sc_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · rename_i stored hmw
      split at hstep
      · injection hstep with hs; rw [← hs]
        exact (writeReg_preserves_zero_slot stored (regIdxSpec rt) 1#32).trans
          (readReg_zero_of_regs_eq (writeMemWord_regs s stored _ _ hmw))
      · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case blez rs imm =>
    rw [blez_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case bgtz rs imm =>
    rw [bgtz_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case j target =>
    rw [j_spec_raw p s w target hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case jr rs =>
    rw [jr_spec_raw p s w rs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case jalr rs rd =>
    rw [jalr_spec_raw p s w rs rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case jal target =>
    rw [jal_spec_raw p s w target hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s 31 _
  case bltz rs imm =>
    rw [bltz_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case bgez rs imm =>
    rw [bgez_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case bltzal rs imm =>
    rw [bltzal_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s 31 _)
  case bgezal rs imm =>
    rw [bgezal_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s 31 _)
  case «break» =>
    rw [break_spec_raw p s w hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case teq rs rt =>
    rw [teq_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tne rs rt =>
    rw [tne_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tlt rs rt =>
    rw [tlt_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tge rs rt =>
    rw [tge_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tltu rs rt =>
    rw [tltu_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tgeu rs rt =>
    rw [tgeu_spec_raw p s w rs rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case clo rs rd =>
    rw [clo_spec_raw p s w rs rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case clz rs rd =>
    rw [clz_spec_raw p s w rs rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case mul rs rt rd =>
    rw [mul_spec_raw p s w rs rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case seb rd rt =>
    rw [seb_spec_raw p s w rd rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case seh rd rt =>
    rw [seh_spec_raw p s w rd rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case wsbh rd rt =>
    rw [wsbh_spec_raw p s w rd rt hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case ext rt rs pos size =>
    rw [ext_spec_raw p s w rt rs pos size hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case ins rt rs pos size =>
    rw [ins_spec_raw p s w rt rs pos size hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case teqi rs imm =>
    rw [teqi_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tnei rs imm =>
    rw [tnei_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tgei rs imm =>
    rw [tgei_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tgeiu rs imm =>
    rw [tgeiu_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tlti rs imm =>
    rw [tlti_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case tltiu rs imm =>
    rw [tltiu_spec_raw p s w rs imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case mfc1 rt fs =>
    rw [mfc1_spec_raw p s w rt fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case mtc1 rt fs =>
    rw [mtc1_spec_raw p s w rt fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case lwc1 rs ft imm =>
    rw [lwc1_spec_raw p s w rs ft imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · injection hstep with hs; rw [← hs]; rfl
  case swc1 rs ft imm =>
    rw [swc1_spec_raw p s w rs ft imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · cases hstep
    · rename_i stored hmw
      injection hstep with hs; rw [← hs]
      exact readReg_zero_of_regs_eq (writeMemWord_regs s stored _ _ hmw)
  case addS fd fs ft =>
    rw [addS_spec_raw p s w fd fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case subS fd fs ft =>
    rw [subS_spec_raw p s w fd fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case mulS fd fs ft =>
    rw [mulS_spec_raw p s w fd fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case divS fd fs ft =>
    rw [divS_spec_raw p s w fd fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case movS fd fs =>
    rw [movS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cvtSW fd fs =>
    rw [cvtSW_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cvtWS fd fs =>
    rw [cvtWS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case sqrtS fd fs =>
    rw [sqrtS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case absS fd fs =>
    rw [absS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case negS fd fs =>
    rw [negS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case roundWS fd fs =>
    rw [roundWS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case truncWS fd fs =>
    rw [truncWS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case ceilWS fd fs =>
    rw [ceilWS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case floorWS fd fs =>
    rw [floorWS_spec_raw p s w fd fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cEqS fs ft =>
    rw [cEqS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cLtS fs ft =>
    rw [cLtS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cLeS fs ft =>
    rw [cLeS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cFS fs ft =>
    rw [cFS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cUnS fs ft =>
    rw [cUnS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cUeqS fs ft =>
    rw [cUeqS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cOltS fs ft =>
    rw [cOltS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cUltS fs ft =>
    rw [cUltS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cOleS fs ft =>
    rw [cOleS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cUleS fs ft =>
    rw [cUleS_spec_raw p s w fs ft hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case cfc1 rt fs =>
    rw [cfc1_spec_raw p s w rt fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
  case ctc1 rt fs =>
    rw [ctc1_spec_raw p s w rt fs hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case eret =>
    rw [eret_spec_raw p s w hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case wait =>
    rw [wait_spec_raw p s w hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    injection hstep with hs; rw [← hs]; rfl
  case lwl rs rt imm =>
    rw [lwl_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;>
      (injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _)
  case lwr rs rt imm =>
    rw [lwr_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;>
      (injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _)
  case swl rs rt imm =>
    rw [swl_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case swr rs rt imm =>
    rw [swr_spec_raw p s w rs rt imm hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep <;> (injection hstep with hs; rw [← hs]; rfl)
  case mfc0 rt rd =>
    rw [mfc0_spec_raw p s w rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
    · injection hstep with hs; rw [← hs]; exact writeReg_preserves_zero_slot s _ _
    · cases hstep
  case mtc0 rt rd =>
    rw [mtc0_spec_raw p s w rt rd hfetch hdecode hpb] at hstep
    try dsimp only at hstep
    split at hstep
    · injection hstep with hs; rw [← hs]; rfl
    · injection hstep with hs; rw [← hs]; rfl
    · injection hstep with hs; rw [← hs]; rfl
    · cases hstep
  all_goals sorry

/-! STALL NOTE on `step_preserves_zero_register_nontrivial`'s remaining
`all_goals sorry` (updated after the proof-zero-reg-splits pass that closed
the `lwl`/`lwr`/`swl`/`swr`/`mfc0`/`mtc0` cases): most of the instruction
families earlier versions of this note listed now have `_spec_raw`
theorems and have been added as `case` branches above (`clo clz mul seb
seh wsbh ext ins`, `teqi tnei tgei tgeiu tlti tltiu`, `mfc1 mtc1 lwc1 swc1
addS subS mulS divS movS cvtSW cvtWS sqrtS absS negS roundWS truncWS
ceilWS floorWS` and all ten compare predicates `cEqS cLtS cLeS cFS cUnS
cUeqS cOltS cUltS cOleS cUleS`, `cfc1 ctc1`, `eret`/`wait`, and now also
`lwl lwr swl swr mfc0 mtc0`: each one's `_spec_raw` right-hand side is a
multi-branch `match` (on the unaligned byte offset `0..3`, or on the CP0
register-select field `12/13/14/_`) rather than the single-`rfl`/
`writeReg_preserves_zero_slot` shape most other cases reduce with, but
`split at hstep` handles all four arms uniformly for `lwl`/`lwr` (every
arm only ever calls `writeReg`, so `<;> writeReg_preserves_zero_slot`
closes all of them at once) and for `swl`/`swr` (every arm only ever
chains `writeMemByte` calls, which are unconditional `some`s — no
alignment check, unlike `writeMemWord`/`writeMemHalf` — so each arm's
final state is `regs`-identical to `s` by `rfl`, no lemma needed); `mfc0`/
`mtc0` needed one bullet per arm instead of `<;>` (three `writeReg_
preserves_zero_slot`/`rfl` arms plus one `illegalInstruction`-halt arm
that contradicts `hstep : _ = StepResult.next s'` via `cases hstep`), since
their match scrutinee is `rd.toNat` rather than a plain `off`.

What's left open by the `cases instr` dispatch above is now just three
genuinely harder-to-close instructions:
- `syscall` — see the dedicated STALL NOTE below (`syscall1_spec`/
  `syscall10_spec`): genuinely blocked on the same private-`execInstr`-
  dispatch chicken-and-egg issue, not just unattempted.
- `bc1t`/`bc1f` (FP-conditional branch) have no `_spec_raw` theorem at all
  yet — real net-new specification work, not a stall.

Left `sorry` here for these three remaining instructions rather than
re-derive `syscall`'s private dispatch or write two new branch-instruction
specs in what is meant to be a closing/consolidation pass. -/

/-! ## Group N — Double-precision (`.d`) FPU instructions

This wave's new-content section (proof-fpu-double track): the double-
precision FPU instructions that landed with zero proof coverage —
`ldc1`/`sdc1` (doubleword load/store), `add.d`/`sub.d`/`mul.d`/`div.d`/
`mov.d`, `cvt.d.s`/`cvt.s.d`/`cvt.d.w`/`cvt.w.d`, `sqrt.d`/`abs.d`/`neg.d`,
and all ten `c.cond.d` compare predicates. Every one of these mirrors an
already-proven single-precision theorem above (`addS_spec_raw`/`cEqS_spec_
raw`/etc.), operating on a 64-bit `Float` composed from a register *pair*
instead of a single 32-bit `Float32` register (`Step.lean`'s module
docstring; `doubleOfRegPair`/`regPairOfDouble` below the single-precision
helpers).

`doubleOfRegPair`/`regPairOfDouble` are already **public** in `Step.lean`
(unlike `floatOfBits`/`bitsOfFloat`, which are `private`), so they are used
directly here with no mirror needed. `Step.lean`'s `readDoubleReg`/
`writeDoubleReg`/`doubleOfIntBits`/`intBitsOfDoubleTrunc` *are* `private`,
so — exactly like `floatOfBitsSpec`/`bitsOfFloatSpec` mirror `floatOfBits`/
`bitsOfFloat` — the four mirrors below reproduce them byte-for-byte using
only public names. -/

/-- Mirrors `Step.lean`'s private `readDoubleReg`: reads the double-
precision `Float` held in the FPR register pair named by `f` (the raw
5-bit field of the pair's *low* register, e.g. `fs`/`ft`/`fd` as decoded)
in `s`'s `fpRegs`, composing via the public `doubleOfRegPair`. -/
def readDoubleRegSpec (s : State) (f : W32) : Float :=
  doubleOfRegPair (readFpReg s (regIdxSpec f)) (readFpReg s (regIdxSpec (f + 1#32)))

/-- Mirrors `Step.lean`'s private `writeDoubleReg`: writes double-precision
`Float` value `v` into the FPR register pair named by `f` (the low
register) in `s`, decomposing via the public `regPairOfDouble`. -/
def writeDoubleRegSpec (s : State) (f : W32) (v : Float) : State :=
  let (lo, hi) := regPairOfDouble v
  writeFpReg (writeFpReg s (regIdxSpec f) lo) (regIdxSpec (f + 1#32)) hi

/-- Mirrors `Step.lean`'s private `doubleOfIntBits`: `cvt.d.w`'s numeric
conversion, reading `w`'s bit pattern as a 32-bit two's-complement int
(`Int32.ofBitVec`) and converting that integer *value* to the nearest
`Float` (`Int32.toFloat`, exact for every `Int32`). -/
def doubleOfIntBitsSpec (w : W32) : Float := (Int32.ofBitVec w).toFloat

/-- Mirrors `Step.lean`'s private `intBitsOfDoubleTrunc`: `cvt.w.d`'s
numeric conversion, truncating `f` toward zero to a 32-bit two's-complement
int (`Float.toInt32`, which clamps on overflow and maps `NaN` to `0`),
returned as a raw bit pattern. -/
def intBitsOfDoubleTruncSpec (f : Float) : W32 := f.toInt32.toBitVec

/-- **`mov.d` copies `$fs`'s register pair (both 32-bit halves) into `$fd`'s
pair, with no `Float` arithmetic at all** — the double-precision analogue of
`movS_spec_raw`, but two `readFpReg`/`writeFpReg` calls instead of one
(INSTRUCTION-REF "mov.d" section; `Step.lean`'s `movD` case). -/
theorem movD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.movD fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let s' := writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs))
      StepResult.next
        { (writeFpReg s' (regIdxSpec (fd + 1#32)) (readFpReg s (regIdxSpec (fs + 1#32)))) with
          pc := (writeFpReg s' (regIdxSpec (fd + 1#32)) (readFpReg s (regIdxSpec (fs + 1#32)))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `mov.d`: `3.0` (lo `0`, hi `0x40080000`) copies through unchanged.
#guard (match step (prog1Spec (.movD 10#32 8#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0#32) 9 0x40080000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0#32 && s.fpRegs.getD 11 0#32 == 0x40080000#32
        | .halt _ => false) = true

/-- **`add.d` writes `$fd := Float.add (double $fs) (double $ft)`**, the
double-precision analogue of `addS_spec_raw`: both operands and the result
are read/written as register-pair-composed 64-bit `Float`s via
`readDoubleRegSpec`/`writeDoubleRegSpec` instead of `floatOfBitsSpec`/
`bitsOfFloatSpec` (INSTRUCTION-REF "add.d" section; `Step.lean`'s `addD`
case). -/
theorem addD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addD fd fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (readDoubleRegSpec s fs).add (readDoubleRegSpec s ft)
      StepResult.next
        { (writeDoubleRegSpec s fd v) with
          pc := (writeDoubleRegSpec s fd v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sub.d` writes `$fd := Float.sub (double $fs) (double $ft)`**, same
shape as `addD_spec_raw` with `Float.sub` (INSTRUCTION-REF "sub.d" section;
`Step.lean`'s `subD` case). -/
theorem subD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.subD fd fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (readDoubleRegSpec s fs).sub (readDoubleRegSpec s ft)
      StepResult.next
        { (writeDoubleRegSpec s fd v) with
          pc := (writeDoubleRegSpec s fd v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`mul.d` writes `$fd := Float.mul (double $fs) (double $ft)`**, same
shape as `addD_spec_raw` with `Float.mul` (INSTRUCTION-REF "mul.d" section;
`Step.lean`'s `mulD` case). -/
theorem mulD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mulD fd fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (readDoubleRegSpec s fs).mul (readDoubleRegSpec s ft)
      StepResult.next
        { (writeDoubleRegSpec s fd v) with
          pc := (writeDoubleRegSpec s fd v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`div.d` writes `$fd := Float.div (double $fs) (double $ft)`** —
IEEE-754 division; `$ft == 0` yields ±Infinity/NaN, never a trap (module
docstring; SPEC-NOTES §9 item 2 precedent), same shape as `addD_spec_raw`
with `Float.div` (INSTRUCTION-REF "div.d" section; `Step.lean`'s `divD`
case). -/
theorem divD_spec_raw (p : Program) (s : State) (w fd fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.divD fd fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (readDoubleRegSpec s fs).div (readDoubleRegSpec s ft)
      StepResult.next
        { (writeDoubleRegSpec s fd v) with
          pc := (writeDoubleRegSpec s fd v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `add.d`: `1.0 + 2.0 = 3.0`; `sub.d`: `5.0 - 2.0 = 3.0`; `mul.d`:
-- `2.0 * 3.0 = 6.0`; `div.d`: `6.0 / 2.0 = 3.0`, and `div.d` by zero gives
-- `+Infinity`, not a trap (same bit patterns as `Step.lean`'s own
-- double-precision test block).
#guard (match step (prog1Spec (.addD 10#32 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x3ff00000#32) 6 0#32) 7 0x40000000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x40080000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.subD 10#32 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x40140000#32) 6 0#32) 7 0x40000000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x40080000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.mulD 10#32 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x40000000#32) 6 0#32) 7 0x40080000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x40180000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.divD 10#32 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x40180000#32) 6 0#32) 7 0x40000000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x40080000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.divD 10#32 8#32 6#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0#32) 9 0x3ff00000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x7ff00000#32
        | .halt _ => false) = true

/-- **`ldc1` loads the 64-bit doubleword at `$rs + sext16(offset)` into FPR
pair `$ft`/`$ft+1`** — two `readMemWord` calls, big-endian doubleword order
matching the project's big-endian word order: the word at the lower address
(`addr`) is the *more*-significant half, written to the **high** register
(`$ft+1`); `addr + 4` is the **low** register (`$ft`) (INSTRUCTION-REF
"ldc1" section; `Step.lean`'s `ldc1` case). Halts with `addressError` if
*either* half's address is misaligned, like `lwc1`/`lw`. -/
theorem ldc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ldc1 rs ft imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr, readMemWord s (addr + 4#32) with
      | some hi, some lo =>
        let s' := writeFpReg s (regIdxSpec ft) lo
        StepResult.next
          { (writeFpReg s' (regIdxSpec (ft + 1#32)) hi) with
            pc := (writeFpReg s' (regIdxSpec (ft + 1#32)) hi).pc + 4#32 }
      | _, _ => StepResult.halt (.addressError addr) := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`sdc1` stores FPR pair `$ft`/`$ft+1`'s doubleword to `$rs +
sext16(offset)` and clears `llBit`** — the **high** register (`$ft+1`)
goes to the lower address (`addr`), the **low** register (`$ft`) goes to
`addr + 4`, the inverse of `ldc1_spec_raw`; two `writeMemWord` calls
(INSTRUCTION-REF "sdc1" section; `Step.lean`'s `sdc1` case). Halts with
`addressError` if *either* half's address is misaligned, like
`swc1`/`sw`. -/
theorem sdc1_spec_raw (p : Program) (s : State) (w rs ft imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sdc1 rs ft imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      let lo := readFpReg s (regIdxSpec ft)
      let hi := readFpReg s (regIdxSpec (ft + 1#32))
      match writeMemWord s addr hi with
      | none => StepResult.halt (.addressError addr)
      | some s' =>
        match writeMemWord s' (addr + 4#32) lo with
        | none => StepResult.halt (.addressError addr)
        | some s'' =>
          StepResult.next
            { ({ s'' with llBit := false }) with
              pc := ({ s'' with llBit := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `ldc1`/`sdc1`: same memory layout `Step.lean`'s own test block uses —
-- double `1.0` = (lo `0x00000000`, hi `0x3ff00000`), big-endian doubleword
-- (high half at the lower address).
#guard (match step (prog1Spec (.ldc1 8#32 9#32 4#32))
          { (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
            mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010004#32 0x3f).insert 0x10010005#32 0xf0)
                     |>.insert 0x10010006#32 0x00 |>.insert 0x10010007#32 0x00 } with
        | .next s => s.fpRegs.getD 9 0#32 == 0x00000000#32 && s.fpRegs.getD 10 0#32 == 0x3ff00000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.sdc1 8#32 9#32 4#32))
          (writeFpReg (writeFpReg (setRegsSpec (initialState textBase) [(8, 0x10010000#32)])
            9 0x00000000#32) 10 0x3ff00000#32) with
        | .next s => readMemWord s 0x10010004#32 == some 0x3ff00000#32 &&
            readMemWord s 0x10010008#32 == some 0x00000000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.ldc1 8#32 9#32 1#32)) (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next _ => false
        | .halt r => r == .addressError 0x10010001#32) = true

/-- **`c.eq.d` sets `fpCondFlag := Float.beq (double $fs) (double $ft)`**,
IEEE-754 double-precision equality — the double-precision analogue of
`cEqS_spec_raw` (INSTRUCTION-REF "c.eq.d" section; `Step.lean`'s `cEqD`
case). -/
theorem cEqD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cEqD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (readDoubleRegSpec s fs).beq (readDoubleRegSpec s ft)
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.lt.d` sets `fpCondFlag := Float.lt (double $fs) (double $ft)`**
(INSTRUCTION-REF "c.lt.d" section; `Step.lean`'s `cLtD` case). Same modeled
result as `cOltD_spec_raw` below, same `c.lt.s`/`c.olt.s` signaling-vs-quiet
relationship as the single-precision family. -/
theorem cLtD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cLtD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (readDoubleRegSpec s fs).lt (readDoubleRegSpec s ft)
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.le.d` sets `fpCondFlag := Float.le (double $fs) (double $ft)`**
(INSTRUCTION-REF "c.le.d" section; `Step.lean`'s `cLeD` case). Same modeled
result as `cOleD_spec_raw` below. -/
theorem cLeD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cLeD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (readDoubleRegSpec s fs).le (readDoubleRegSpec s ft)
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.f.d` sets `fpCondFlag := false` unconditionally**, ignoring both
operands entirely — real MIPS32's "always false" predicate placeholder,
same as `cFS_spec_raw` (INSTRUCTION-REF "c.f.d" section; `Step.lean`'s
`cFD` case). -/
theorem cFD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cFD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { ({ s with fpCondFlag := false }) with
          pc := ({ s with fpCondFlag := false }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.un.d` sets `fpCondFlag := isNaN(double $fs) || isNaN(double $ft)`**
("unordered") — built from `Float.isNaN` explicitly, same rationale as
`cUnS_spec_raw` (INSTRUCTION-REF "c.un.d" section; `Step.lean`'s `cUnD`
case). -/
theorem cUnD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cUnD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := readDoubleRegSpec s fs
      let b := readDoubleRegSpec s ft
      StepResult.next
        { ({ s with fpCondFlag := a.isNaN || b.isNaN }) with
          pc := ({ s with fpCondFlag := a.isNaN || b.isNaN }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.ueq.d` sets `fpCondFlag := ($fs == $ft) || isNaN($fs) || isNaN($ft)`**
("equal-or-unordered"; INSTRUCTION-REF "c.ueq.d" section; `Step.lean`'s
`cUeqD` case). -/
theorem cUeqD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cUeqD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := readDoubleRegSpec s fs
      let b := readDoubleRegSpec s ft
      StepResult.next
        { ({ s with fpCondFlag := a.beq b || a.isNaN || b.isNaN }) with
          pc := ({ s with fpCondFlag := a.beq b || a.isNaN || b.isNaN }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.olt.d` sets `fpCondFlag := Float.lt (double $fs) (double $ft)`**
("ordered-less-than") — numerically **identical** to `cLtD_spec_raw`'s
right-hand side under this model, same `c.lt.d`/`c.olt.d`
signaling-vs-quiet relationship as `cLtS_spec_raw`/`cOltS_spec_raw`
(INSTRUCTION-REF "c.olt.d" section; `Step.lean`'s `cOltD` case). -/
theorem cOltD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cOltD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (readDoubleRegSpec s fs).lt (readDoubleRegSpec s ft)
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.ult.d` sets `fpCondFlag := ($fs < $ft) || isNaN($fs) || isNaN($ft)`**
("less-than-or-unordered"), built from `Float.isNaN` explicitly, same
rationale as `cUnD_spec_raw` (INSTRUCTION-REF "c.ult.d" section;
`Step.lean`'s `cUltD` case). -/
theorem cUltD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cUltD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := readDoubleRegSpec s fs
      let b := readDoubleRegSpec s ft
      StepResult.next
        { ({ s with fpCondFlag := a.lt b || a.isNaN || b.isNaN }) with
          pc := ({ s with fpCondFlag := a.lt b || a.isNaN || b.isNaN }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.ole.d` sets `fpCondFlag := Float.le (double $fs) (double $ft)`**
("ordered-less-or-equal") — numerically **identical** to `cLeD_spec_raw`'s
right-hand side under this model, same `c.le.d`/`c.ole.d`
signaling-vs-quiet relationship as `cLeS_spec_raw`/`cOleS_spec_raw`
(INSTRUCTION-REF "c.ole.d" section; `Step.lean`'s `cOleD` case). -/
theorem cOleD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cOleD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let flag := (readDoubleRegSpec s fs).le (readDoubleRegSpec s ft)
      StepResult.next
        { ({ s with fpCondFlag := flag }) with
          pc := ({ s with fpCondFlag := flag }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`c.ule.d` sets `fpCondFlag := ($fs <= $ft) || isNaN($fs) || isNaN($ft)`**
("less-or-equal-or-unordered"), built from `Float.isNaN` explicitly, same
rationale as `cUnD_spec_raw` (INSTRUCTION-REF "c.ule.d" section;
`Step.lean`'s `cUleD` case). -/
theorem cUleD_spec_raw (p : Program) (s : State) (w fs ft : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cUleD fs ft))
    (hpb : s.pendingBranch = none) :
    step p s =
      let a := readDoubleRegSpec s fs
      let b := readDoubleRegSpec s ft
      StepResult.next
        { ({ s with fpCondFlag := a.le b || a.isNaN || b.isNaN }) with
          pc := ({ s with fpCondFlag := a.le b || a.isNaN || b.isNaN }).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- All ten `c.cond.d` predicates, same bit patterns as `Step.lean`'s own
-- double-precision compare test block (quiet double NaN = lo `0`, hi
-- `0x7ff80000`).
#guard (match step (prog1Spec (.cEqD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x3ff00000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cEqD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x3ff00000#32) 6 0#32) 7 0x40000000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cLtD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x3ff00000#32) 6 0#32) 7 0x40000000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cLeD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x3ff00000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cFD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x3ff00000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUnD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x7ff80000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUeqD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x7ff80000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cOltD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x7ff80000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUltD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x7ff80000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cOleD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x3ff00000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cUleD 8#32 6#32))
          (writeFpReg (writeFpReg (writeFpReg (writeFpReg (initialState textBase)
            8 0#32) 9 0x7ff80000#32) 6 0#32) 7 0x3ff00000#32) with
        | .next s => s.fpCondFlag == true
        | .halt _ => false) = true

/-- **`sqrt.d` writes `$fd := Float.sqrt (double $fs)`** — correctly-rounded
IEEE-754 double-precision square root, the double-precision analogue of
`sqrtS_spec_raw` (INSTRUCTION-REF "sqrt.d" section; `Step.lean`'s `sqrtD`
case). -/
theorem sqrtD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sqrtD fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let v := (readDoubleRegSpec s fs).sqrt
      StepResult.next
        { (writeDoubleRegSpec s fd v) with
          pc := (writeDoubleRegSpec s fd v).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`abs.d` clears `$fs`'s sign bit into `$fd`, operating on the **high**
half only** — a double's sign bit is bit 63 of the 64-bit value, i.e. bit
31 of the high register; the low register is copied unchanged, no `Float`
arithmetic involved (`Instruction.absD`'s docstring; `Step.lean`'s `absD`
case) — exact for every bit pattern, including NaN payloads, same as
`absS_spec_raw`. -/
theorem absD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.absD fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let s' := writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs))
      StepResult.next
        { (writeFpReg s' (regIdxSpec (fd + 1#32)) (readFpReg s (regIdxSpec (fs + 1#32)) &&& 0x7fffffff#32)) with
          pc := (writeFpReg s' (regIdxSpec (fd + 1#32))
            (readFpReg s (regIdxSpec (fs + 1#32)) &&& 0x7fffffff#32)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`neg.d` flips `$fs`'s sign bit into `$fd`, operating on the **high**
half only** — same bit-position reasoning as `absD_spec_raw`, `^^^
0x80000000` instead of `&&& 0x7fffffff` (`Instruction.negD`'s docstring;
`Step.lean`'s `negD` case), same as `negS_spec_raw`. -/
theorem negD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.negD fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      let s' := writeFpReg s (regIdxSpec fd) (readFpReg s (regIdxSpec fs))
      StepResult.next
        { (writeFpReg s' (regIdxSpec (fd + 1#32)) (readFpReg s (regIdxSpec (fs + 1#32)) ^^^ 0x80000000#32)) with
          pc := (writeFpReg s' (regIdxSpec (fd + 1#32))
            (readFpReg s (regIdxSpec (fs + 1#32)) ^^^ 0x80000000#32)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `sqrt.d`: `4.0` -> `2.0`; `abs.d`: `-3.0` -> `3.0` (low half unchanged);
-- `neg.d`: `3.0` -> `-3.0`, `-3.0` -> `3.0` (same bit patterns as
-- `Step.lean`'s own test block).
#guard (match step (prog1Spec (.sqrtD 10#32 8#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0#32) 9 0x40100000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x40000000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.absD 10#32 8#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0#32) 9 0xc0080000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x40080000#32 && s.fpRegs.getD 10 0#32 == 0#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.negD 10#32 8#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0#32) 9 0x40080000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0xc0080000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.negD 10#32 8#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0#32) 9 0xc0080000#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x40080000#32
        | .halt _ => false) = true

/-- **`cvt.d.s` writes `$fd := double(float32 $fs)`** — single-to-double
numeric promotion via Lean core's `Float32.toFloat` (INSTRUCTION-REF
"cvt.d.s" section; `Step.lean`'s `cvtDS` case). -/
theorem cvtDS_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtDS fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeDoubleRegSpec s fd (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).toFloat) with
          pc := (writeDoubleRegSpec s fd (floatOfBitsSpec (readFpReg s (regIdxSpec fs))).toFloat).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`cvt.s.d` writes `$fd := float32(double $fs)`** — double-to-single
numeric demotion via Lean core's `Float.toFloat32` (INSTRUCTION-REF
"cvt.s.d" section; `Step.lean`'s `cvtSD` case). -/
theorem cvtSD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtSD fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec (readDoubleRegSpec s fs).toFloat32)) with
          pc := (writeFpReg s (regIdxSpec fd) (bitsOfFloatSpec (readDoubleRegSpec s fs).toFloat32)).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`cvt.d.w` writes `$fd := double(int32bits($fs))`** — numeric
conversion of `$fs`'s bit pattern read as a 32-bit two's-complement int,
*not* a raw bit-pattern copy, the double-precision analogue of
`cvtSW_spec_raw` (INSTRUCTION-REF "cvt.d.w" section; `Step.lean`'s `cvtDW`
case uses `doubleOfIntBits`/`doubleOfIntBitsSpec`). -/
theorem cvtDW_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtDW fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeDoubleRegSpec s fd (doubleOfIntBitsSpec (readFpReg s (regIdxSpec fs)))) with
          pc := (writeDoubleRegSpec s fd (doubleOfIntBitsSpec (readFpReg s (regIdxSpec fs)))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`cvt.w.d` writes `$fd := int32bits(trunc($fs))`**, truncating toward
zero — real MIPS32 rounds per the current FCSR rounding mode, but this
model always truncates (no `FCSR` in scope, same simplification as
`cvtWS_spec_raw`; `Step.lean`'s `cvtWD` case uses `intBitsOfDoubleTrunc`/
`intBitsOfDoubleTruncSpec`). -/
theorem cvtWD_spec_raw (p : Program) (s : State) (w fd fs : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.cvtWD fd fs))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeFpReg s (regIdxSpec fd) (intBitsOfDoubleTruncSpec (readDoubleRegSpec s fs))) with
          pc := (writeFpReg s (regIdxSpec fd) (intBitsOfDoubleTruncSpec (readDoubleRegSpec s fs))).pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

-- `cvt.d.s`: single `1.0` (`0x3f800000`) -> double `1.0` (lo `0`, hi
-- `0x3ff00000`); `cvt.s.d`: double `3.0` (lo `0`, hi `0x40080000`) ->
-- single `3.0` (`0x40400000`); `cvt.d.w`: `5` -> `5.0`, `-5`
-- (`0xfffffffb`) -> `-5.0`; `cvt.w.d`: `5.9` -> `5` (truncated, not
-- rounded), `-5.9` -> `-5` (same bit patterns as `Step.lean`'s own test
-- block).
#guard (match step (prog1Spec (.cvtDS 10#32 8#32)) (writeFpReg (initialState textBase) 8 0x3f800000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0#32 && s.fpRegs.getD 11 0#32 == 0x3ff00000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cvtSD 10#32 8#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0#32) 9 0x40080000#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x40400000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cvtDW 10#32 8#32)) (writeFpReg (initialState textBase) 8 5#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0x40140000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cvtDW 10#32 8#32)) (writeFpReg (initialState textBase) 8 0xfffffffb#32) with
        | .next s => s.fpRegs.getD 11 0#32 == 0xc0140000#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cvtWD 10#32 8#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x9999999a#32) 9 0x40179999#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0x00000005#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.cvtWD 10#32 8#32))
          (writeFpReg (writeFpReg (initialState textBase) 8 0x9999999a#32) 9 0xc0179999#32) with
        | .next s => s.fpRegs.getD 10 0#32 == 0xfffffffb#32
        | .halt _ => false) = true

/-! ## Group N+1 — `sync`/`synci` no-ops and `bc1t`/`bc1f` FP-conditional branch

Four previously-unproven instructions (`docs/spec/MIPS-COVERAGE-GAPS.md`
§3.7): `sync` and `synci` are documented no-ops (`Step.lean`'s docstrings
for each), proved by the same `mkNext s s`-closes-with-`rfl` recipe as
`wait_spec_raw` above; `bc1t`/`bc1f` are the FP-conditional pair, proved by
the same one-delay-slot `if`-shaped recipe as `beq_spec_raw`/`bltz_spec_raw`
above, reading `State.fpCondFlag` (set by the `c.eq.s`/`c.lt.s`/`c.le.s`/
… family) in place of a GPR comparison. -/

/-- **`sync` is a documented no-op**: this single-hart simulator models no
concurrency or out-of-order execution for a memory-ordering barrier to
order anything against, so `sync` just falls through to `pc + 4` like any
ordinary non-control-flow instruction, touching no other state
(`Step.lean`'s `sync` docstring: `mkNext s s`). -/
theorem sync_spec_raw (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .sync)
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`synci` is a documented no-op**: it computes the same effective
address as `lw`/`sw` (`readReg s rs + signExt16 offset`) for architectural
fidelity, but this simulator has no instruction-cache model to flush, so
the address is immediately discarded and `synci` falls through to `pc + 4`
touching no other state at all, not even a memory read (`Step.lean`'s
`synci` docstring). -/
theorem synci_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.synci rs imm))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bc1t`/`bc1f` branch target and condition**: real MIPS32 FP-conditional
branches, reading `State.fpCondFlag` (set by `c.eq.s`/`c.lt.s`/`c.le.s`/…)
in place of the GPR comparisons `beq`/`bltz` use, but scheduling the same
one-delay-slot `pendingBranch := some (PC_next + (offset << 2))` transfer
as every other branch in this file (`Step.lean`'s `bc1t`/`bc1f` docstring:
upgraded to this shared delay-slot discipline during dev/v2 integration).
`bc1t` branches when `fpCondFlag` is `true`; `bc1f` is its mirror image,
branching when `fpCondFlag` is `false`. Neither case ever jumps
immediately — the delay-slot instruction at `PC_next` always executes
first, exactly as for `beq_spec_raw`/`bltz_spec_raw`. -/
theorem bc1t_spec_raw (p : Program) (s : State) (w imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1t imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if s.fpCondFlag then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

theorem bc1f_spec_raw (p : Program) (s : State) (w imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1f imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if s.fpCondFlag then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bc1t`, taken**: when `fpCondFlag` is `true`, `bc1t` schedules
`PC_next + (offset << 2)` as the pending delay-slot transfer and itself
falls through to `PC_next`. -/
theorem bc1t_taken_spec (p : Program) (s : State) (w imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1t imm))
    (hpb : s.pendingBranch = none)
    (htaken : s.fpCondFlag = true) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bc1t_spec_raw p s w imm hfetch hdecode hpb, if_pos htaken]

/-- **`bc1t`, not taken**: when `fpCondFlag` is `false`, control simply
falls through to `PC_next`, exactly as an ordinary instruction. -/
theorem bc1t_not_taken_spec (p : Program) (s : State) (w imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1t imm))
    (hpb : s.pendingBranch = none)
    (hnot : s.fpCondFlag = false) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [bc1t_spec_raw p s w imm hfetch hdecode hpb, if_neg (by simp [hnot])]

/-- **`bc1f`, taken**: when `fpCondFlag` is `false`, `bc1f` schedules
`PC_next + (offset << 2)` as the pending delay-slot transfer — the mirror
image of `bc1t`. -/
theorem bc1f_taken_spec (p : Program) (s : State) (w imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1f imm))
    (hpb : s.pendingBranch = none)
    (htaken : s.fpCondFlag = false) :
    step p s = StepResult.next
      { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bc1f_spec_raw p s w imm hfetch hdecode hpb, if_neg (by simp [htaken])]

/-- **`bc1f`, not taken**: when `fpCondFlag` is `true`, control simply
falls through to `PC_next`. -/
theorem bc1f_not_taken_spec (p : Program) (s : State) (w imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bc1f imm))
    (hpb : s.pendingBranch = none)
    (hnot : s.fpCondFlag = true) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [bc1f_spec_raw p s w imm hfetch hdecode hpb, if_pos hnot]

/-! ## Group N — "branch likely" family (`beql bnel blezl bgtzl bltzl bgezl
bltzall bgezall`)

`docs/spec/INSTRUCTION-REF.md` "branch likely" section; `Semantics/
Step.lean`'s module docstring and its `.beql`..`.bgezall` `execInstr` cases.
These eight are architecturally different from every other branch/jump
documented above: a **taken** branch-likely schedules `pendingBranch`
exactly like its non-likely counterpart (the delay slot executes
normally), but a **not-taken** branch-likely does *not* fall through the
ordinary way — it sets `State.squashNext := true` and leaves `pc` at
`PC_next` (the delay-slot instruction's own address), rather than ever
reading `s.pendingBranch`/calling `advance`. The theorems below are the
same `_spec_raw` recipe as `beq_spec_raw`/`bltz_spec_raw`/`bltzal_spec_raw`
above, each with its own `if`'s `else` branch now reading `squashNext :=
true` instead of plain fall-through — this is exactly `step`'s view of the
instruction (and the whole claim `step` itself is able to make: `step` is
deliberately kept unaware that `squashNext` is ever read back by anything,
per `Step.lean`'s docstring; the actual "delay slot is skipped" guarantee
is a property of `run`, proved separately below in
`beql_not_taken_squashes_delay_slot`). -/

/-- **`beql`/`bnel` step-level shape**: identical field layout and taken
condition to `beq` (`$rs == $rt`), but the not-taken case sets
`State.squashNext := true` instead of an ordinary fall-through
(INSTRUCTION-REF "beql / bnel" section). -/
theorem beql_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, squashNext := true } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bnel`**: the mirror image of `beql` — taken on `$rs ≠ $rt`, squashes
(sets `State.squashNext := true`) when `$rs == $rt` instead. -/
theorem bnel_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bnel rs rt imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next { s with pc := s.pc + 4#32, squashNext := true }
      else
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`blezl`**: same condition as `blez` (`$rs ≤ 0`, signed), not-taken
sets `State.squashNext := true` instead of falling through plainly. -/
theorem blezl_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.blezl rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≤ 0 then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, squashNext := true } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgtzl`**: same condition as `bgtz` (`$rs > 0`, signed), not-taken
sets `State.squashNext := true`. -/
theorem bgtzl_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgtzl rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if 0 < asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, squashNext := true } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bltzl`** (REGIMM `rt = 0x02`): same condition as `bltz` (`$rs < 0`,
signed), not-taken sets `State.squashNext := true`. -/
theorem bltzl_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzl rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, squashNext := true } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgezl`** (REGIMM `rt = 0x03`): same condition as `bgez` (`$rs ≥ 0`,
signed), not-taken sets `State.squashNext := true`. -/
theorem bgezl_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezl rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next
          { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s with pc := s.pc + 4#32, squashNext := true } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bltzall`** (REGIMM `rt = 0x12`): same unconditional-`$ra`-link
convention as `bltzal` (`$ra := PC_next + 4`, written before the
taken/not-taken test, independent of the branch outcome), then the same
`$rs < 0` condition as `bltzl` — not-taken sets `State.squashNext := true`
instead of plainly falling through, exactly like every other branch-likely
instruction above; the link still happens on the squashed path, matching
INSTRUCTION-REF's explicit note that the link "survives the squash case". -/
theorem bltzall_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bltzall rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s' with pc := pcNext, squashNext := true } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`bgezall`** (REGIMM `rt = 0x13`): same unconditional link as
`bltzall`, mirrored branch condition (`$rs ≥ 0`, same as `bgezl`/`bgezal`).
Not-taken sets `State.squashNext := true`; the link still happens either
way. -/
theorem bgezall_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bgezall rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        StepResult.next { s' with pc := pcNext, squashNext := true } := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, squashNext, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-! ### Satisfiable examples for the branch-likely `_spec_raw` theorems

Same discipline as every other group above: each theorem is instantiated
on a concrete program/state with every hypothesis discharged, via `#guard`
(compiled evaluation). Each pair below exercises both the taken branch
(ordinary `pendingBranch` scheduling, no `squashNext`) and the not-taken
branch (`squashNext := true`, `pendingBranch` left `none`). -/

-- `beql`: `5 == 5` schedules the target with no squash; `5 == 6` is false
-- and squashes instead of plainly falling through (contrast `beq`'s
-- not-taken example above, which never touches `squashNext`).
#guard (match step (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32) &&
            s.squashNext == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none && s.squashNext == true
        | .halt _ => false) = true

-- `bnel`: opposite polarity to `beql`, same squash mechanism.
#guard (match step (prog1Spec (.bnel 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32) &&
            s.squashNext == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bnel 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none && s.squashNext == true
        | .halt _ => false) = true

-- `blezl`/`bgtzl`: same conditions as `blez`/`bgtz`, squash instead of
-- plain fall-through on not-taken.
#guard (match step (prog1Spec (.blezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32) &&
            s.squashNext == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.blezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none && s.squashNext == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgtzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32) &&
            s.squashNext == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgtzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none && s.squashNext == true
        | .halt _ => false) = true

-- `bltzl`/`bgezl` (REGIMM): same conditions as `bltz`/`bgez`.
#guard (match step (prog1Spec (.bltzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32) &&
            s.squashNext == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bltzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none && s.squashNext == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32) &&
            s.squashNext == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == none && s.squashNext == true
        | .halt _ => false) = true

-- `bltzall`/`bgezall` (REGIMM): `$ra` links to `pc + 8` unconditionally in
-- both the taken and squashed cases, mirroring `bltzal`/`bgezal`'s own
-- examples above but now also checking `squashNext` on the not-taken side.
#guard (match step (prog1Spec (.bltzall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32) && s.squashNext == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bltzall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == none && s.squashNext == true
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32) && s.squashNext == false
        | .halt _ => false) = true
#guard (match step (prog1Spec (.bgezall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)]) with
        | .next s =>
          readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == none && s.squashNext == true
        | .halt _ => false) = true

/-! ## `run`-level squash guarantee for `beql`

Every theorem above (including the eight `_spec_raw` theorems in the
previous section) is a statement about a single `step` call. That is the
most `step` itself can say about the branch-likely family: per `Step.
lean`'s module docstring, `step` sets `State.squashNext := true` on a
not-taken branch-likely instruction but never reads the flag back — the
actual guarantee that the delay-slot instruction is skipped belongs to
`run`'s `go` loop, which checks the *incoming* state's `squashNext` before
ever calling `step` again. The theorem below is the one genuine `run`-level
claim this pass attempts (see this track's task description): a not-taken
`beql`, run for two steps, always lands `pc` at `s.pc + 8#32` — past the
branch *and* its squashed delay slot — **with no hypothesis at all about
what `p` contains at `s.pc + 4#32`**. That absence is the whole point: the
proof below never needs `fetchWord`/`decode` at `s.pc + 4#32` to go through
(`run.go`'s `squashNext`-true branch advances `pc` directly, bypassing
`step` entirely), so the claim holds equally whether that address holds a
real instruction, undecodable garbage, or nothing mapped at all — matching
real MIPS32 hardware, which never fetches a squashed delay slot. The
concrete example below goes one step further than "undecodable garbage"
and uses a program with *no* instruction mapped at `s.pc + 4#32` at all
(so a bare `step` call there would halt with `HaltReason.addressError`),
to make the "never even looked at" guarantee as visible as possible.

`run`'s `go` is a `let rec`, which Lean compiles to a top-level auxiliary
`run.go` with its own equation lemmas `run.go.eq_1`/`run.go.eq_2` — these
(not `unfold run`, which only peels the outer `run.go p maxSteps s₀ 0`
wrapper) are what this proof rewrites with, two rounds for the two-step
budget: round 1 (`fuel = 1`) finds `s.squashNext = false` (hypothesis
`hsquash`), so it falls through to an ordinary `step` call, which
`beql_spec_raw`'s not-taken case computes; round 2 (`fuel = 0`) finds the
resulting state's `squashNext = true`, so it takes the squash-skip branch
directly to `run.go.eq_1`'s base case, advancing `pc` by one more word
without ever consulting `p` again. -/
theorem beql_not_taken_squashes_delay_slot (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none) (hsquash : s.squashNext = false)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    run p s 2 = RunResult.limitReached { s with pc := s.pc + 8#32, squashNext := false } 2 := by
  have hstep : step p s = StepResult.next { s with pc := s.pc + 4#32, squashNext := true } := by
    rw [beql_spec_raw p s w rs rt imm hfetch hdecode hpb, if_neg (by simpa using hnot)]
  show run.go p 2 s 0 = _
  rw [show (2 : Nat) = Nat.succ 1 from rfl, run.go.eq_2, if_neg (by rw [hsquash]; simp), hstep]
  dsimp only
  rw [show (1 : Nat) = Nat.succ 0 from rfl, run.go.eq_2, if_pos (by simp), run.go.eq_1]
  dsimp only
  have hpc : s.pc + 4#32 + 4#32 = s.pc + 8#32 := by bv_decide
  rw [hpc]

-- Concrete instance of `beql_not_taken_squashes_delay_slot`: `prog1Spec`
-- maps *only* `textBase` (the `beql` itself) — there is deliberately no
-- instruction at `textBase + 4#32` at all, so a bare `step` call there
-- would halt with `HaltReason.addressError`. `run` nonetheless reaches
-- `textBase + 8#32` cleanly in exactly 2 steps, witnessing that the
-- squashed delay slot is never fetched, let alone executed.
#guard (match run (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) 2 with
        | .limitReached s steps => steps == 2 && s.pc == textBase + 8#32 && s.squashNext == false
        | .halted _ _ _ => false) = true
