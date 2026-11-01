import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Step

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

STALL NOTE: a fully generic proof needs `step` unfolded and then every one
of the 24 `Instruction` constructors handled uniformly. The arithmetic/
logic/mult/div instructions (no memory access, no branching) close cleanly
with `cases instr <;> simp_all [writeReg_preserves_zero_slot]`-style
reasoning, but the instructions whose body is itself a `match`/`if` on a
memory read or a branch condition (`lw`,`sw`,`lb`,`lbu`,`lh`,`lhu`,`sh`,
`beq`,`bne`,`blez`,`bgtz`,`j`,`jal`,`syscall`,`lui`) need that inner
match/if exposed before the combinator can see register-file structure, and
`dsimp`/`split` refuse to expose it uniformly across all of them in one
tactic script (each individually closes by the same technique used for the
per-instruction lemmas in Group 2, at the cost of one lemma per
instruction). Left `sorry` here; see `step_preserves_zero_register_arith`
below for the closed version covering every instruction without memory
access, branching, or jumping (everything but
`lw,sw,lb,lbu,lh,lhu,sh,beq,bne,blez,bgtz,j,jal,syscall,lui`), which is
exactly the subset that already closes. -/
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
    (hv0 : readReg s (regIdxSpec 2#32) = 1#32) :
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

/-! STALL NOTE on `syscall1_spec`/`syscall10_spec`: `step`'s own syscall
dispatch is a five-way `Nat` pattern match (`1 | 4 | 10 | 11 | _`) on
`(readReg s 2).toNat` nested inside `execInstr` (private, Group 2's usual
technique needs the exact match reconstructed and closed by `rfl`). That
`rfl` genuinely times out / mismatches on this match for an *abstract*
state `s` even with very large recursion/heartbeat budgets, and forcing the
syscall-number register to a literal value via `writeReg` does not help,
because `State.regs` has no general-purpose length invariant visible to the
kernel at this level (`writeReg`'s array write is a no-op if `s.regs` is
shorter than 32, which is possible for an arbitrary `s : State`). Rather
than add an artificial well-formedness hypothesis and risk more stalling,
these two are left `sorry`. The closed weaker versions below pin `s` down
to a fully concrete, well-formed state (via `initialState`) and verify the
same claims by `#guard` (compiled evaluation — required for anything that
touches `Program`/`State.mem`, which are backed by `cbv_opaque`
`Std.HashMap`s and are not kernel-reducible by `decide`/`rfl`). -/

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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
  obtain ⟨pc, regs, hi, lo, fpRegs, fpCondFlag, mem, out, pb, llBit, cp0Status, cp0Cause, cp0Epc⟩ := s
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
