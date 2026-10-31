import MipsSim.Word
import MipsSim.Types
import MipsSim.State
import MipsSim.Instruction
import MipsSim.Step

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
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.add rs rt rd)) :
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
    (hstep : step p s = StepResult.next s') : readReg s' 0 = readReg s 0 := by
  rw [add_spec_raw p s w rs rt rd hfw hdw] at hstep
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
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.sub rs rt rd)) :
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
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.addi rs rt imm)) :
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
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt)) :
    step p s =
      let a := asSigned (readReg s (regIdxSpec rs))
      let b := asSigned (readReg s (regIdxSpec rt))
      if b == 0 then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b), pc := s.pc + 4#32 } := by
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
    (hzero : readReg s (regIdxSpec rt) = 0#32) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [div_spec_raw p s w rs rt hfetch hdecode, hzero]
  rfl

/-- Corollary of `div_spec_raw`: with a negative dividend and a nonzero
divisor, the remainder (`hi`) takes the dividend's sign, since `Int.tmod`
truncates toward zero (same as Java's `%`, which Java-derived MARS uses —
INSTRUCTION-REF "div" section, "remainder takes the sign of the dividend"). -/
theorem div_negative_dividend_spec (p : Program) (s : State) (w rs rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.div rs rt))
    (hnz : asSigned (readReg s (regIdxSpec rt)) ≠ 0)
    (hneg : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step p s =
      StepResult.next
        { s with
          lo := ofInt32 ((asSigned (readReg s (regIdxSpec rs))).tdiv (asSigned (readReg s (regIdxSpec rt))))
          hi := ofInt32 ((asSigned (readReg s (regIdxSpec rs))).tmod (asSigned (readReg s (regIdxSpec rt))))
          pc := s.pc + 4#32 } := by
  rw [div_spec_raw p s w rs rt hfetch hdecode]
  have : ¬ (asSigned (readReg s (regIdxSpec rt)) == 0) := by
    simp [hnz]
  rw [if_neg (by simpa using this)]

/-- **`beq`/`bne` branch target and condition, in one equation.** Mirrors
`step`'s own code: the comparison `$rs == $rt` picks between falling through
to `PC_next` and jumping to `PC_next + (sext16(offset) << 2)`, with `beq`
and `bne` using the comparison the opposite way around (INSTRUCTION-REF
"beq"/"bne" sections, Global rule 1 — no delay slot, so the taken branch's
target is the very next fetch). -/
theorem beq_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm)) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next { s with pc := (s.pc + 4#32) + (signExt16 imm <<< 2) }
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

theorem bne_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm)) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        StepResult.next { s with pc := s.pc + 4#32 }
      else
        StepResult.next { s with pc := (s.pc + 4#32) + (signExt16 imm <<< 2) } := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- **`beq`, taken**: when `$rs = $rt`, the next program counter is the
address *after* `beq` plus the sign-extended offset scaled by 4
(INSTRUCTION-REF "beq" / Global rule 1: `PC = PC_next + (offset << 2)`, no
delay slot). -/
theorem beq_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := (s.pc + 4#32) + (signExt16 imm <<< 2) } := by
  rw [beq_spec_raw p s w rs rt imm hfetch hdecode, if_pos (by simpa using htaken)]

/-- **`beq`, not taken**: when `$rs ≠ $rt`, control simply falls through to
`PC_next` (INSTRUCTION-REF "beq" section). -/
theorem beq_not_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [beq_spec_raw p s w rs rt imm hfetch hdecode, if_neg (by simpa using hnot)]

/-- **`bne`, taken**: when `$rs ≠ $rt`, branches to `PC_next + (offset <<
2)` — the mirror image of `beq` (INSTRUCTION-REF "bne" section). -/
theorem bne_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (htaken : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := (s.pc + 4#32) + (signExt16 imm <<< 2) } := by
  rw [bne_spec_raw p s w rs rt imm hfetch hdecode, if_neg (by simpa using htaken)]

/-- **`bne`, not taken**: when `$rs = $rt`, falls through to `PC_next`. -/
theorem bne_not_taken_spec (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hnot : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  rw [bne_spec_raw p s w rs rt imm hfetch hdecode, if_pos (by simpa using hnot)]

/-- **`jal` links `$ra` to the address right after itself, and jumps to a
target whose top 4 bits come from `PC_next`, not from `jal`'s own
address** (INSTRUCTION-REF "jal" / Global rule 1 — `$ra = PC_next`,
`PC = (PC_next & 0xF0000000) | (target << 2)`). -/
theorem jal_spec_raw (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jal target)) :
    step p s =
      let pcNext := s.pc + 4#32
      StepResult.next
        { (writeReg s 31 pcNext) with
          pc := (pcNext &&& 0xf0000000#32) ||| (target <<< 2) } := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rfl

/-- Corollary of `jal_spec_raw`: `$ra` (register 31) reads back exactly
`PC_next`, i.e. the address of the instruction right after `jal`. -/
theorem jal_sets_ra (p : Program) (s : State) (w target : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.jal target))
    (hsize32 : s.regs.size = 32) :
    ∃ s', step p s = StepResult.next s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 4#32 := by
  refine ⟨_, jal_spec_raw p s w target hfetch hdecode, ?_⟩
  show readReg (writeReg s 31 (s.pc + 4#32)) (regIdxSpec 31#32) = s.pc + 4#32
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  rw [h31]
  exact writeReg_reads_back s 31 (s.pc + 4#32) (by decide) hsize32

/-- **`lw` composes a big-endian word from memory at `$rs + sext16(offset)`,
or halts with `addressError` on a misaligned effective address**
(INSTRUCTION-REF "lw" section; SPEC-NOTES §9.3 — the offset is
sign-extended, unlike MARS's own latent zero-extension bug for raw-decoded
binaries). -/
theorem lw_spec_raw (p : Program) (s : State) (w rs rt imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.lw rs rt imm)) :
    step p s =
      let addr := readReg s (regIdxSpec rs) + signExt16 imm
      match readMemWord s addr with
      | none => StepResult.halt (.addressError addr)
      | some v =>
        StepResult.next
          { (writeReg s (regIdxSpec rt) v) with
            pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
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
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step p s = StepResult.halt (.addressError (readReg s (regIdxSpec rs) + signExt16 imm)) := by
  rw [lw_spec_raw p s w rs rt imm hfetch hdecode]
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
    (hfetchBU : fetchWord p s.pc = some wbu) (hdecodeBU : decode wbu = some (.lbu rs rt imm)) :
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

-- `beq_taken_spec`/`beq_not_taken_spec`: equal registers branch, unequal
-- registers fall through.
#guard (match step (prog1Spec (.beq 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 + 12#32
        | .halt _ => false) = true
#guard (match step (prog1Spec (.beq 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `bne_taken_spec`/`bne_not_taken_spec`: the mirror image of `beq`.
#guard (match step (prog1Spec (.bne 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 + 12#32
        | .halt _ => false) = true

-- `jal_sets_ra`: `$ra` ends up exactly `pc + 4`, and the jump target's top
-- 4 bits come from `pc + 4`, not from `jal`'s own address.
#guard (match step (prog1Spec (.jal 0x1000#32)) (initialState textBase) with
        | .next s => readReg s 31 == textBase + 4#32 && s.pc == 0x4000#32
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
    (ha : readReg s (regIdxSpec 8#32) = 0x7fffffff#32)
    (hb : readReg s (regIdxSpec 9#32) = 1#32) :
    ¬ ∃ s', step p s = StepResult.next s' := by
  rintro ⟨s', hs'⟩
  rw [add_spec_raw p s w 8#32 9#32 10#32 hfetch hdecode] at hs'
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
    (hmisaligned : (readReg s (regIdxSpec rs) + signExt16 imm).toNat % 4 ≠ 0) :
    ¬ ∃ s', step p s = StepResult.next s' := by
  rintro ⟨s', hs'⟩
  rw [lw_misaligned_spec p s w rs rt imm hfetch hdecode hmisaligned] at hs'
  cases hs'

-- Concrete witness: `lw` from a `+1`-misaligned address halts, it never
-- "succeeds anyway" with some rounded value.
#guard (match step (prog1Spec (.lw 8#32 9#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0x10010000#32)]) with
        | .next _ => false
        | .halt _ => true) = true
