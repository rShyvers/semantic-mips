import Std.Data.HashMap.Basic
import MipsSim.Word
import MipsSim.Types
import MipsSim.State
import MipsSim.Instruction

/-!
# Step — small-step semantics of the v1 MIPS instruction set

Wave 2 module (DESIGN.md §4): `step` and the bounded `run` loop. This is the
single writer for the simulator's execution semantics; it composes the
foundation (`Word`, `Types`) and Wave 1 modules (`State`, `Instruction`)
without modifying any of them.

Ground truth for every instruction: `docs/spec/INSTRUCTION-REF.md`. Where the
MARS source diverges from the plain MIPS architecture, `docs/spec/SPEC-NOTES.md`
§9 overrides (no delay slots; `div`/`divu` by zero leave `hi`/`lo` unchanged
and do **not** halt; `lw`/`sw` offsets are sign-extended per the ISA, unlike
MARS's latent zero-extension bug for raw-decoded binary).

## Design notes

- `step` is total: every input `(p, s)` produces a `StepResult`, never `panic`
  or `sorry`. Decode/fetch failures and syscall-number mismatches all become
  defined `HaltReason`s.
- Instruction-fetch failure (misaligned `pc`, or no instruction recorded at
  `pc`) is modeled as `HaltReason.addressError s.pc` — this matches
  INSTRUCTION-REF Global rule §5 ("Instruction fetch misalignment/out-of-range
  ... halts with EXCEPTION"). A fetched-but-undecodable word (e.g. an
  unimplemented opcode) is `HaltReason.illegalInstruction word` instead, since
  in that case we *do* have a concrete word to report.
- Register-field operands on `Instruction` constructors are raw `W32`s
  produced by 5-bit field extraction in `decode`, so their `toNat` values are
  always `< 32`; `regIdx` converts them to `Fin 32` for `readReg`/`writeReg`.
-/

/-- Convert a raw 5-bit register-field value (as extracted by `decode`, hence
always `< 32`) into a `Fin 32` index for `readReg`/`writeReg`. -/
private def regIdx (w : W32) : Fin 32 :=
  Fin.ofNat 32 w.toNat

/-- Advance `s`'s program counter by one instruction word (`W32` wraparound
on overflow, matching hardware). Used for every non-control-flow instruction
and for untaken/fallthrough control flow. -/
private def advance (s : State) : State :=
  { s with pc := s.pc + 4#32 }

/-- Package `s` as a successful step that just falls through to `pc + 4`. -/
private def mkNext (s : State) : StepResult :=
  StepResult.next (advance s)

/-- Set `s`'s program counter to an explicitly-computed value (used by
branches/jumps, which bypass `advance`). -/
private def setPc (s : State) (pc : W32) : State :=
  { s with pc := pc }

/-- Signed-overflow predicate for `add`/`addi`, following INSTRUCTION-REF's
exact Java-derived test: overflow iff both operands are non-negative and the
(32-bit-wrapped) sum is negative, or both are negative and the sum is
non-negative. -/
private def addOverflows (a b sum : Int) : Bool :=
  decide ((0 ≤ a ∧ 0 ≤ b ∧ sum < 0) ∨ (a < 0 ∧ b < 0 ∧ 0 ≤ sum))

/-- Signed-overflow predicate for `sub`, following INSTRUCTION-REF's exact
test: overflow iff the minuend is non-negative, the subtrahend is negative,
and the (32-bit-wrapped) difference is negative; or the minuend is negative,
the subtrahend is non-negative, and the difference is non-negative. -/
private def subOverflows (a b diff : Int) : Bool :=
  decide ((0 ≤ a ∧ b < 0 ∧ diff < 0) ∨ (a < 0 ∧ 0 ≤ b ∧ 0 ≤ diff))

/-- Sign-extend a byte to a full `W32` (for `lb`). -/
private def signExtByte (b : UInt8) : W32 :=
  (BitVec.ofNat 8 b.toNat).signExtend 32

/-- Zero-extend a byte to a full `W32` (for `lbu`). -/
private def zeroExtByte (b : UInt8) : W32 :=
  BitVec.ofNat 32 b.toNat

/-- Maximum number of bytes scanned by syscall 4 (`PrintString`) before
giving up. This is a v1 simulator limitation (needed for `step` to remain a
total function without assuming anything about how "long" a null-terminated
string in sparse memory can be): any realistic test-corpus string is many
orders of magnitude shorter than this. Documented for the Wave 3 harness in
case a corpus program relies on a longer unterminated scan. -/
private def printStringFuel : Nat := 65536

/-- Scan up to `fuel` bytes starting at `addr`, stopping at the first `0x00`
byte (exclusive) or when fuel runs out, decoding each byte as ASCII. Absent
bytes read as `0` (`State.readMemByte`'s zero-fill convention), so any scan
over memory that is not deliberately padded with a long run of distinct
nonzero bytes terminates well within `printStringFuel`. -/
private def readCString (s : State) (addr : W32) : Nat → String
  | 0 => ""
  | fuel + 1 =>
    let b := (s.mem.get? addr).getD 0
    if b == 0 then ""
    else String.singleton (Char.ofNat b.toNat) ++ readCString s (addr + 1#32) fuel

/-- Execute a single already-fetched-and-decoded instruction. `w` is the raw
instruction word (needed only to report `illegalInstruction` for an unknown
`syscall` service number, per the pinned syscall decision). -/
private def execInstr (s : State) (w : W32) (instr : Instruction) : StepResult :=
  match instr with
  -- R-type reg/reg/reg arithmetic
  | .add rs rt rd =>
    let av := readReg s (regIdx rs)
    let bv := readReg s (regIdx rt)
    let sumBV := av + bv
    if addOverflows (asSigned av) (asSigned bv) (asSigned sumBV) then
      StepResult.halt .arithmeticOverflow
    else
      mkNext (writeReg s (regIdx rd) sumBV)
  | .addu rs rt rd =>
    mkNext (writeReg s (regIdx rd) (readReg s (regIdx rs) + readReg s (regIdx rt)))
  | .sub rs rt rd =>
    let av := readReg s (regIdx rs)
    let bv := readReg s (regIdx rt)
    let diffBV := av - bv
    if subOverflows (asSigned av) (asSigned bv) (asSigned diffBV) then
      StepResult.halt .arithmeticOverflow
    else
      mkNext (writeReg s (regIdx rd) diffBV)
  | .subu rs rt rd =>
    mkNext (writeReg s (regIdx rd) (readReg s (regIdx rs) - readReg s (regIdx rt)))
  | .and rs rt rd =>
    mkNext (writeReg s (regIdx rd) (readReg s (regIdx rs) &&& readReg s (regIdx rt)))
  | .or rs rt rd =>
    mkNext (writeReg s (regIdx rd) (readReg s (regIdx rs) ||| readReg s (regIdx rt)))
  | .xor rs rt rd =>
    mkNext (writeReg s (regIdx rd) (readReg s (regIdx rs) ^^^ readReg s (regIdx rt)))
  | .nor rs rt rd =>
    mkNext (writeReg s (regIdx rd) (~~~(readReg s (regIdx rs) ||| readReg s (regIdx rt))))
  | .slt rs rt rd =>
    let v := if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))
             then 1#32 else 0#32
    mkNext (writeReg s (regIdx rd) v)
  | .sltu rs rt rd =>
    let v := if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat
             then 1#32 else 0#32
    mkNext (writeReg s (regIdx rd) v)
  -- R-type shifts
  | .sll rd rt shamt =>
    mkNext (writeReg s (regIdx rd) (readReg s (regIdx rt) <<< shamt.toNat))
  | .srl rd rt shamt =>
    mkNext (writeReg s (regIdx rd) (readReg s (regIdx rt) >>> shamt.toNat))
  | .sra rd rt shamt =>
    mkNext (writeReg s (regIdx rd) ((readReg s (regIdx rt)).sshiftRight shamt.toNat))
  -- R-type mult/div
  | .mult rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
    mkNext { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32 }
  | .multu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
    mkNext { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32 }
  | .div rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    if b == 0 then
      -- SPEC-NOTES §9.2: hi/lo unchanged, no halt.
      mkNext s
    else
      mkNext { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b) }
  | .divu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    if b == 0 then
      mkNext s
    else
      mkNext { s with lo := BitVec.ofNat 32 (a / b), hi := BitVec.ofNat 32 (a % b) }
  | .mflo rd => mkNext (writeReg s (regIdx rd) s.lo)
  | .mfhi rd => mkNext (writeReg s (regIdx rd) s.hi)
  -- I-type arith/logic
  | .addi rs rt imm =>
    let av := readReg s (regIdx rs)
    let bv := signExt16 imm
    let sumBV := av + bv
    if addOverflows (asSigned av) (asSigned bv) (asSigned sumBV) then
      StepResult.halt .arithmeticOverflow
    else
      mkNext (writeReg s (regIdx rt) sumBV)
  | .addiu rs rt imm =>
    mkNext (writeReg s (regIdx rt) (readReg s (regIdx rs) + signExt16 imm))
  | .slti rs rt imm =>
    let v := if asSigned (readReg s (regIdx rs)) < asSigned (signExt16 imm)
             then 1#32 else 0#32
    mkNext (writeReg s (regIdx rt) v)
  | .sltiu rs rt imm =>
    let v := if (readReg s (regIdx rs)).toNat < (signExt16 imm).toNat
             then 1#32 else 0#32
    mkNext (writeReg s (regIdx rt) v)
  | .andi rs rt imm =>
    mkNext (writeReg s (regIdx rt) (readReg s (regIdx rs) &&& zeroExt16 imm))
  | .ori rs rt imm =>
    mkNext (writeReg s (regIdx rt) (readReg s (regIdx rs) ||| zeroExt16 imm))
  | .xori rs rt imm =>
    mkNext (writeReg s (regIdx rt) (readReg s (regIdx rs) ^^^ zeroExt16 imm))
  | .lui rt imm =>
    mkNext (writeReg s (regIdx rt) (zeroExt16 imm <<< 16))
  -- Memory access: effective address = $rs + sign-extended offset
  -- (SPEC-NOTES §9.3 — we follow the ISA, not MARS's lw/sw zero-extension bug).
  | .lw rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => StepResult.halt (.addressError addr)
    | some v => mkNext (writeReg s (regIdx rt) v)
  | .sw rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readReg s (regIdx rt)) with
    | none => StepResult.halt (.addressError addr)
    | some s' => mkNext s'
  | .lb rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => StepResult.halt (.addressError addr)
    | some b => mkNext (writeReg s (regIdx rt) (signExtByte b))
  | .lbu rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => StepResult.halt (.addressError addr)
    | some b => mkNext (writeReg s (regIdx rt) (zeroExtByte b))
  | .lh rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemHalf s addr with
    | none => StepResult.halt (.addressError addr)
    | some h => mkNext (writeReg s (regIdx rt) (signExt16 h))
  | .lhu rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemHalf s addr with
    | none => StepResult.halt (.addressError addr)
    | some h => mkNext (writeReg s (regIdx rt) h)
  | .sh rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemHalf s addr (readReg s (regIdx rt)) with
    | none => StepResult.halt (.addressError addr)
    | some s' => mkNext s'
  -- Control flow: no delay slot (SPEC-NOTES §9.1). `pcNext` is `s.pc + 4`;
  -- taken branches add `signExt16 imm <<< 2` to it, jumps replace its top
  -- 4 bits with the shifted target.
  | .beq rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      StepResult.next (setPc s (pcNext + (signExt16 imm <<< 2)))
    else
      StepResult.next (setPc s pcNext)
  | .bne rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      StepResult.next (setPc s pcNext)
    else
      StepResult.next (setPc s (pcNext + (signExt16 imm <<< 2)))
  | .blez rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) ≤ 0 then
      StepResult.next (setPc s (pcNext + (signExt16 imm <<< 2)))
    else
      StepResult.next (setPc s pcNext)
  | .bgtz rs imm =>
    let pcNext := s.pc + 4#32
    if 0 < asSigned (readReg s (regIdx rs)) then
      StepResult.next (setPc s (pcNext + (signExt16 imm <<< 2)))
    else
      StepResult.next (setPc s pcNext)
  | .j target =>
    let pcNext := s.pc + 4#32
    StepResult.next (setPc s ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)))
  | .jal target =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 pcNext
    StepResult.next (setPc s' ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)))
  -- Syscalls (v1 scope: 1/4/10/11; see docs/spec/INSTRUCTION-REF.md syscall section).
  | .syscall =>
    match (readReg s 2).toNat with
    | 1 =>
      let n := asSigned (readReg s 4)
      mkNext { s with out := s.out ++ toString n ++ "\n" }
    | 4 =>
      let str := readCString s (readReg s 4) printStringFuel
      mkNext { s with out := s.out ++ str }
    | 10 => StepResult.halt .exit
    | 11 =>
      let c := Char.ofNat ((readReg s 4 &&& 0xff#32).toNat)
      mkNext { s with out := s.out ++ String.singleton c }
    | _ =>
      -- v1 approximation of MARS's unsupported-syscall-number error: we have
      -- no generic `ProcessingException`/`SYSCALL_EXCEPTION` halt reason, so
      -- we report it the same way as any other undecodable-in-context word.
      StepResult.halt (.illegalInstruction w)

/-- Execute a single instruction: fetch at `s.pc`, decode, and dispatch.
Total: fetch/decode failure and syscall-dispatch failure all become defined
`HaltReason`s rather than partial behavior. -/
def step (p : Program) (s : State) : StepResult :=
  match fetchWord p s.pc with
  | none => StepResult.halt (.addressError s.pc)
  | some w =>
    match decode w with
    | none => StepResult.halt (.illegalInstruction w)
    | some instr => execInstr s w instr

/-- Outcome of running a bounded number of steps: either the program halted
(carrying the reason, the final state, and how many instructions executed
before and including the halting step), or the step budget was exhausted
first. -/
inductive RunResult where
  | halted (r : HaltReason) (s : State) (steps : Nat)
  | limitReached (s : State) (steps : Nat)

/-- Run `step` repeatedly from `s₀` until it halts or `maxSteps` instructions
have been executed, whichever comes first. Total by structural recursion on
the fuel parameter. `steps` counts every executed instruction, including the
one that produces a halt (if any). -/
def run (p : Program) (s₀ : State) (maxSteps : Nat) : RunResult :=
  let rec go : Nat → State → Nat → RunResult
    | 0, s, steps => .limitReached s steps
    | fuel + 1, s, steps =>
      match step p s with
      | .halt r => .halted r s (steps + 1)
      | .next s' => go fuel s' (steps + 1)
  go maxSteps s₀ 0

-- ## Tests
--
-- Per DESIGN.md §5 / CLAUDE.md §5: pure arithmetic helpers (no `Program` or
-- `State.mem` HashMap access) are checked with `by decide`/`by rfl`. Anything
-- that calls `step`/`run` touches `Program` (`Std.HashMap W32 W32`), which is
-- `cbv_opaque` and not kernel-reducible, so *every* `step`/`run` check below
-- uses `#guard` (compiled evaluation) — this is a strictly larger scope than
-- Wave 1's "memory contents" rule, because `step` always fetches from
-- `Program` first. The one exception is the misaligned-fetch case, which
-- short-circuits before touching the map and so is provable by `decide`.

section TestHelpers

private def regs0 : State := initialState textBase

private def setRegs (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeReg acc kv.1 kv.2) s

private def prog1 (instr : Instruction) : Program :=
  (∅ : Program).insert textBase (encode instr)

private def progAt (addr : W32) (instr : Instruction) : Program :=
  (∅ : Program).insert addr (encode instr)

private def buildProg (base : W32) (instrs : List Instruction) : Program :=
  instrs.zipIdx.foldl (fun acc (instr, i) => acc.insert (base + BitVec.ofNat 32 (4 * i)) (encode instr))
    (∅ : Program)

private def stepState (p : Program) (s : State) : Option State :=
  match step p s with
  | .next s' => some s'
  | .halt _ => none

private def nextRegEq (r : StepResult) (i : Fin 32) (v : W32) : Bool :=
  match r with
  | .next s => readReg s i == v
  | .halt _ => false

private def nextPcEq (r : StepResult) (pc : W32) : Bool :=
  match r with
  | .next s => s.pc == pc
  | .halt _ => false

private def nextHiLoEq (r : StepResult) (hi lo : W32) : Bool :=
  match r with
  | .next s => s.hi == hi && s.lo == lo
  | .halt _ => false

private def isNext (r : StepResult) : Bool :=
  match r with
  | .next _ => true
  | .halt _ => false

private def isHaltOverflow (r : StepResult) : Bool :=
  match r with
  | .halt .arithmeticOverflow => true
  | _ => false

private def isHaltIllegal (r : StepResult) (w : W32) : Bool :=
  match r with
  | .halt (.illegalInstruction w') => w' == w
  | _ => false

private def isHaltAddr (r : StepResult) (a : W32) : Bool :=
  match r with
  | .halt (.addressError a') => a' == a
  | _ => false

private def isHaltExit (r : StepResult) : Bool :=
  match r with
  | .halt .exit => true
  | _ => false

end TestHelpers

-- ### Pure-arithmetic helper sanity (`by decide`/`by rfl`, no `Program`/`mem`)

example : regIdx (5#32) = (5 : Fin 32) := by decide
example : regIdx (31#32) = (31 : Fin 32) := by decide
example : (advance (initialState textBase)).pc = textBase + 4#32 := by decide
example : addOverflows 0x7fffffff (1 : Int) (-0x80000000 : Int) = true := by decide
example : addOverflows 5 7 12 = false := by decide
example : subOverflows (-0x80000000 : Int) 1 0x7fffffff = true := by decide
example : subOverflows 10 3 7 = false := by decide
example : signExtByte 0x80 = 0xffffff80#32 := by decide
example : zeroExtByte 0x80 = 0x00000080#32 := by decide
-- PC wraparound (W32 arithmetic): pc+4 wraps past 0xffffffff.
example : (0xfffffffc#32 : W32) + 4#32 = 0#32 := by decide

-- Misaligned instruction fetch short-circuits before touching `Program`
-- (same reasoning as `fetchWord`'s own tests in State.lean), so this is
-- provable by `decide` even though `step`'s signature takes a `Program`.
private def misalignedState : State := { (initialState textBase) with pc := textBase + 1#32 }
example : isHaltAddr (step (∅ : Program) misalignedState) (textBase + 1#32) = true := by decide

-- ### R-type reg/reg/reg: one basic case each, plus `$zero` write-ignore

#guard nextRegEq (step (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 7#32)]))
  10 12#32
#guard nextRegEq (step (prog1 (.addu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 2#32)]))
  10 1#32
#guard nextRegEq (step (prog1 (.sub 8#32 9#32 10#32)) (setRegs regs0 [(8, 10#32), (9, 3#32)]))
  10 7#32
#guard nextRegEq (step (prog1 (.subu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0#32), (9, 1#32)]))
  10 0xffffffff#32
#guard nextRegEq (step (prog1 (.and 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0x0f000f00#32
#guard nextRegEq (step (prog1 (.or 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0xff0fff0f#32
#guard nextRegEq (step (prog1 (.xor 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0xf00ff00f#32
#guard nextRegEq (step (prog1 (.nor 8#32 9#32 10#32)) (setRegs regs0 [(8, 0#32), (9, 0#32)]))
  10 0xffffffff#32
#guard nextRegEq (step (prog1 (.slt 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  10 1#32  -- signed: -1 < 1
#guard nextRegEq (step (prog1 (.sltu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  10 0#32  -- unsigned: 0xffffffff is not < 1
-- `$rd = $zero` write-ignore, observed through `step` (and pc still advances)
#guard (match step (prog1 (.add 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 7#32)]) with
        | .next s' => readReg s' 0 == 0#32 && s'.pc == textBase + 4#32
        | .halt _ => false)

-- ### add/sub overflow traps

#guard isHaltOverflow (step (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)]))
#guard isHaltOverflow (step (prog1 (.sub 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))
-- addu/subu never trap on the same operands
#guard isNext (step (prog1 (.addu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)]))
#guard isNext (step (prog1 (.subu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))

-- ### Shifts: shamt 0 and 31; sra sign-fill

#guard nextRegEq (step (prog1 (.sll 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)])) 10 0x12345678#32
#guard nextRegEq (step (prog1 (.sll 10#32 8#32 31#32)) (setRegs regs0 [(8, 1#32)])) 10 0x80000000#32
#guard nextRegEq (step (prog1 (.srl 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)])) 10 0x12345678#32
#guard nextRegEq (step (prog1 (.srl 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 1#32
#guard nextRegEq (step (prog1 (.sra 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 0x80000000#32
#guard nextRegEq (step (prog1 (.sra 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 0xffffffff#32

-- ### slt vs sltu with a negative operand; slti/sltiu

#guard nextRegEq (step (prog1 (.slti 8#32 9#32 0x0000#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 1#32  -- -1 < 0
#guard nextRegEq (step (prog1 (.sltiu 8#32 9#32 0x0000#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 0#32 -- 0xffffffff </u 0 is false

-- ### mult / multu / div / divu / mflo / mfhi

-- mult: positive × positive
#guard nextHiLoEq (step (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 6#32), (9, 7#32)])) 0#32 42#32
-- mult: negative × negative, hi ≠ 0
#guard nextHiLoEq (step (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  0x3782dace#32 0x9d900000#32
-- mflo/mfhi read both halves back out
#guard (match stepState (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (step (prog1 (.mflo 10#32)) s'') 10 0x9d900000#32 &&
          nextRegEq (step (prog1 (.mfhi 11#32)) s'') 11 0x3782dace#32
        | none => false)
-- multu: both operands > 2^31
#guard nextHiLoEq (step (prog1 (.multu 8#32 9#32)) (setRegs regs0 [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x7ce66c50#32 0xe2840000#32

-- div: positive dividend
#guard nextHiLoEq (step (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 17#32), (9, 5#32)])) 2#32 3#32
-- div: negative dividend — remainder takes the dividend's sign
#guard nextHiLoEq (step (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 0xffffffef#32), (9, 5#32)]))
  0xfffffffe#32 0xfffffffd#32  -- hi = -2, lo = -3  (tdiv(-17,5)=-3, tmod(-17,5)=-2)
-- div: zero divisor with pre-seeded hi/lo — unchanged, no halt
private def seededHiLo : State := { regs0 with hi := 0xdeadbeef#32, lo := 0xcafef00d#32 }
#guard isNext (step (prog1 (.div 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))
#guard nextHiLoEq (step (prog1 (.div 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))
  0xdeadbeef#32 0xcafef00d#32
-- div: INT_MIN / -1 wraps silently (no halt, no overflow concept for div)
#guard nextHiLoEq (step (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 0xffffffff#32)]))
  0#32 0x80000000#32
-- divu: basic
#guard nextHiLoEq (step (prog1 (.divu 8#32 9#32)) (setRegs regs0 [(8, 17#32), (9, 5#32)])) 2#32 3#32
-- divu: zero divisor unchanged, no halt
#guard isNext (step (prog1 (.divu 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))

-- ### addi overflow trap vs addiu wrap; andi/ori/xori high-imm-bits; lui

#guard isHaltOverflow (step (prog1 (.addi 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x7fffffff#32)]))
#guard nextRegEq (step (prog1 (.addiu 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x7fffffff#32)])) 9 0x80000000#32
-- `andi`/`ori`/`xori` zero-extend the immediate (imm bit 15 set must NOT sign-extend)
#guard nextRegEq (step (prog1 (.andi 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 0x00008001#32
#guard nextRegEq (step (prog1 (.ori 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0#32)])) 9 0x00008001#32
#guard nextRegEq (step (prog1 (.xori 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0#32)])) 9 0x00008001#32
#guard nextRegEq (step (prog1 (.lui 9#32 0x8001#32)) regs0) 9 0x80010000#32

-- ### Loads/stores: big-endian composition, sign/zero extension, alignment

private def memTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32)]) with
      mem := ((((∅ : Std.HashMap W32 UInt8).insert 0x10010004#32 0x80).insert 0x10010005#32 0x01)
                |>.insert 0x10010006#32 0xff).insert 0x10010007#32 0x00 }

-- lw: full big-endian word
#guard nextRegEq (step (prog1 (.lw 8#32 9#32 4#32)) memTestState) 9 0x8001ff00#32
-- lb/lbu at the same address: sign-extend vs zero-extend a high-bit byte
#guard nextRegEq (step (prog1 (.lb 8#32 9#32 4#32)) memTestState) 9 0xffffff80#32
#guard nextRegEq (step (prog1 (.lbu 8#32 9#32 4#32)) memTestState) 9 0x00000080#32
-- lh/lhu at offset 4 (0x8001) and offset 6 (0xff00)
#guard nextRegEq (step (prog1 (.lh 8#32 9#32 4#32)) memTestState) 9 0xffff8001#32
#guard nextRegEq (step (prog1 (.lhu 8#32 9#32 4#32)) memTestState) 9 0x00008001#32
#guard nextRegEq (step (prog1 (.lh 8#32 9#32 6#32)) memTestState) 9 0xffffff00#32
#guard nextRegEq (step (prog1 (.lhu 8#32 9#32 6#32)) memTestState) 9 0x0000ff00#32
-- sw then read back
#guard (stepState (prog1 (.sw 8#32 9#32 4#32)) (setRegs regs0 [(8, 0x10010000#32), (9, 0x12345678#32)])).bind
        (fun s' => readMemWord s' 0x10010004#32) = some 0x12345678#32
-- sh stores only the low 16 bits, big-endian
#guard (stepState (prog1 (.sh 8#32 9#32 4#32)) (setRegs regs0 [(8, 0x10010000#32), (9, 0xffff1234#32)])).bind
        (fun s' => readMemHalf s' 0x10010004#32) = some 0x1234#32
-- misaligned lw/sw/lh/sh → addressError; lb/lbu never misalign
#guard isHaltAddr (step (prog1 (.lw 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) 0x10010001#32
#guard isHaltAddr (step (prog1 (.sw 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) 0x10010001#32
#guard isHaltAddr (step (prog1 (.lh 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) 0x10010001#32
#guard isHaltAddr (step (prog1 (.sh 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) 0x10010001#32
#guard isNext (step (prog1 (.lb 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]))
-- effective address uses the sign-extended offset (SPEC-NOTES §9.3): a
-- negative offset must subtract, not add as a huge positive number.
#guard (stepState (prog1 (.sw 8#32 9#32 0xfffc#32)) (setRegs regs0 [(8, 0x10010010#32), (9, 0x2a#32)])).bind
        (fun s' => readMemWord s' 0x1001000c#32) = some 0x2a#32

-- ### beq/bne/blez/bgtz: taken/not-taken with exact target words

#guard nextPcEq (step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32)
#guard nextPcEq (step (prog1 (.bne 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.bne 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  (textBase + 4#32)
#guard nextPcEq (step (prog1 (.blez 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]))  -- -5 ≤ 0
  (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.blez 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 ≤ 0
  (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.blez 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 ≤ 0 is false
  (textBase + 4#32)
#guard nextPcEq (step (prog1 (.bgtz 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 > 0
  (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgtz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 > 0 is false
  (textBase + 4#32)

-- ### j/jal: exact targets including top-4-bit preservation from `pc_next`; jal $ra

private def crossRegionState : State := { regs0 with pc := 0x90400000#32 }
#guard nextPcEq (step (progAt 0x90400000#32 (.j 0x1000#32)) crossRegionState) 0x90004000#32
#guard nextPcEq (step (progAt 0x90400000#32 (.jal 0x1000#32)) crossRegionState) 0x90004000#32
#guard nextRegEq (step (progAt 0x90400000#32 (.jal 0x1000#32)) crossRegionState) 31 0x90400004#32

-- ### syscalls

#guard (stepState (prog1 .syscall) (setRegs regs0 [(2, 1#32), (4, 5#32)])).bind (fun s => some s.out)
  = some "5\n"
#guard (stepState (prog1 .syscall) (setRegs regs0 [(2, 1#32), (4, 0xfffffffb#32)])).bind (fun s => some s.out)
  = some "-5\n"
private def syscall4State : State :=
  { (setRegs regs0 [(2, 4#32), (4, 0x10010000#32)]) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0x48).insert 0x10010001#32 0x69)
               |>.insert 0x10010002#32 0 }
#guard (stepState (prog1 .syscall) syscall4State).bind (fun s => some s.out) = some "Hi"
private def syscall4EmptyState : State :=
  { (setRegs regs0 [(2, 4#32), (4, 0x10010000#32)]) with
      mem := (∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0 }
#guard (stepState (prog1 .syscall) syscall4EmptyState).bind (fun s => some s.out) = some ""
#guard isHaltExit (step (prog1 .syscall) (setRegs regs0 [(2, 10#32)]))
#guard (stepState (prog1 .syscall) (setRegs regs0 [(2, 11#32), (4, 0x41#32)])).bind (fun s => some s.out)
  = some "A"
#guard isHaltIllegal (step (prog1 .syscall) (setRegs regs0 [(2, 999#32)])) (encode .syscall)

-- ### Undecodable word → illegalInstruction

private def badWord : W32 := 0x11#32 <<< 26  -- opcode 0x11, unimplemented
private def badProg : Program := (∅ : Program).insert textBase badWord
#guard isHaltIllegal (step badProg regs0) badWord

-- ### `run`: a short program that computes something and exits

-- addi $t0,$zero,5 ; addi $t1,$zero,7 ; add $t2,$t0,$t1 ; add $a0,$t2,$zero ;
-- addi $v0,$zero,1 ; syscall (print 12) ; addi $v0,$zero,10 ; syscall (exit)
private def sumProg : Program :=
  buildProg textBase
    [ .addi 0#32 8#32 5#32
    , .addi 0#32 9#32 7#32
    , .add  8#32 9#32 10#32
    , .add  10#32 0#32 4#32
    , .addi 0#32 2#32 1#32
    , .syscall
    , .addi 0#32 2#32 10#32
    , .syscall ]

#guard (match run sumProg regs0 20 with
        | .halted .exit s steps => s.out == "12\n" && steps == 8
        | _ => false)

-- `limitReached`: a one-instruction infinite self-loop (`beq $zero,$zero,-1`)
private def loopProg : Program := (∅ : Program).insert textBase (encode (.beq 0#32 0#32 0xffff#32))
#guard (match run loopProg regs0 5 with
        | .limitReached _ steps => steps == 5
        | _ => false)
