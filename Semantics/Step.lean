import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction

/-!
# Step — small-step semantics of the v1 MIPS instruction set

Wave 2 module (DESIGN.md §4): `step` and the bounded `run` loop. This is the
single writer for the simulator's execution semantics; it composes the
foundation (`Word`, `Types`) and Wave 1 modules (`State`, `Instruction`)
without modifying any of them.

Ground truth for every instruction: `docs/spec/INSTRUCTION-REF.md`. Where the
MARS source diverges from the plain MIPS architecture, `docs/spec/SPEC-NOTES.md`
§9 overrides (real MIPS32 one-delay-slot branch/jump semantics, not MARS's
default no-delay-slot config; `div`/`divu` by zero leave `hi`/`lo` unchanged
and do **not** halt; `lw`/`sw` offsets are sign-extended per the ISA, unlike
MARS's latent zero-extension bug for raw-decoded binary). The coprocessor-0
trap/exception model (`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu`/`break` and
`takeException` below) is grounded in the real MIPS32 ISA instead, per
INSTRUCTION-REF's dedicated "Coprocessor 0 / traps and exceptions" section.

The coprocessor-1 (FPU) instructions (v1.x addition; single-precision only,
double-precision out of scope — see `docs/spec/INSTRUCTION-REF.md`'s
floating-point section) are grounded directly in the real MIPS32 ISA, not
MARS; their arithmetic uses Lean core's native `Float32` (`Init.Data.Float.
Float32`), which implements IEEE-754 binary32 exactly, including
`Float32.ofBits`/`Float32.toBits` for the lossless bit-pattern round-trip
`fpRegs` storage needs. No FP traps are modeled: divide-by-zero and invalid
operations propagate IEEE-754 Infinity/NaN naturally, the same precedent as
integer `div`/`divu` by zero (SPEC-NOTES §9 item 2).

`ll`/`sc` (v1.x addition; real MIPS32 atomic synchronization primitives, not
part of the original v1 instruction set) are grounded directly in the real
MIPS32 ISA (MD00086 Rev 2.50 §3.2), per `docs/spec/INSTRUCTION-REF.md`'s
dedicated section. Real hardware's `LLbit` is cleared by `sc` and by several
events this single-hart simulator has no notion of (context switches,
multi-core cache-coherence traffic); the one documented simplification this
model makes is that `State.llBit` is cleared by *any* store-class
instruction (`sw`/`sh`/`swc1`; this model has no `sb`) executing after `ll`,
which is the one part of the real semantics that is both architecturally
mandated and observable on a single core.

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

/-- Advance `s`'s program counter: if a branch/jump delay-slot transfer is
pending (`s.pendingBranch = some target`), resolve it now — `pc` becomes
`target` and `pendingBranch` is cleared — otherwise this is an ordinary
fallthrough, so `pc` advances by one instruction word (`W32` wraparound on
overflow, matching hardware). This is the one place the delay-slot exit is
implemented (SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3): every
non-control-flow `execInstr` case routes through `mkNext`/`advance`, so it
automatically commits a pending branch/jump when it is the delay-slot
instruction, without any of those ~18 cases mentioning `pendingBranch`
themselves. -/
private def advance (orig result : State) : State :=
  match orig.pendingBranch with
  | some target => { result with pc := target, pendingBranch := none }
  | none => { result with pc := result.pc + 4#32 }

/-- Package `result` (the ordinary, non-control-flow effect of the current
instruction) as a successful step, resolving any delay-slot transfer
pending on `orig` -- the state `execInstr` was called with, i.e. *before*
this instruction's own effect -- via `advance`. Taking `orig` and `result`
as two separate arguments (rather than just the already-updated state)
keeps `orig.pendingBranch` syntactically visible at the call site instead of
buried behind an arbitrary `writeReg`/`writeMem*` call's own internal
register-index/alignment check, which matters for `StepSpec.lean`'s
`rfl`-based proofs (a symbolic register index makes `(writeReg s i v)`
itself irreducible, which would otherwise make its `.pendingBranch` field
irreducible too, even though `writeReg`/`writeMem*` never actually change
it). -/
private def mkNext (orig result : State) : StepResult :=
  StepResult.next (advance orig result)

/-- Whether `instr` is one of the twelve branch/jump instructions that
schedule a delay-slot transfer (`beq`,`bne`,`blez`,`bgtz`,`bltz`,`bgez`,
`bltzal`,`bgezal`,`j`,`jal`,`jr`,`jalr`). Used to detect a branch/jump
occurring itself inside another's delay slot (real MIPS32 leaves this
architecturally discouraged/implementation-defined), so `execInstr` can
halt with `HaltReason.branchInDelaySlot` instead of guessing. -/
private def isBranchLike (instr : Instruction) : Bool :=
  match instr with
  | .beq _ _ _ | .bne _ _ _ | .blez _ _ | .bgtz _ _
  | .bltz _ _ | .bgez _ _ | .bltzal _ _ | .bgezal _ _
  | .j _ | .jal _ | .jr _ | .jalr _ _ => true
  | _ => false

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

/-- Sign-extend the low byte of a register value to 32 bits (for `seb`).
Same technique as `signExtByte`, but operating directly on a `W32` register
value rather than a `UInt8` loaded from memory. -/
private def signExtLowByte (w : W32) : W32 :=
  (w.extractLsb 7 0).signExtend 32

/-- Count leading zero bits in `w` from the MSB (bit 31), stopping at the
first set bit; `32` if `w` is all-zero. `fuel` bounds the scan to the
remaining unscanned bit positions (`pos .. 31`) so this terminates by
structural recursion on `fuel`, with no `partial`/`sorry` needed. Used by
`clz`/`clo` (`docs/spec/INSTRUCTION-REF.md`): per the MIPS32 ISA, both
instructions report `32` when there is no bit of the relevant kind. -/
private def countLeadingZerosFrom (w : W32) : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos => if w.getMsbD pos then pos else countLeadingZerosFrom w fuel (pos + 1)

/-- Count leading zero bits in `w`, from the MSB. -/
private def countLeadingZeros (w : W32) : Nat :=
  countLeadingZerosFrom w 32 0

/-- Count leading one bits in `w`, from the MSB: a run of `1`s in `w` is
exactly a run of `0`s in `~~~w`, so this reduces to `countLeadingZeros`. -/
private def countLeadingOnes (w : W32) : Nat :=
  countLeadingZeros (~~~w)
/-- Take a real MIPS32 exception from `s` with the given `Cause.ExcCode`
(`excCodeBp` or `excCodeTr`; see `Types.lean`). This is the minimal
coprocessor-0 trap model (see the module's new "## Traps / exceptions
(coprocessor 0)" docs below and `docs/spec/INSTRUCTION-REF.md`): record the
trapping instruction's own address in `EPC`, pack `excCode` into `Cause`'s
`ExcCode` field (bits 6..2, i.e. `excCode <<< 2`), set `Status.EXL`, and jump
`PC` directly to `exceptionVectorAddr`. This is a real state transition
(`StepResult.next`), not a `HaltReason`; with no handler installed at the
vector address in v1, the *next* `step` call will naturally hit the existing
fetch-failure halt (`addressError`) there, giving real exception-vector
semantics without inventing a synthetic "unhandled exception" halt reason. -/
private def takeException (s : State) (excCode : W32) : StepResult :=
  StepResult.next
    { s with
        cp0Epc := s.pc
        cp0Cause := excCode <<< 2
        cp0Status := s.cp0Status ||| statusExlMask
        pc := exceptionVectorAddr }

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

/-- Reinterpret `w`'s raw bit pattern as an IEEE-754 single-precision float
(no numeric conversion \u2014 matches `fpRegs`' raw-bit-pattern storage
convention, `Types.lean`). `Float32.ofBits` is Lean core's exact IEEE-754
bit-pattern decode (`Init.Data.Float.Float32`). -/
private def floatOfBits (w : W32) : Float32 :=
  Float32.ofBits w.toNat.toUInt32

/-- Inverse of `floatOfBits`: the raw bit pattern of `f`, as a `W32`. -/
private def bitsOfFloat (f : Float32) : W32 :=
  BitVec.ofNat 32 f.toBits.toNat

/-- `cvt.s.w`'s numeric conversion: read `w`'s bit pattern as a 32-bit
two's-complement int (`Int32.ofBitVec`), then convert that integer *value*
to the nearest `Float32` (`Int32.toFloat32`, exact for every `Int32`). -/
private def floatOfIntBits (w : W32) : Float32 :=
  (Int32.ofBitVec w).toFloat32

/-- `cvt.w.s`'s numeric conversion: truncate `f` toward zero to a 32-bit
two's-complement int (`Float32.toInt32`, which clamps on overflow and maps
`NaN` to `0`), returned as a raw bit pattern. See `Instruction.cvtWS`'s
docstring for the truncating-vs-FCSR-rounding-mode simplification this
pins. -/
private def intBitsOfFloatTrunc (f : Float32) : W32 :=
  f.toInt32.toBitVec

/-- Execute a single already-fetched-and-decoded instruction. `w` is the raw
instruction word (needed only to report `illegalInstruction` for an unknown
`syscall` service number, per the pinned syscall decision).

Before dispatching, checks whether `s` already has a branch/jump delay-slot
transfer pending (`s.pendingBranch = some _`) *and* `instr` is itself one of
the eight branch/jump instructions (`isBranchLike`) — i.e. a branch/jump
occurring in another's delay slot. Real MIPS32 leaves that
architecturally discouraged/implementation-defined, so rather than pick an
arbitrary behavior this halts with `HaltReason.branchInDelaySlot`, keeping
`step` total and the condition diagnosable (SPEC-NOTES §9 item 1;
INSTRUCTION-REF Global rule 3). -/
private def execInstr (s : State) (w : W32) (instr : Instruction) : StepResult :=
  if s.pendingBranch.isSome && isBranchLike instr then
    StepResult.halt .branchInDelaySlot
  else
  match instr with
  -- R-type reg/reg/reg arithmetic
  | .add rs rt rd =>
    let av := readReg s (regIdx rs)
    let bv := readReg s (regIdx rt)
    let sumBV := av + bv
    if addOverflows (asSigned av) (asSigned bv) (asSigned sumBV) then
      StepResult.halt .arithmeticOverflow
    else
      mkNext s (writeReg s (regIdx rd) sumBV)
  | .addu rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) + readReg s (regIdx rt)))
  | .sub rs rt rd =>
    let av := readReg s (regIdx rs)
    let bv := readReg s (regIdx rt)
    let diffBV := av - bv
    if subOverflows (asSigned av) (asSigned bv) (asSigned diffBV) then
      StepResult.halt .arithmeticOverflow
    else
      mkNext s (writeReg s (regIdx rd) diffBV)
  | .subu rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) - readReg s (regIdx rt)))
  | .and rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) &&& readReg s (regIdx rt)))
  | .or rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) ||| readReg s (regIdx rt)))
  | .xor rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) ^^^ readReg s (regIdx rt)))
  | .nor rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (~~~(readReg s (regIdx rs) ||| readReg s (regIdx rt))))
  | .slt rs rt rd =>
    let v := if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rd) v)
  | .sltu rs rt rd =>
    let v := if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rd) v)
  -- Conditional move: `$rd` is left *unchanged*, not zeroed, when the
  -- condition fails (MIPS32r2 `movn`/`movz`; docs/spec/INSTRUCTION-REF.md).
  | .movn rs rt rd =>
    if readReg s (regIdx rt) != 0#32 then
      mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs)))
    else
      mkNext s s
  | .movz rs rt rd =>
    if readReg s (regIdx rt) == 0#32 then
      mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs)))
    else
      mkNext s s
  -- R-type shifts
  | .sll rd rt shamt =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) <<< shamt.toNat))
  | .srl rd rt shamt =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) >>> shamt.toNat))
  | .sra rd rt shamt =>
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).sshiftRight shamt.toNat))
  -- R-type variable shifts (MIPS32): the shift amount comes from `$rs`'s
  -- low 5 bits (`extractLsb 4 0`), not a fixed `shamt` field \u2014 so e.g. a
  -- shift-amount register holding 33 (0b100001) behaves identically to one
  -- holding 1, per the real MIPS32 ISA (docs/spec/MIPS-COVERAGE-GAPS.md \u00a73.4).
  | .sllv rd rt rs =>
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) <<< amt))
  | .srlv rd rt rs =>
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) >>> amt))
  | .srav rd rt rs =>
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).sshiftRight amt))
  -- R-type mult/div
  | .mult rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
    mkNext s { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32 }
  | .multu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
    mkNext s { s with lo := prod64.extractLsb 31 0, hi := prod64.extractLsb 63 32 }
  | .div rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    if b == 0 then
      -- SPEC-NOTES §9.2: hi/lo unchanged, no halt.
      mkNext s s
    else
      mkNext s { s with lo := ofInt32 (a.tdiv b), hi := ofInt32 (a.tmod b) }
  | .divu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    if b == 0 then
      mkNext s s
    else
      mkNext s { s with lo := BitVec.ofNat 32 (a / b), hi := BitVec.ofNat 32 (a % b) }
  | .mflo rd => mkNext s (writeReg s (regIdx rd) s.lo)
  | .mfhi rd => mkNext s (writeReg s (regIdx rd) s.hi)
  -- SPECIAL2 bit-count (MIPS32)
  | .clo rs rd =>
    mkNext s (writeReg s (regIdx rd) (BitVec.ofNat 32 (countLeadingOnes (readReg s (regIdx rs)))))
  | .clz rs rd =>
    mkNext s (writeReg s (regIdx rd) (BitVec.ofNat 32 (countLeadingZeros (readReg s (regIdx rs)))))
  -- SPECIAL2 GPR multiply (MIPS32): `$rd` gets the low 32 bits of the
  -- signed product, exactly the bits `mult`+`mflo` would leave in `lo`
  -- (two's-complement multiplication's low bits don't depend on the sign
  -- interpretation of the operands, so plain `W32` `*` already wraps
  -- correctly here \u2014 no need to go through `asSigned`/`BitVec.ofInt` the
  -- way `.mult` does). `hi`/`lo` are deliberately left **unchanged**: real
  -- MIPS32 hardware leaves them unpredictable after `mul`, and this is the
  -- simplest deterministic choice for this model (see `Instruction.mul`'s
  -- docstring and `docs/spec/INSTRUCTION-REF.md`).
  | .mul rs rt rd =>
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) * readReg s (regIdx rt)))
  -- SPECIAL3 BSHFL sign-extend (MIPS32r2)
  | .seb rd rt =>
    mkNext s (writeReg s (regIdx rd) (signExtLowByte (readReg s (regIdx rt))))
  | .seh rd rt =>
    mkNext s (writeReg s (regIdx rd) (signExt16 (readReg s (regIdx rt))))
  -- I-type arith/logic
  | .addi rs rt imm =>
    let av := readReg s (regIdx rs)
    let bv := signExt16 imm
    let sumBV := av + bv
    if addOverflows (asSigned av) (asSigned bv) (asSigned sumBV) then
      StepResult.halt .arithmeticOverflow
    else
      mkNext s (writeReg s (regIdx rt) sumBV)
  | .addiu rs rt imm =>
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) + signExt16 imm))
  | .slti rs rt imm =>
    let v := if asSigned (readReg s (regIdx rs)) < asSigned (signExt16 imm)
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rt) v)
  | .sltiu rs rt imm =>
    let v := if (readReg s (regIdx rs)).toNat < (signExt16 imm).toNat
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rt) v)
  | .andi rs rt imm =>
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) &&& zeroExt16 imm))
  | .ori rs rt imm =>
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) ||| zeroExt16 imm))
  | .xori rs rt imm =>
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) ^^^ zeroExt16 imm))
  | .lui rt imm =>
    mkNext s (writeReg s (regIdx rt) (zeroExt16 imm <<< 16))
  -- Memory access: effective address = $rs + sign-extended offset
  -- (SPEC-NOTES §9.3 — we follow the ISA, not MARS's lw/sw zero-extension bug).
  | .lw rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => StepResult.halt (.addressError addr)
    | some v => mkNext s (writeReg s (regIdx rt) v)
  | .sw rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readReg s (regIdx rt)) with
    | none => StepResult.halt (.addressError addr)
    | some s' => mkNext s { s' with llBit := false }
  | .lb rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => StepResult.halt (.addressError addr)
    | some b => mkNext s (writeReg s (regIdx rt) (signExtByte b))
  | .lbu rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemByte s addr with
    | none => StepResult.halt (.addressError addr)
    | some b => mkNext s (writeReg s (regIdx rt) (zeroExtByte b))
  | .lh rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemHalf s addr with
    | none => StepResult.halt (.addressError addr)
    | some h => mkNext s (writeReg s (regIdx rt) (signExt16 h))
  | .lhu rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemHalf s addr with
    | none => StepResult.halt (.addressError addr)
    | some h => mkNext s (writeReg s (regIdx rt) h)
  | .sh rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemHalf s addr (readReg s (regIdx rt)) with
    | none => StepResult.halt (.addressError addr)
    | some s' => mkNext s { s' with llBit := false }
  -- `ll`/`sc`: real MIPS32 atomic synchronization primitives (opcodes
  -- 0x30/0x38; MD00086 Rev 2.50 §3.2). `ll` loads like `lw` and additionally
  -- sets `llBit`; `sc` performs its store only if `llBit` is set (checked
  -- *before* clearing it), writing success/failure back to `$rt`, and
  -- always clears `llBit` afterward -- see `Types.lean`'s `llBit` docstring
  -- for this model's single-hart simplification.
  | .ll rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => StepResult.halt (.addressError addr)
    | some v => mkNext s { (writeReg s (regIdx rt) v) with llBit := true }
  | .sc rs rt imm =>
    -- The effective-address alignment check happens unconditionally, exactly
    -- as for `sw` (real MIPS32 computes/validates the memory reference
    -- regardless of whether `LLbit` ends up permitting the store); only
    -- *committing* `writeMemWord`'s result is conditional on `s.llBit`,
    -- which is checked before it is cleared below.
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readReg s (regIdx rt)) with
    | none => StepResult.halt (.addressError addr)
    | some stored =>
      if s.llBit then
        mkNext s { (writeReg stored (regIdx rt) 1#32) with llBit := false }
      else
        mkNext s { (writeReg s (regIdx rt) 0#32) with llBit := false }
  -- Control flow: one architectural delay slot per branch/jump, matching
  -- real MIPS32 (SPEC-NOTES §9 item 1 — not MARS's default no-delay-slot
  -- config; INSTRUCTION-REF Global rule 3). A taken branch/jump never jumps
  -- immediately: it falls through to `pcNext` (the delay-slot instruction
  -- executes next, normally) and *schedules* the real target in
  -- `pendingBranch`; `advance`/`mkNext` commits it one step later, when the
  -- delay-slot instruction retires. A not-taken branch sets no
  -- `pendingBranch` and is indistinguishable from an ordinary instruction
  -- (`mkNext`). `pcNext` is `s.pc + 4`; taken branches schedule
  -- `pcNext + (signExt16 imm <<< 2)`, jumps schedule a target whose top 4
  -- bits come from `pcNext`.
  | .beq rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      mkNext s s
  | .bne rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      mkNext s s
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .blez rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) ≤ 0 then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      mkNext s s
  | .bgtz rs imm =>
    let pcNext := s.pc + 4#32
    if 0 < asSigned (readReg s (regIdx rs)) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      mkNext s s
  -- REGIMM zero-comparison branches (opcode 0x01; MD00086 Rev 2.50 \u00a73.2,
  -- Table 3-2). `bltz`/`bgez` are plain conditional branches, same shape as
  -- `blez`/`bgtz` above. `bltzal`/`bgezal` additionally link `$ra` to
  -- `pcNext + 4` (`pc + 8`, past the delay slot, same convention as `jal`)
  -- -- real MIPS32 performs this link **unconditionally**, on every
  -- execution of the instruction, regardless of whether the branch itself
  -- is taken; only the branch transfer is conditional.
  | .bltz rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) < 0 then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      mkNext s s
  | .bgez rs imm =>
    let pcNext := s.pc + 4#32
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      mkNext s s
  | .bltzal rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if asSigned (readReg s (regIdx rs)) < 0 then
      StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      mkNext s s'
  | .bgezal rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      mkNext s s'
  | .j target =>
    let pcNext := s.pc + 4#32
    StepResult.next
      { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }
  | .jal target =>
    -- `$ra` links to `pc + 8` — past the delay slot — not `pcNext` (`pc + 4`):
    -- real MIPS32's `jal` link value is the address of the instruction
    -- *after* the delay slot, since the delay-slot instruction itself still
    -- executes before control reaches `$ra` on return.
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let s' := writeReg s 31 linkVal
    StepResult.next
      { s' with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }
  -- Register-indirect jump/call (real MIPS32 `jr`/`jalr`, MD00086 §3.2):
  -- same one-instruction delay-slot scheduling as `j`/`jal` above, but the
  -- target is the raw 32-bit value read from `$rs` instead of composed from
  -- the 26-bit `target` field. A misaligned `$rs` value is not special-cased
  -- here: it becomes an ordinary `addressError` halt the next time `step`
  -- tries to fetch from it (`fetchWord`'s existing alignment check), exactly
  -- like any other misaligned `pc`.
  | .jr rs =>
    let pcNext := s.pc + 4#32
    StepResult.next { s with pc := pcNext, pendingBranch := some (readReg s (regIdx rs)) }
  | .jalr rs rd =>
    -- `$rd` links to `pc + 8` — past the delay slot — the same `jal` link-value
    -- convention as above. The link target is read before `$rd` is written,
    -- so `jalr $rs, $rs` (rd = rs) still reads the pre-write `$rs` value.
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let target := readReg s (regIdx rs)
    let s' := writeReg s (regIdx rd) linkVal
    StepResult.next { s' with pc := pcNext, pendingBranch := some target }
  -- Coprocessor 1 (FPU), single-precision subset (docs/spec/INSTRUCTION-REF.md
  -- floating-point section). `mtc1`/`mfc1`/`lwc1`/`swc1` move/transfer raw
  -- bit patterns with no numeric conversion; arithmetic/compare/convert go
  -- through `floatOfBits`/`bitsOfFloat` at the point of computation.
  | .mfc1 rt fs =>
    mkNext s (writeReg s (regIdx rt) (readFpReg s (regIdx fs)))
  | .mtc1 rt fs =>
    mkNext s (writeFpReg s (regIdx fs) (readReg s (regIdx rt)))
  | .lwc1 rs ft imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr with
    | none => StepResult.halt (.addressError addr)
    | some v => mkNext s (writeFpReg s (regIdx ft) v)
  | .swc1 rs ft imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match writeMemWord s addr (readFpReg s (regIdx ft)) with
    | none => StepResult.halt (.addressError addr)
    | some s' => mkNext s { s' with llBit := false }
  | .addS fd fs ft =>
    let v := (floatOfBits (readFpReg s (regIdx fs))).add (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s (writeFpReg s (regIdx fd) (bitsOfFloat v))
  | .subS fd fs ft =>
    let v := (floatOfBits (readFpReg s (regIdx fs))).sub (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s (writeFpReg s (regIdx fd) (bitsOfFloat v))
  | .mulS fd fs ft =>
    let v := (floatOfBits (readFpReg s (regIdx fs))).mul (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s (writeFpReg s (regIdx fd) (bitsOfFloat v))
  | .divS fd fs ft =>
    -- IEEE-754 division; `$ft == 0` yields ±Infinity/NaN, never a trap
    -- (module docstring; SPEC-NOTES §9 item 2 precedent).
    let v := (floatOfBits (readFpReg s (regIdx fs))).div (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s (writeFpReg s (regIdx fd) (bitsOfFloat v))
  | .movS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs)))
  | .cvtSW fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (bitsOfFloat (floatOfIntBits (readFpReg s (regIdx fs)))))
  | .cvtWS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (intBitsOfFloatTrunc (floatOfBits (readFpReg s (regIdx fs)))))
  | .cEqS fs ft =>
    let flag := (floatOfBits (readFpReg s (regIdx fs))).beq (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s { s with fpCondFlag := flag }
  | .cLtS fs ft =>
    let flag := (floatOfBits (readFpReg s (regIdx fs))).lt (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s { s with fpCondFlag := flag }
  | .cLeS fs ft =>
    let flag := (floatOfBits (readFpReg s (regIdx fs))).le (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s { s with fpCondFlag := flag }
  -- `bc1t`/`bc1f`: upgraded during dev/v2 integration to use the same
  -- `pendingBranch` delay-slot scheduling as `beq`/`bne`/etc. (real MIPS32
  -- gives every branch, including FP ones, exactly one delay slot) instead
  -- of the immediate-jump the fpu track shipped under time pressure --
  -- closing that documented gap rather than leaving two different branch
  -- disciplines coexisting in one semantics.
  | .bc1t imm =>
    let pcNext := s.pc + 4#32
    if s.fpCondFlag then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      mkNext s s
  | .bc1f imm =>
    let pcNext := s.pc + 4#32
    if s.fpCondFlag then
      mkNext s s
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  -- Syscalls (v1 scope: 1/4/10/11; see docs/spec/INSTRUCTION-REF.md syscall section).
  | .syscall =>
    match (readReg s 2).toNat with
    | 1 =>
      let n := asSigned (readReg s 4)
      mkNext s { s with out := s.out ++ toString n }
    | 4 =>
      let str := readCString s (readReg s 4) printStringFuel
      mkNext s { s with out := s.out ++ str }
    | 10 => StepResult.halt .exit
    | 11 =>
      let c := Char.ofNat ((readReg s 4 &&& 0xff#32).toNat)
      mkNext s { s with out := s.out ++ String.singleton c }
    | _ =>
      -- v1 approximation of MARS's unsupported-syscall-number error: we have
      -- no generic `ProcessingException`/`SYSCALL_EXCEPTION` halt reason, so
      -- we report it the same way as any other undecodable-in-context word.
      StepResult.halt (.illegalInstruction w)
  -- Trap-on-condition (coprocessor-0 exception model, real MIPS32 ISA; see
  -- `takeException` above and `docs/spec/INSTRUCTION-REF.md`). Trap-not-taken
  -- behaves like an ordinary instruction: `mkNext s` falls through to
  -- `pc + 4` with no CP0 state touched at all.
  | .teq rs rt =>
    if readReg s (regIdx rs) == readReg s (regIdx rt) then takeException s excCodeTr else mkNext s s
  | .tne rs rt =>
    if readReg s (regIdx rs) ≠ readReg s (regIdx rt) then takeException s excCodeTr else mkNext s s
  | .tlt rs rt =>
    if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))
    then takeException s excCodeTr else mkNext s s
  | .tge rs rt =>
    if asSigned (readReg s (regIdx rs)) ≥ asSigned (readReg s (regIdx rt))
    then takeException s excCodeTr else mkNext s s
  | .tltu rs rt =>
    if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat
    then takeException s excCodeTr else mkNext s s
  | .tgeu rs rt =>
    if (readReg s (regIdx rs)).toNat ≥ (readReg s (regIdx rt)).toNat
    then takeException s excCodeTr else mkNext s s
  -- break: unconditional trap (coprocessor-0 exception model).
  | .break => takeException s excCodeBp
  -- Coprocessor 0 (CP0) register move and execution-control instructions
  -- (v1.x addition; `docs/spec/MIPS-COVERAGE-GAPS.md` \u00a73.10A). Scoped to
  -- exactly the three CP0 registers this project models: `rd = 12/13/14`
  -- maps to `cp0Status`/`cp0Cause`/`cp0Epc` (the real MIPS32 register
  -- numbers for `Status`/`Cause`/`EPC`). Any other `rd` has no backing
  -- register in this minimal model; rather than silently fabricate a `0`
  -- read or silently drop a write, this halts with
  -- `HaltReason.illegalInstruction` \u2014 a documented, honest choice (real
  -- hardware would read garbage or trap depending on the specific
  -- register; since every other CP0 register is architecturally
  -- out-of-scope here, a clean halt is more defensible than inventing
  -- behavior for registers this model doesn't have).
  | .mfc0 rt rd =>
    match rd.toNat with
    | 12 => mkNext s (writeReg s (regIdx rt) s.cp0Status)
    | 13 => mkNext s (writeReg s (regIdx rt) s.cp0Cause)
    | 14 => mkNext s (writeReg s (regIdx rt) s.cp0Epc)
    | _ => StepResult.halt (.illegalInstruction w)
  | .mtc0 rt rd =>
    match rd.toNat with
    | 12 => mkNext s { s with cp0Status := readReg s (regIdx rt) }
    | 13 => mkNext s { s with cp0Cause := readReg s (regIdx rt) }
    | 14 => mkNext s { s with cp0Epc := readReg s (regIdx rt) }
    | _ => StepResult.halt (.illegalInstruction w)
  -- `eret`: exception return (MD00086 Rev 2.50 \u00a73.2, Table 3-23). Sets
  -- `PC := cp0Epc` and clears `Status.EXL` (the same bit `takeException`
  -- sets, cleared here via `&&& ~~~statusExlMask`). Real MIPS32: `eret` is
  -- NOT delay-slotted \u2014 it takes effect immediately, an explicit
  -- architectural exception to the general branch/jump delay-slot rule, so
  -- (unlike every control-flow instruction above) this bypasses
  -- `mkNext`/`pendingBranch` entirely and sets `pc` directly.
  | .eret =>
    StepResult.next { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask }
  -- `wait`: real hardware halts the pipeline until an interrupt arrives;
  -- this simulator has no interrupt/timer model at all, so the only
  -- sensible behavior is a documented no-op that falls through to `pc + 4`
  -- via `mkNext`, the same as any other non-control-flow instruction.
  | .wait => mkNext s s

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

private def setFpRegs (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeFpReg acc kv.1 kv.2) s

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

private def nextFpRegEq (r : StepResult) (i : Fin 32) (v : W32) : Bool :=
  match r with
  | .next s => readFpReg s i == v
  | .halt _ => false

private def nextFpCondFlagEq (r : StepResult) (v : Bool) : Bool :=
  match r with
  | .next s => s.fpCondFlag == v
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

private def isHaltBranchInDelaySlot (r : StepResult) : Bool :=
  match r with
  | .halt .branchInDelaySlot => true
  | _ => false

private def nextPendingEq (r : StepResult) (pb : Option W32) : Bool :=
  match r with
  | .next s => s.pendingBranch == pb
  | .halt _ => false

private def nextLlBitEq (r : StepResult) (b : Bool) : Bool :=
  match r with
  | .next s => s.llBit == b
  | .halt _ => false

-- `sll $zero, $zero, 0` — the canonical MIPS encoding of `nop` (word
-- `0x00000000`) — used as an inert delay-slot filler instruction below.
private def nopInstr : Instruction := .sll 0#32 0#32 0#32

/-- Step once through `instr` placed at `base` (with `nopInstr` as its delay
slot at `base + 4`) from `s`, then step once more through the delay slot:
returns the landing `pc` after both steps, or `none` if either step halts.
Used to exercise the full two-step delay-slot behavior of a taken
branch/jump (SPEC-NOTES §9 item 1). -/
private def stepThroughDelaySlot (base : W32) (instr : Instruction) (s : State) : Option W32 :=
  let p := buildProg base [instr, nopInstr]
  match stepState p s with
  | some s1 => match step p s1 with
    | .next s2 => some s2.pc
    | .halt _ => none
  | none => none

end TestHelpers

-- ### Pure-arithmetic helper sanity (`by decide`/`by rfl`, no `Program`/`mem`)

example : regIdx (5#32) = (5 : Fin 32) := by decide
example : regIdx (31#32) = (31 : Fin 32) := by decide
example : (advance (initialState textBase) (initialState textBase)).pc = textBase + 4#32 := by decide
example : addOverflows 0x7fffffff (1 : Int) (-0x80000000 : Int) = true := by decide
example : addOverflows 5 7 12 = false := by decide
example : subOverflows (-0x80000000 : Int) 1 0x7fffffff = true := by decide
example : subOverflows 10 3 7 = false := by decide
example : signExtByte 0x80 = 0xffffff80#32 := by decide
example : zeroExtByte 0x80 = 0x00000080#32 := by decide
example : signExtLowByte 0x00000080#32 = 0xffffff80#32 := by decide
example : signExtLowByte 0x0000007f#32 = 0x0000007f#32 := by decide
example : countLeadingZeros 0#32 = 32 := by decide
example : countLeadingZeros 0xffffffff#32 = 0 := by decide
example : countLeadingZeros 0x80000000#32 = 0 := by decide
example : countLeadingZeros 1#32 = 31 := by decide
example : countLeadingZeros 0x0000ffff#32 = 16 := by decide
example : countLeadingOnes 0xffffffff#32 = 32 := by decide
example : countLeadingOnes 0#32 = 0 := by decide
example : countLeadingOnes 0xffff0000#32 = 16 := by decide
example : countLeadingOnes 0x7fffffff#32 = 0 := by decide  -- MSB clear -> zero leading ones
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

-- ### movn/movz: conditional move -- the "condition fails" case must leave
-- `$rd` at its *preset* value (99 below), not zero it (a real no-op, per
-- docs/spec/INSTRUCTION-REF.md's movn/movz entries).
#guard nextRegEq (step (prog1 (.movn 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 1#32), (10, 99#32)]))
  10 5#32   -- movn, $rt != 0: moves
#guard nextRegEq (step (prog1 (.movn 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 0#32), (10, 99#32)]))
  10 99#32  -- movn, $rt == 0: $rd unchanged
#guard nextRegEq (step (prog1 (.movz 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 0#32), (10, 99#32)]))
  10 5#32   -- movz, $rt == 0: moves
#guard nextRegEq (step (prog1 (.movz 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 1#32), (10, 99#32)]))
  10 99#32  -- movz, $rt != 0: $rd unchanged

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

-- ### mul (MIPS32 SPECIAL2 GPR multiply; docs/spec/MIPS-COVERAGE-GAPS.md §3.5)
-- `mul`'s result must match the low 32 bits `mult`+`mflo` would produce, for
-- the same operand pairs already exercised above -- including one whose
-- 64-bit product overflows 32 bits signed, confirming the wraparound -- and
-- `mul` must leave `hi`/`lo` unchanged (the pinned dialect choice).
#guard nextRegEq (step (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 6#32), (9, 7#32)])) 10 42#32  -- matches mult/mflo's lo above (0#32 42#32)
#guard nextRegEq (step (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  10 0x9d900000#32  -- matches mult/mflo's lo above (overflows 32-bit signed: hi was nonzero, 0x3782dace)
#guard nextHiLoEq (step (prog1 (.mul 8#32 9#32 10#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafef00d#32  -- hi/lo unchanged by mul
#guard nextRegEq (step (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 2#32)])) 10 0xfffffffe#32  -- (-1) * 2 = -2, wraps

-- ### clo/clz/movn/movz/seb/seh (MIPS32/MIPS32r2 additions; see
-- docs/spec/INSTRUCTION-REF.md)

-- clo: all-ones -> 32; a mixed pattern; all-zero -> 0 leading ones
#guard nextRegEq (step (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 10 32#32
#guard nextRegEq (step (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0xfff0ffff#32)])) 10 12#32
#guard nextRegEq (step (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0x00000000#32)])) 10 0#32
-- clz: all-zero -> 32; a mixed pattern; all-ones -> 0 leading zeros
#guard nextRegEq (step (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0x00000000#32)])) 10 32#32
#guard nextRegEq (step (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0x0000ffff#32)])) 10 16#32
#guard nextRegEq (step (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 10 0#32

-- seb: sign-extends only the low byte of $rt, ignoring higher bits
#guard nextRegEq (step (prog1 (.seb 10#32 8#32)) (setRegs regs0 [(8, 0x12345680#32)])) 10 0xffffff80#32
#guard nextRegEq (step (prog1 (.seb 10#32 8#32)) (setRegs regs0 [(8, 0x1234567f#32)])) 10 0x0000007f#32
-- seh: sign-extends only the low halfword of $rt
#guard nextRegEq (step (prog1 (.seh 10#32 8#32)) (setRegs regs0 [(8, 0x1234ffff#32)])) 10 0xffffffff#32
#guard nextRegEq (step (prog1 (.seh 10#32 8#32)) (setRegs regs0 [(8, 0x12347fff#32)])) 10 0x00007fff#32

-- ### sllv/srlv/srav (MIPS32 variable shifts; docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.4): the shift amount is `$rs`'s low 5 bits, not a `shamt` field --
-- these mirror the sll/srl/sra shamt-0/31 cases above but via a register,
-- and a shift-amount register holding 33 (0x21, i.e. 32 + 1) must behave
-- identically to one holding 1 (the masking test).
#guard nextRegEq (step (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 0#32)]))
  10 0x12345678#32
#guard nextRegEq (step (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 31#32)]))
  10 0x80000000#32
#guard nextRegEq (step (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 31#32)]))
  10 1#32
#guard nextRegEq (step (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 31#32)]))
  10 0xffffffff#32
-- masking: shift-amount register holding 33 behaves identically to holding 1
#guard nextRegEq (step (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 33#32)]))
  10 2#32
#guard nextRegEq (step (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 1#32)]))
  10 2#32
#guard nextRegEq (step (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 33#32)]))
  10 0x40000000#32
#guard nextRegEq (step (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))
  10 0x40000000#32
#guard nextRegEq (step (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 33#32)]))
  10 0xc0000000#32
#guard nextRegEq (step (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))
  10 0xc0000000#32

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

-- ### ll/sc: load-linked/store-conditional (real MIPS32 atomic
-- synchronization primitives; see `Types.lean`'s `llBit` docstring for the
-- single-hart simplification). Same addressing/alignment as lw/sw.

/-- Step through `p` from `s` exactly `n` times, threading the state;
`none` if any intermediate step halts. Used below to exercise `ll`/`sc`
multi-instruction sequences (ordinary fallthrough, no delay slot involved). -/
private def stepN (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (stepState p s).bind (stepN p n)

-- `ll`: loads like `lw` and sets `llBit`.
#guard nextRegEq (step (prog1 (.ll 8#32 9#32 4#32)) memTestState) 9 0x8001ff00#32
#guard nextLlBitEq (step (prog1 (.ll 8#32 9#32 4#32)) memTestState) true
-- misaligned ll/sc → addressError, same as lw/sw
#guard isHaltAddr (step (prog1 (.ll 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) 0x10010001#32
#guard isHaltAddr (step (prog1 (.sc 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)])) 0x10010001#32

-- `sc` right after a matching `ll` succeeds: writes 1 to `$rt` and the store
-- commits.
private def llscAddr : W32 := 0x10010000#32
private def llscSuccessProg : Program := buildProg textBase [.ll 8#32 9#32 0#32, .sc 8#32 10#32 0#32]
private def llscSuccessState : State := setRegs regs0 [(8, llscAddr), (10, 0xdeadbeef#32)]
#guard (stepN llscSuccessProg 2 llscSuccessState).bind (fun s => readMemWord s llscAddr)
  = some 0xdeadbeef#32
#guard (stepN llscSuccessProg 2 llscSuccessState).bind (fun s => some (readReg s 10))
  = some 1#32
#guard (stepN llscSuccessProg 2 llscSuccessState).bind (fun s => some s.llBit) = some false

-- `sc` after an intervening `sw` to *any* address (not just the `ll`'s own
-- address) fails: writes 0, the store does not commit, memory unchanged.
private def llscOtherAddr : W32 := 0x20000000#32
private def llscFailProg : Program :=
  buildProg textBase [.ll 8#32 9#32 0#32, .sw 11#32 12#32 0#32, .sc 8#32 10#32 0#32]
private def llscFailState : State :=
  setRegs regs0 [(8, llscAddr), (10, 0xdeadbeef#32), (11, llscOtherAddr), (12, 0x5555#32)]
#guard (stepN llscFailProg 3 llscFailState).bind (fun s => some (readReg s 10)) = some 0#32
#guard (stepN llscFailProg 3 llscFailState).bind (fun s => some s.llBit) = some false
-- the `ll`'s own address was never written by `sc` (it reads back as the
-- zero-fill default, not the attempted `0xdeadbeef` store)
#guard (stepN llscFailProg 3 llscFailState).bind (fun s => readMemWord s llscAddr) = some 0#32
-- the intervening `sw` itself did commit, to its own (different) address
#guard (stepN llscFailProg 3 llscFailState).bind (fun s => readMemWord s llscOtherAddr)
  = some 0x5555#32

-- `sc` always clears `llBit`, even on success, so a second immediate `sc`
-- (no intervening `ll`) fails: writes 0 and does not re-commit a new value.
private def llscDoubleProg : Program :=
  buildProg textBase [.ll 8#32 9#32 0#32, .sc 8#32 10#32 0#32, .sc 8#32 10#32 0#32]
private def llscDoubleState : State := setRegs regs0 [(8, llscAddr), (10, 0xaaaa5555#32)]
#guard (stepN llscDoubleProg 3 llscDoubleState).bind (fun s => some (readReg s 10)) = some 0#32
#guard (stepN llscDoubleProg 3 llscDoubleState).bind (fun s => some s.llBit) = some false
-- memory still holds the first `sc`'s committed value, not the second
-- (failed) attempt's
#guard (stepN llscDoubleProg 3 llscDoubleState).bind (fun s => readMemWord s llscAddr)
  = some 0xaaaa5555#32

-- ### beq/bne/blez/bgtz: taken schedules a `pendingBranch` and falls
-- through to the delay slot; not-taken behaves exactly as before (SPEC-NOTES
-- §9 item 1). `stepThroughDelaySlot` executes the branch *and* an inert
-- delay-slot instruction, landing on the real target.

-- `beq` taken: the branch's own step falls through to `pcNext` with the
-- real target recorded in `pendingBranch`, not yet applied to `pc`.
#guard (match step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false)
-- ... and the delay-slot instruction's own step is what actually lands on
-- the target.
#guard stepThroughDelaySlot textBase (.beq 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 5#32)])
  = some (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32)
#guard nextPendingEq (step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)])) none

#guard stepThroughDelaySlot textBase (.bne 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.bne 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  (textBase + 4#32)

#guard stepThroughDelaySlot textBase (.blez 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 ≤ 0
  = some (textBase + 4#32 + 8#32)
#guard stepThroughDelaySlot textBase (.blez 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 ≤ 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.blez 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 ≤ 0 is false
  (textBase + 4#32)
#guard stepThroughDelaySlot textBase (.bgtz 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 > 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgtz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 > 0 is false
  (textBase + 4#32)

-- ### bltz/bgez/bltzal/bgezal (REGIMM, opcode 0x01): same `pendingBranch`
-- delay-slot scheduling as blez/bgtz, taken/not-taken for each; the `al`
-- variants additionally link `$ra` unconditionally.

-- bltz: taken on a negative $rs, not taken on zero/positive
#guard stepThroughDelaySlot textBase (.bltz 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 < 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bltz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 < 0 is false
  (textBase + 4#32)
#guard nextPcEq (step (prog1 (.bltz 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 < 0 is false
  (textBase + 4#32)

-- bgez: taken on zero/positive $rs, not taken on negative
#guard stepThroughDelaySlot textBase (.bgez 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 >= 0
  = some (textBase + 4#32 + 8#32)
#guard stepThroughDelaySlot textBase (.bgez 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 >= 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgez 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]))  -- -5 >= 0 is false
  (textBase + 4#32)

-- bltzal: link into $ra is unconditional (pc + 8, past the delay slot),
-- whether or not the branch itself is taken.
#guard nextRegEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- taken: -5 < 0
#guard nextRegEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- not taken: 5 < 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bltzal 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))
  (textBase + 4#32)

-- bgezal: same unconditional-link convention as bltzal, >= 0 condition.
#guard nextRegEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- taken: 5 >= 0
#guard nextRegEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- not taken: -5 >= 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bgezal 8#32 2#32) (setRegs regs0 [(8, 5#32)])
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]))
  (textBase + 4#32)

-- ### j/jal: exact targets including top-4-bit preservation from `pc_next`;
-- jal $ra links to `pc + 8` (past the delay slot), not `pc + 4`

private def crossRegionState : State := { regs0 with pc := 0x90400000#32 }
-- `j`'s own step falls through to the delay slot, scheduling the target.
#guard (match step (progAt 0x90400000#32 (.j 0x1000#32)) crossRegionState with
        | .next s => s.pc == 0x90400004#32 && s.pendingBranch == some 0x90004000#32
        | .halt _ => false)
#guard stepThroughDelaySlot 0x90400000#32 (.j 0x1000#32) crossRegionState = some 0x90004000#32
-- `jal`: `$ra` is `pc + 8`, and the target lands the same way as `j` after
-- the delay slot.
#guard nextRegEq (step (progAt 0x90400000#32 (.jal 0x1000#32)) crossRegionState) 31 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jal 0x1000#32) crossRegionState = some 0x90004000#32

-- ### jr/jalr: register-indirect jump/call, same one-delay-slot scheduling
-- as j/jal, but the target comes from a register read. `jr $ra` is the
-- canonical function-return idiom; `jalr $rd, $rs` additionally links `$rd`
-- to `pc + 8`, exactly like `jal`'s link-value convention.

-- `jr`'s own step falls through to the delay slot, scheduling `$rs`'s raw
-- value as the target (no top-4-bit composition, unlike `j`).
#guard (match step (progAt 0x90400000#32 (.jr 8#32)) (setRegs crossRegionState [(8, 0x80020000#32)]) with
        | .next s => s.pc == 0x90400004#32 && s.pendingBranch == some 0x80020000#32
        | .halt _ => false)
#guard stepThroughDelaySlot 0x90400000#32 (.jr 8#32) (setRegs crossRegionState [(8, 0x80020000#32)])
  = some 0x80020000#32
-- the classic `jr $ra` function-return idiom: landing on whatever address
-- was previously linked into `$ra`.
#guard stepThroughDelaySlot textBase (.jr 31#32) (setRegs regs0 [(31, 0x00400040#32)])
  = some 0x00400040#32

-- `jalr $rd, $rs`: `$rd` is `pc + 8` (past the delay slot, same convention
-- as `jal`), and the target lands the same way as `jr` after the delay slot.
#guard nextRegEq (step (progAt 0x90400000#32 (.jalr 8#32 9#32)) (setRegs crossRegionState [(8, 0x80020000#32)]))
  9 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 8#32 9#32) (setRegs crossRegionState [(8, 0x80020000#32)])
  = some 0x80020000#32
-- `jalr $t9, $t9` (rd = rs): the link value overwrites `$rs` only *after*
-- its pre-write value has been captured as the jump target.
#guard nextRegEq (step (progAt 0x90400000#32 (.jalr 9#32 9#32)) (setRegs crossRegionState [(9, 0x80020000#32)]))
  9 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 9#32 9#32) (setRegs crossRegionState [(9, 0x80020000#32)])
  = some 0x80020000#32

-- a `jr` target that isn't 4-byte-aligned is not special-cased: the branch
-- step itself still schedules it as an ordinary `pendingBranch`, and the
-- misalignment only surfaces as the existing `addressError` halt on the
-- *next* fetch attempt, once `pc` actually becomes that value.
#guard stepThroughDelaySlot 0x90400000#32 (.jr 8#32) (setRegs crossRegionState [(8, 0x80020001#32)])
  = some 0x80020001#32
#guard (match stepState (buildProg 0x90400000#32 [.jr 8#32, nopInstr])
          (setRegs crossRegionState [(8, 0x80020001#32)]) with
        | some s1 =>
          (match stepState (buildProg 0x90400000#32 [.jr 8#32, nopInstr]) s1 with
           | some s2 => isHaltAddr (step (buildProg 0x90400000#32 [.jr 8#32, nopInstr]) s2) 0x80020001#32
           | none => false)
        | none => false)

-- ### branch/jump in a delay slot: diagnosable halt, not arbitrary behavior

-- A branch immediately following a *taken* branch (i.e. itself occupying
-- the delay slot) halts rather than silently scheduling/overwriting
-- anything — real MIPS32 leaves this architecturally discouraged/
-- implementation-defined (INSTRUCTION-REF Global rule 3).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
-- A branch following a *not-taken* branch is unaffected (no pending
-- transfer was ever scheduled, so there is no delay slot to be inside).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | some s1 =>
          isNext (step (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
-- `j` right after a taken `beq` halts the same way.
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .j 0x1000#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot (step (buildProg textBase [.beq 8#32 9#32 1#32, .j 0x1000#32]) s1)
        | none => false)
-- `bltz` right after a taken `beq` halts the same way (confirms the REGIMM
-- branches are included in `isBranchLike`).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .bltz 8#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .bltz 8#32 0#32]) s1)
        | none => false)

-- ### syscalls

#guard (stepState (prog1 .syscall) (setRegs regs0 [(2, 1#32), (4, 5#32)])).bind (fun s => some s.out)
  = some "5"
#guard (stepState (prog1 .syscall) (setRegs regs0 [(2, 1#32), (4, 0xfffffffb#32)])).bind (fun s => some s.out)
  = some "-5"
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

-- ### Traps / exceptions (coprocessor 0): teq/tne/tlt/tge/tltu/tgeu/break

private def cp0Eq (r : StepResult) (epc cause status pc : W32) : Bool :=
  match r with
  | .next s => s.cp0Epc == epc && s.cp0Cause == cause && s.cp0Status == status && s.pc == pc
  | .halt _ => false

private def cp0Untouched (r : StepResult) (before : State) : Bool :=
  match r with
  | .next s => s.cp0Epc == before.cp0Epc && s.cp0Cause == before.cp0Cause
                 && s.cp0Status == before.cp0Status
  | .halt _ => false

-- teq: trap-taken from `textBase` sets `EPC = textBase` (the trapping
-- instruction's own address, not `pc + 4`), `Cause.ExcCode = excCodeTr`
-- packed into bits 6..2 (`excCodeTr <<< 2`), `Status.EXL` (bit 1) set, and
-- `pc = exceptionVectorAddr`.
#guard cp0Eq (step (prog1 (.teq 8#32 9#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr
-- teq: trap-not-taken behaves like an ordinary instruction (falls through
-- to `pc + 4`) and leaves all CP0 state untouched.
#guard nextPcEq (step (prog1 (.teq 8#32 9#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32)
#guard cp0Untouched (step (prog1 (.teq 8#32 9#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)])) regs0

-- tne: trap on not-equal (opposite condition from teq)
#guard cp0Eq (step (prog1 (.tne 8#32 9#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr
#guard isNext (step (prog1 (.tne 8#32 9#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))

-- tlt/tge: signed comparison (negative `$rs` is less than positive `$rt`)
#guard cp0Eq (step (prog1 (.tlt 8#32 9#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr  -- -1 < 1
#guard isNext (step (prog1 (.tlt 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 0xffffffff#32)]))  -- 1 < -1 false
#guard cp0Eq (step (prog1 (.tge 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr  -- 1 >= -1
#guard isNext (step (prog1 (.tge 8#32 9#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))  -- -1 >= 1 false

-- tltu/tgeu: unsigned comparison (0xffffffff is the largest unsigned value,
-- so it is never `<u` anything and always `>=u` everything)
#guard isNext (step (prog1 (.tltu 8#32 9#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
#guard cp0Eq (step (prog1 (.tgeu 8#32 9#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr

-- break: unconditional trap, distinct `ExcCode` (`excCodeBp` ≠ `excCodeTr`)
-- from the same starting state/address as the teq case above.
#guard excCodeBp ≠ excCodeTr
#guard cp0Eq (step (prog1 .break) regs0)
  textBase (excCodeBp <<< 2) statusExlMask exceptionVectorAddr

-- a second trap from a nonzero `pc` records that instruction's own address
-- in `EPC`, not `textBase`/`pc + 4`.
private def trapAtState : State := { regs0 with pc := textBase + 0x100#32 }
#guard cp0Eq (step (progAt (textBase + 0x100#32) .break) trapAtState)
  (textBase + 0x100#32) (excCodeBp <<< 2) statusExlMask exceptionVectorAddr

-- exception-vector mechanism "for free": with no handler installed at
-- `exceptionVectorAddr`, the *next* `step` call from the post-trap state
-- naturally hits the existing fetch-failure halt (no instruction recorded
-- there) -- this is `step`'s ordinary `addressError`, not a synthetic
-- "unhandled exception" halt reason.
#guard (match stepState (prog1 .break) regs0 with
        | some s' => isHaltAddr (step (∅ : Program) s') exceptionVectorAddr
        | none => false)

-- if a real handler word *is* present at the vector address, it executes
-- normally after the trap (e.g. an `addi` landing there).
private def vectorHandlerProg : Program :=
  (prog1 .break).insert exceptionVectorAddr (encode (.addi 0#32 8#32 42#32))
#guard (match stepState vectorHandlerProg regs0 with
        | some s' => nextRegEq (step vectorHandlerProg s') 8 42#32
        | none => false)

-- ### Coprocessor 0 (CP0): mfc0/mtc0/eret/wait (docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.10A)

-- mfc0 reads back each of the three real CP0 registers, selected by `rd`
-- (12/13/14 = Status/Cause/EPC).
#guard nextRegEq (step (prog1 (.mfc0 8#32 12#32)) { regs0 with cp0Status := 0x2#32 }) 8 0x2#32
#guard nextRegEq (step (prog1 (.mfc0 8#32 13#32)) { regs0 with cp0Cause := 0x34#32 }) 8 0x34#32
#guard nextRegEq (step (prog1 (.mfc0 8#32 14#32)) { regs0 with cp0Epc := 0x3000#32 }) 8 0x3000#32

-- mtc0 writes each of the three real CP0 registers from a GPR.
#guard (match stepState (prog1 (.mtc0 8#32 12#32)) (setRegs regs0 [(8, 0x2#32)]) with
        | some s' => s'.cp0Status == 0x2#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 13#32)) (setRegs regs0 [(8, 0x34#32)]) with
        | some s' => s'.cp0Cause == 0x34#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 14#32)) (setRegs regs0 [(8, 0x3000#32)]) with
        | some s' => s'.cp0Epc == 0x3000#32
        | none => false)

-- mtc0 then mfc0 round-trips an arbitrary value through each of the three
-- registers (Status/Cause/EPC in turn).
#guard (match stepState (prog1 (.mtc0 8#32 12#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (step (prog1 (.mfc0 9#32 12#32)) { s' with pc := textBase }) 9
            0xabcd#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 13#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (step (prog1 (.mfc0 9#32 13#32)) { s' with pc := textBase }) 9
            0xabcd#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 14#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (step (prog1 (.mfc0 9#32 14#32)) { s' with pc := textBase }) 9
            0xabcd#32
        | none => false)

-- mfc0/mtc0 with an out-of-scope `rd` (this model has no CP0 register other
-- than 12/13/14) halt with `illegalInstruction`, the documented choice over
-- silently reading back `0` or silently dropping the write.
#guard isHaltIllegal (step (prog1 (.mfc0 8#32 0#32)) regs0) (encode (.mfc0 8#32 0#32))
#guard isHaltIllegal (step (prog1 (.mtc0 8#32 0#32)) (setRegs regs0 [(8, 1#32)]))
  (encode (.mtc0 8#32 0#32))

-- eret: restores `pc` from `cp0Epc` and clears `Status.EXL` (bit 1, the same
-- bit `takeException` sets) in a *single* `step` call -- no delay-slot
-- scheduling (`pendingBranch` stays `none`, confirming `eret` bypasses
-- `mkNext` entirely rather than landing one instruction later).
private def eretReadyState : State :=
  { regs0 with cp0Epc := 0x3000#32, cp0Status := statusExlMask, pendingBranch := none }
#guard nextPcEq (step (prog1 .eret) eretReadyState) 0x3000#32
#guard (match stepState (prog1 .eret) eretReadyState with
        | some s' => s'.cp0Status == 0#32 && s'.pendingBranch == none
        | none => false)

-- full round trip: `teq` traps from `textBase` to `exceptionVectorAddr`
-- (confirming `cp0Epc`/`pc` land at the expected places, same as the
-- existing teq tests above), then `eret` placed at the vector returns
-- `pc` exactly to the original trapping instruction's address and clears
-- `Status.EXL`.
private def teqEretProg : Program :=
  ((∅ : Program).insert textBase (encode (.teq 8#32 9#32))).insert exceptionVectorAddr (encode .eret)
#guard (match stepState teqEretProg (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          s1.cp0Epc == textBase && s1.pc == exceptionVectorAddr && s1.cp0Status == statusExlMask &&
            (match stepState teqEretProg s1 with
             | some s2 => s2.pc == textBase && s2.cp0Status == 0#32
             | none => false)
        | none => false)

-- wait: a documented no-op (no interrupt/timer model exists to wait for),
-- falls through to `pc + 4` with all state otherwise untouched.
#guard nextPcEq (step (prog1 .wait) regs0) (textBase + 4#32)
#guard (match stepState (prog1 .wait) regs0 with
        | some s' => s'.cp0Status == regs0.cp0Status && s'.cp0Cause == regs0.cp0Cause
                       && s'.cp0Epc == regs0.cp0Epc
        | none => false)

-- ### Undecodable word → illegalInstruction

-- opcode 0x11 (COP1) is implemented for the fmt/funct combinations decoded
-- in `Instruction.lean`; fmt=0x1f is not one of them, so this word is still
-- genuinely undecodable.
private def badWord : W32 := (0x11#32 <<< 26) ||| (0x1f#32 <<< 21)
private def badProg : Program := (∅ : Program).insert textBase badWord
#guard isHaltIllegal (step badProg regs0) badWord

-- ### Coprocessor 1 (FPU): mtc1/mfc1/lwc1/swc1 raw bit-pattern moves

-- mtc1 then mfc1 round-trips an arbitrary bit pattern through $f3
#guard nextFpRegEq (step (prog1 (.mtc1 8#32 3#32)) (setRegs regs0 [(8, 0x12345678#32)])) 3
  0x12345678#32
#guard (match stepState (prog1 (.mtc1 8#32 3#32)) (setRegs regs0 [(8, 0x12345678#32)]) with
        | some s' => nextRegEq (step (prog1 (.mfc1 9#32 3#32)) { s' with pc := textBase }) 9
            0x12345678#32
        | none => false)

private def fpMemTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32)]) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010004#32 0x3f).insert 0x10010005#32 0x80)
               |>.insert 0x10010006#32 0x00 |>.insert 0x10010007#32 0x00 }  -- 1.0 at offset 4
#guard nextFpRegEq (step (prog1 (.lwc1 8#32 9#32 4#32)) fpMemTestState) 9 0x3f800000#32
#guard (stepState (prog1 (.swc1 8#32 9#32 4#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32)]) [(9, 0x3f800000#32)])).bind
        (fun s' => readMemWord s' 0x10010004#32) = some 0x3f800000#32
-- lwc1/swc1 alignment rules match lw/sw exactly
#guard isHaltAddr (step (prog1 (.lwc1 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]))
  0x10010001#32

-- ### Coprocessor 1 (FPU): add.s/sub.s/mul.s/div.s/mov.s (IEEE-754 single-precision)

-- 1.0 = 0x3f800000, 2.0 = 0x40000000, 3.0 = 0x40400000, 5.0 = 0x40a00000,
-- 6.0 = 0x40c00000 (standard IEEE-754 binary32 bit patterns).
#guard nextFpRegEq (step (prog1 (.addS 10#32 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x40000000#32)])) 10 0x40400000#32  -- 1.0+2.0=3.0
#guard nextFpRegEq (step (prog1 (.subS 10#32 8#32 9#32))
  (setFpRegs regs0 [(8, 0x40a00000#32), (9, 0x40000000#32)])) 10 0x40400000#32  -- 5.0-2.0=3.0
#guard nextFpRegEq (step (prog1 (.mulS 10#32 8#32 9#32))
  (setFpRegs regs0 [(8, 0x40000000#32), (9, 0x40400000#32)])) 10 0x40c00000#32  -- 2.0*3.0=6.0
#guard nextFpRegEq (step (prog1 (.divS 10#32 8#32 9#32))
  (setFpRegs regs0 [(8, 0x40c00000#32), (9, 0x40000000#32)])) 10 0x40400000#32  -- 6.0/2.0=3.0
-- div.s by zero: IEEE-754 Infinity, no trap (SPEC-NOTES §9 item 2 precedent)
#guard isNext (step (prog1 (.divS 10#32 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x00000000#32)]))
#guard nextFpRegEq (step (prog1 (.divS 10#32 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x00000000#32)])) 10 0x7f800000#32  -- 1.0/0.0=+Inf
#guard nextFpRegEq (step (prog1 (.movS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40400000#32)])) 10
  0x40400000#32

-- ### Coprocessor 1 (FPU): cvt.s.w / cvt.w.s numeric conversions

-- cvt.s.w: int bit pattern -> float value; 5 -> 5.0, -5 (0xfffffffb) -> -5.0
#guard nextFpRegEq (step (prog1 (.cvtSW 10#32 8#32)) (setFpRegs regs0 [(8, 5#32)])) 10
  0x40a00000#32
#guard nextFpRegEq (step (prog1 (.cvtSW 10#32 8#32)) (setFpRegs regs0 [(8, 0xfffffffb#32)])) 10
  0xc0a00000#32
-- cvt.w.s: float value -> int bit pattern, truncating toward zero (not
-- rounding); 5.9 (0x40bccccd) -> 5, -5.9 (0xc0bccccd) -> -5
#guard nextFpRegEq (step (prog1 (.cvtWS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40a00000#32)])) 10
  0x00000005#32
#guard nextFpRegEq (step (prog1 (.cvtWS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40bccccd#32)])) 10
  0x00000005#32
#guard nextFpRegEq (step (prog1 (.cvtWS 10#32 8#32)) (setFpRegs regs0 [(8, 0xc0bccccd#32)])) 10
  0xfffffffb#32

-- ### Coprocessor 1 (FPU): c.eq.s/c.lt.s/c.le.s set `fpCondFlag`; bc1t/bc1f branch on it

#guard nextFpCondFlagEq (step (prog1 (.cEqS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x3f800000#32)])) true   -- 1.0 == 1.0
#guard nextFpCondFlagEq (step (prog1 (.cEqS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x40000000#32)])) false  -- 1.0 != 2.0
#guard nextFpCondFlagEq (step (prog1 (.cLtS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x40000000#32)])) true   -- 1.0 < 2.0
#guard nextFpCondFlagEq (step (prog1 (.cLtS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x40000000#32), (9, 0x3f800000#32)])) false  -- 2.0 < 1.0 is false
#guard nextFpCondFlagEq (step (prog1 (.cLeS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x3f800000#32)])) true   -- 1.0 <= 1.0

-- `bc1t`/`bc1f` get the same delay slot as every other branch (dev/v2
-- integration: upgraded from the fpu track's original immediate-jump
-- implementation to match `beq`/`bne`/etc.'s `pendingBranch` scheduling --
-- see `Step.lean`'s `.bc1t`/`.bc1f` cases). Taken: two steps via
-- `stepThroughDelaySlot` land on the target. Not taken: one step is an
-- ordinary fallthrough to `pc + 4`, same as before.
private def fpFlagState (b : Bool) : State := { regs0 with fpCondFlag := b }
#guard stepThroughDelaySlot textBase (.bc1t 3#32) (fpFlagState true) = some (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.bc1t 3#32)) (fpFlagState false)) (textBase + 4#32)
#guard stepThroughDelaySlot textBase (.bc1f 3#32) (fpFlagState false) = some (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.bc1f 3#32)) (fpFlagState true)) (textBase + 4#32)

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
        | .halted .exit s steps => s.out == "12" && steps == 8
        | _ => false)

-- `limitReached`: a two-instruction infinite self-loop
-- (`beq $zero,$zero,-1` with a `nop` delay slot) — with delay slots the
-- loop body is the branch *plus* its delay-slot instruction, so each
-- iteration costs 2 steps, but it still never halts.
private def loopProg : Program := buildProg textBase [.beq 0#32 0#32 0xffff#32, nopInstr]
#guard (match run loopProg regs0 5 with
        | .limitReached _ steps => steps == 5
        | _ => false)
