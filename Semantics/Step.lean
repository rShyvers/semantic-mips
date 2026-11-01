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

The coprocessor-1 (FPU) instructions (v1.x addition; single-precision, plus a
v2 double-precision addition -- see `docs/spec/INSTRUCTION-REF.md`'s
floating-point section) are grounded directly in the real MIPS32 ISA, not
MARS; single-precision arithmetic uses Lean core's native `Float32`
(`Init.Data.Float.Float32`), which implements IEEE-754 binary32 exactly,
including `Float32.ofBits`/`Float32.toBits` for the lossless bit-pattern
round-trip `fpRegs` storage needs. Double-precision arithmetic uses Lean
core's native 64-bit `Float` (`Init.Data.Float.Float`, IEEE-754 binary64)
over a *pair* of adjacent `fpRegs` entries, per the classic MIPS32 FR=0
register-pair convention (`$fN` = low 32 bits, `$f(N+1)` = high 32 bits) --
see `doubleOfRegPair`/`regPairOfDouble` below. No FP traps are modeled:
divide-by-zero and invalid operations propagate IEEE-754 Infinity/NaN
naturally, the same precedent as integer `div`/`divu` by zero (SPEC-NOTES §9
item 2).

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

/-- Whether `instr` is one of the twenty branch/jump instructions that
schedule a delay-slot transfer when taken (`beq`,`bne`,`blez`,`bgtz`,
`bltz`,`bgez`,`bltzal`,`bgezal`,`j`,`jal`,`jr`,`jalr`, plus the eight
"branch likely" instructions `beql`,`bnel`,`blezl`,`bgtzl`,`bltzl`,`bgezl`,
`bltzall`,`bgezall` -- real MIPS32, deprecated in MIPS32/removed in Release 6,
MIPS-COVERAGE-GAPS.md §3.3). Used to detect a branch/jump occurring itself
inside another's delay slot (real MIPS32 leaves this architecturally
discouraged/implementation-defined), so `execInstr` can halt with
`HaltReason.branchInDelaySlot` instead of guessing. The branch-likely
instructions are included here on the same footing as every other branch:
this check only ever fires when `s.pendingBranch.isSome`, i.e. when a
previous *taken* branch/jump's delay slot is still pending -- exactly the
same condition under which `beq` in a delay slot halts -- and is unrelated
to `State.squashNext`/the not-taken-branch-likely squash mechanism (see its
docstring in `Types.lean`), which is enforced separately by `run`, one
level above `step`/`execInstr` entirely (see `run`'s docstring below). -/
private def isBranchLike (instr : Instruction) : Bool :=
  match instr with
  | .beq _ _ _ | .bne _ _ _ | .blez _ _ | .bgtz _ _
  | .bltz _ _ | .bgez _ _ | .bltzal _ _ | .bgezal _ _
  | .j _ | .jal _ | .jr _ | .jalr _ _
  | .beql _ _ _ | .bnel _ _ _ | .blezl _ _ | .bgtzl _ _
  | .bltzl _ _ | .bgezl _ _ | .bltzall _ _ | .bgezall _ _ => true
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

/-- Replace byte-position `slot` of `w` with `b`, leaving the other three
byte-positions unchanged. `slot = 0` is the most-significant byte (bits
31..24), `slot = 3` the least-significant (bits 7..0) -- the same
big-endian byte-position convention `State.readMemWord`/`writeMemWord` use
(`slot` is literally "how many word-boundary-crossing bytes this position is
from the top"). Used by `lwl`/`lwr`'s partial-register merge (`docs/spec/
INSTRUCTION-REF.md`'s unaligned-memory-access section). -/
private def setByteSlot (w : W32) (slot : Nat) (b : UInt8) : W32 :=
  let shift := (3 - slot) * 8
  let mask : W32 := 0xff#32 <<< shift
  (w &&& ~~~mask) ||| (zeroExtByte b <<< shift)

/-- Extract byte-position `slot` of `w` (same convention as `setByteSlot`).
Used by `swl`/`swr`'s partial-memory-store byte extraction. -/
private def getByteSlot (w : W32) (slot : Nat) : UInt8 :=
  let shift := (3 - slot) * 8
  ((w >>> shift) &&& 0xff#32).toNat.toUInt8

/-- Sign-extend the low byte of a register value to 32 bits (for `seb`).
Same technique as `signExtByte`, but operating directly on a `W32` register
value rather than a `UInt8` loaded from memory. -/
private def signExtLowByte (w : W32) : W32 :=
  (w.extractLsb 7 0).signExtend 32

/-- A `W32` with the low `n` bits set and all higher bits clear (`n = 0..32`).
Used by `ext`/`ins` to mask out a `size`-bit field. Built as `(1 <<< n) - 1`:
for `n = 32`, `1 <<< 32` wraps to `0` in a 32-bit `BitVec` (hardware shift
semantics, `BitVec.shiftLeft`), so `0 - 1` wraps to `0xffffffff` -- exactly
the all-ones mask a full-word field needs, with no separate case split. -/
private def lowBitsMask (n : Nat) : W32 :=
  ((1#32) <<< n) - 1#32

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

/-- `round.w.s`'s numeric conversion: round `f` to the nearest integer via
Lean core's `Float32.round` (`roundf`, ties away from zero \u2014 see
`Instruction.roundWS`'s docstring for why this isn't ties-to-even), then
clamp/convert to `Int32` the same way `intBitsOfFloatTrunc` does. -/
private def intBitsOfFloatRound (f : Float32) : W32 :=
  f.round.toInt32.toBitVec

/-- `ceil.w.s`'s numeric conversion: round `f` toward +Infinity
(`Float32.ceil`, `ceilf`), then clamp/convert to `Int32`. -/
private def intBitsOfFloatCeil (f : Float32) : W32 :=
  f.ceil.toInt32.toBitVec

/-- `floor.w.s`'s numeric conversion: round `f` toward -Infinity
(`Float32.floor`, `floorf`), then clamp/convert to `Int32`. -/
private def intBitsOfFloatFloor (f : Float32) : W32 :=
  f.floor.toInt32.toBitVec

-- ### Double-precision (`.d`) register-pair bit-pattern composition
--
-- Classic MIPS32 FR=0 convention (this project's `fpRegs : Array W32`
-- already follows it): a double value in assembly register `$fN` occupies
-- the *pair* of adjacent 32-bit FPRs `fpRegs[n]` (low 32 bits) and
-- `fpRegs[n+1]` (high 32 bits). `doubleOfRegPair`/`regPairOfDouble` compose/
-- decompose that pair into/from Lean core's 64-bit `Float`, mirroring
-- `floatOfBits`/`bitsOfFloat`'s raw-bit-pattern round-trip above but for
-- `Float.ofBits`/`Float.toBits` (`Init.Data.Float.Float`) instead of
-- `Float32.ofBits`/`Float32.toBits`. Public (not `private`): used by both
-- `execInstr`'s double-precision cases below and available to `StepSpec`
-- reasoning about double-precision results.

/-- Compose the raw 64-bit bit pattern of a double-precision value from an
FPR register pair `(lo, hi)` -- `lo` is the low 32 bits (the register named
`$fN` in assembly), `hi` is the high 32 bits (`$f(N+1)`) -- into a `Float`
via Lean core's `Float.ofBits : UInt64 → Float`. Real MIPS32 requires `N`
to be even for double operands; this is not checked/enforced here, the
function just follows the register-pair convention when composing. -/
def doubleOfRegPair (lo hi : W32) : Float :=
  Float.ofBits (hi ++ lo : BitVec 64).toNat.toUInt64

/-- Inverse of `doubleOfRegPair`: decompose `f`'s raw 64-bit bit pattern
(`Float.toBits`) into an FPR register pair `(lo, hi)` -- `lo` (low 32 bits)
goes in `$fN`, `hi` (high 32 bits) goes in `$f(N+1)`. -/
def regPairOfDouble (f : Float) : W32 × W32 :=
  let bits : BitVec 64 := BitVec.ofNat 64 f.toBits.toNat
  (bits.extractLsb 31 0, bits.extractLsb 63 32)

/-- `cvt.d.w`'s numeric conversion: read `w`'s bit pattern as a 32-bit
two's-complement int (`Int32.ofBitVec`), then convert that integer *value*
to the nearest `Float` (`Int32.toFloat`, exact for every `Int32` -- binary64
has 52 mantissa bits). -/
private def doubleOfIntBits (w : W32) : Float :=
  (Int32.ofBitVec w).toFloat

/-- `cvt.w.d`'s numeric conversion: truncate `f` toward zero to a 32-bit
two's-complement int (`Float.toInt32`, which clamps on overflow and maps
`NaN` to `0`, the double-precision counterpart of `intBitsOfFloatTrunc`),
returned as a raw bit pattern. Same truncating-vs-FCSR-rounding-mode
simplification as `intBitsOfFloatTrunc`/`cvtWS`. -/
private def intBitsOfDoubleTrunc (f : Float) : W32 :=
  f.toInt32.toBitVec

/-- Read the double-precision `Float` held in the FPR pair named by `f` (the
raw 5-bit field of the pair's *low* register, e.g. `fs`/`ft`/`fd` as decoded)
in `s`'s `fpRegs`, composing via `doubleOfRegPair`. -/
private def readDoubleReg (s : State) (f : W32) : Float :=
  doubleOfRegPair (readFpReg s (regIdx f)) (readFpReg s (regIdx (f + 1#32)))

/-- Write double-precision `Float` value `v` into the FPR pair named by `f`
(the low register) in `s`, decomposing via `regPairOfDouble`. -/
private def writeDoubleReg (s : State) (f : W32) (v : Float) : State :=
  let (lo, hi) := regPairOfDouble v
  writeFpReg (writeFpReg s (regIdx f) lo) (regIdx (f + 1#32)) hi

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
  -- R-type rotate (MIPS32r2): bits shifted off the bottom wrap around to the
  -- top, unlike `srl`/`srlv`'s zero-fill on the same input
  -- (docs/spec/MIPS-COVERAGE-GAPS.md section 3.4). `BitVec.rotateRight` already
  -- reduces its shift amount mod the bitvector width, matching the real
  -- MIPS32 `sa`/`$rs & 0x1f` range (0-31) exactly.
  | .rotr rd rt sa =>
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).rotateRight sa.toNat))
  | .rotrv rd rt rs =>
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).rotateRight amt))
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
  -- SPECIAL2 multiply-accumulate (MIPS32): same signed/unsigned 64-bit
  -- product formation as `mult`/`multu` above, but added to (or subtracted
  -- from) the *existing* `{hi,lo}` pair instead of overwriting it. The
  -- 64-bit add/subtract is plain `BitVec 64` arithmetic, which already
  -- wraps on overflow -- no overflow trap, matching `mult`'s existing
  -- non-trapping precedent (docs/spec/MIPS-COVERAGE-GAPS.md §3.5). `hi ++ lo`
  -- reassembles the current 64-bit accumulator (`hi` is the high word).
  | .madd rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
    let acc64 : BitVec 64 := s.hi ++ s.lo
    let sum64 := acc64 + prod64
    mkNext s { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32 }
  | .maddu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
    let acc64 : BitVec 64 := s.hi ++ s.lo
    let sum64 := acc64 + prod64
    mkNext s { s with lo := sum64.extractLsb 31 0, hi := sum64.extractLsb 63 32 }
  | .msub rs rt =>
    let a := asSigned (readReg s (regIdx rs))
    let b := asSigned (readReg s (regIdx rt))
    let prod64 : BitVec 64 := BitVec.ofInt 64 (a * b)
    let acc64 : BitVec 64 := s.hi ++ s.lo
    let diff64 := acc64 - prod64
    mkNext s { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32 }
  | .msubu rs rt =>
    let a := (readReg s (regIdx rs)).toNat
    let b := (readReg s (regIdx rt)).toNat
    let prod64 : BitVec 64 := BitVec.ofNat 64 (a * b)
    let acc64 : BitVec 64 := s.hi ++ s.lo
    let diff64 := acc64 - prod64
    mkNext s { s with lo := diff64.extractLsb 31 0, hi := diff64.extractLsb 63 32 }
  | .mflo rd => mkNext s (writeReg s (regIdx rd) s.lo)
  | .mfhi rd => mkNext s (writeReg s (regIdx rd) s.hi)
  -- R-type move, write direction: the write-direction counterparts to
  -- `mfhi`/`mflo` above (docs/spec/MIPS-COVERAGE-GAPS.md §3.5).
  | .mthi rs => mkNext s { s with hi := readReg s (regIdx rs) }
  | .mtlo rs => mkNext s { s with lo := readReg s (regIdx rs) }
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
  -- SPECIAL3 BSHFL word-swap-bytes-within-halfwords (MIPS32r2): swap the
  -- two bytes of each 16-bit half of `$rt` independently; the halfwords
  -- themselves stay in their original word positions (not a full 32-bit
  -- byte-reverse -- that's `wsbh` + `rotr 16`, not modeled as a single op).
  | .wsbh rd rt =>
    let v := readReg s (regIdx rt)
    let b0 := v &&& 0xff#32
    let b1 := (v >>> 8) &&& 0xff#32
    let b2 := (v >>> 16) &&& 0xff#32
    let b3 := (v >>> 24) &&& 0xff#32
    let result := (b2 <<< 24) ||| (b3 <<< 16) ||| (b0 <<< 8) ||| b1
    mkNext s (writeReg s (regIdx rd) result)
  -- SPECIAL3 bitfield extract/insert (MIPS32r2;
  -- docs/spec/MIPS-COVERAGE-GAPS.md section 3.4). `pos`/`size` are already the
  -- semantic values (`Instruction.decode` did the raw-field +-1 arithmetic),
  -- so this is pure bit masking -- no special-casing for the real
  -- `pos + size <= 32` hardware constraint, per this track's brief.
  | .ext rt rs pos size =>
    let field := (readReg s (regIdx rs) >>> pos.toNat) &&& lowBitsMask size.toNat
    mkNext s (writeReg s (regIdx rt) field)
  | .ins rt rs pos size =>
    let mask := lowBitsMask size.toNat
    let srcField := (readReg s (regIdx rs) &&& mask) <<< pos.toNat
    let clearMask := ~~~(mask <<< pos.toNat)
    let newVal := (readReg s (regIdx rt) &&& clearMask) ||| srcField
    mkNext s (writeReg s (regIdx rt) newVal)
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
  -- `sync`: real MIPS32 memory-ordering barrier (opcode 0, funct 0x0f;
  -- MD00086 Rev 2.50 §3.2), completing the atomics story alongside `ll`/
  -- `sc` above (`docs/spec/MIPS-COVERAGE-GAPS.md` §3.7). Real hardware
  -- ensures every load/store issued before `sync` completes (as observed
  -- by other processors/coherent I/O) before any issued after it; this
  -- single-hart simulator models no concurrency or out-of-order execution
  -- for such a barrier to order anything against, so `sync` is a documented
  -- no-op that falls through to `pc + 4` via `mkNext`, touching no state at
  -- all -- same convention as `wait` below.
  | .sync => mkNext s s
  -- `synci`: real MIPS32 instruction-cache-flush hint (REGIMM opcode 0x01,
  -- `rt` field 0x1f; MIPS32r2, `docs/spec/MIPS-COVERAGE-GAPS.md` §3.7),
  -- used by self-modifying code / JIT compilers to flush a stale
  -- instruction-cache line after writing new code bytes. Computes the same
  -- effective address as `lw`/`sw` for architectural fidelity, but this
  -- simulator has no instruction-cache model at all, so the address is
  -- never read from or written to memory -- a documented no-op that falls
  -- through to `pc + 4` via `mkNext`, touching no state at all (not even a
  -- memory read).
  | .synci rs imm =>
    let _addr := readReg s (regIdx rs) + signExt16 imm
    mkNext s s
  -- `lwl`/`lwr`/`swl`/`swr`: real MIPS32 classic (pre-r6) unaligned
  -- load/store pair (MD00086 Rev 2.50 §3.2, Table 3-4; `docs/spec/
  -- MIPS-COVERAGE-GAPS.md` §3.6). Unlike `lw`/`sw`, `addr` has no alignment
  -- requirement -- `readMemByte`/`writeMemByte` are already total, so none
  -- of these four cases can halt. `off = addr.toNat % 4` selects how many
  -- bytes straddle the word boundary; the `.getD` fallback on every
  -- `readMemByte`/`writeMemByte` result is never actually exercised (those
  -- helpers always return `some`), it just discharges the `Option` they
  -- still return. See `docs/spec/INSTRUCTION-REF.md`'s dedicated section
  -- for the worked byte-position example this case-split implements.
  | .lwl rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let off := addr.toNat % 4
    let old := readReg s (regIdx rt)
    let b0 := (readMemByte s addr).getD 0
    let v :=
      match off with
      | 0 =>
        let b1 := (readMemByte s (addr + 1#32)).getD 0
        let b2 := (readMemByte s (addr + 2#32)).getD 0
        let b3 := (readMemByte s (addr + 3#32)).getD 0
        setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2) 3 b3
      | 1 =>
        let b1 := (readMemByte s (addr + 1#32)).getD 0
        let b2 := (readMemByte s (addr + 2#32)).getD 0
        setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2
      | 2 =>
        let b1 := (readMemByte s (addr + 1#32)).getD 0
        setByteSlot (setByteSlot old 0 b0) 1 b1
      | _ =>  -- off = 3 (Nat match needs a default; addr.toNat % 4 is always < 4)
        setByteSlot old 0 b0
    mkNext s (writeReg s (regIdx rt) v)
  | .lwr rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let off := addr.toNat % 4
    let old := readReg s (regIdx rt)
    let v :=
      match off with
      | 0 =>
        let b3 := (readMemByte s addr).getD 0
        setByteSlot old 3 b3
      | 1 =>
        let b2 := (readMemByte s (addr - 1#32)).getD 0
        let b3 := (readMemByte s addr).getD 0
        setByteSlot (setByteSlot old 2 b2) 3 b3
      | 2 =>
        let b1 := (readMemByte s (addr - 2#32)).getD 0
        let b2 := (readMemByte s (addr - 1#32)).getD 0
        let b3 := (readMemByte s addr).getD 0
        setByteSlot (setByteSlot (setByteSlot old 1 b1) 2 b2) 3 b3
      | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
        let b0 := (readMemByte s (addr - 3#32)).getD 0
        let b1 := (readMemByte s (addr - 2#32)).getD 0
        let b2 := (readMemByte s (addr - 1#32)).getD 0
        let b3 := (readMemByte s addr).getD 0
        setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2) 3 b3
    mkNext s (writeReg s (regIdx rt) v)
  -- `swl`/`swr` are store-class, so (like `sw`/`sh`/`swc1`) they clear
  -- `llBit` -- see the module docstring's `ll`/`sc` paragraph.
  | .swl rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let off := addr.toNat % 4
    let v := readReg s (regIdx rt)
    let s1 := (writeMemByte s addr (getByteSlot v 0)).getD s
    let s' :=
      match off with
      | 0 =>
        let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlot v 1)).getD s1
        let s3 := (writeMemByte s2 (addr + 2#32) (getByteSlot v 2)).getD s2
        (writeMemByte s3 (addr + 3#32) (getByteSlot v 3)).getD s3
      | 1 =>
        let s2 := (writeMemByte s1 (addr + 1#32) (getByteSlot v 1)).getD s1
        (writeMemByte s2 (addr + 2#32) (getByteSlot v 2)).getD s2
      | 2 => (writeMemByte s1 (addr + 1#32) (getByteSlot v 1)).getD s1
      | _ => s1  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
    mkNext s { s' with llBit := false }
  | .swr rs rt imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let off := addr.toNat % 4
    let v := readReg s (regIdx rt)
    let s' :=
      match off with
      | 0 => (writeMemByte s addr (getByteSlot v 3)).getD s
      | 1 =>
        let s1 := (writeMemByte s (addr - 1#32) (getByteSlot v 2)).getD s
        (writeMemByte s1 addr (getByteSlot v 3)).getD s1
      | 2 =>
        let s1 := (writeMemByte s (addr - 2#32) (getByteSlot v 1)).getD s
        let s2 := (writeMemByte s1 (addr - 1#32) (getByteSlot v 2)).getD s1
        (writeMemByte s2 addr (getByteSlot v 3)).getD s2
      | _ =>  -- off = 3 (and unreachable default; addr.toNat % 4 is always < 4)
        let s1 := (writeMemByte s (addr - 3#32) (getByteSlot v 0)).getD s
        let s2 := (writeMemByte s1 (addr - 2#32) (getByteSlot v 1)).getD s1
        let s3 := (writeMemByte s2 (addr - 1#32) (getByteSlot v 2)).getD s2
        (writeMemByte s3 addr (getByteSlot v 3)).getD s3
    mkNext s { s' with llBit := false }
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
  -- "Branch likely" family (real MIPS32; deprecated in MIPS32, removed in
  -- Release 6 -- MD00086 Rev 2.50 §3.2, Table 3-10, p. 28;
  -- docs/spec/MIPS-COVERAGE-GAPS.md §3.3). Architecturally different from
  -- every other branch/jump above: a **taken** branch-likely behaves
  -- exactly like its non-likely counterpart (falls through to `pcNext`,
  -- schedules the real target in `pendingBranch` -- the delay slot
  -- executes normally). A **not-taken** branch-likely does *not* fall
  -- through normally: it sets `State.squashNext := true` and leaves `pc`
  -- at `pcNext` (the delay-slot instruction's own address) -- `run`'s `go`
  -- loop (see its docstring below) is what actually skips that
  -- instruction's fetch/decode/execution on the *next* iteration, advancing
  -- `pc` one further word without ever calling `step` on it. `step` itself
  -- is never told about `squashNext` (so this one `execInstr` case is the
  -- only place in this file, other than `run`, that mentions the field at
  -- all). No `mkNext`/`advance` call is used for the not-taken case (unlike the
  -- non-likely branches' `mkNext s s`), since `advance`'s normal
  -- `pendingBranch`-or-`pc+4` logic has no notion of squashing; incoming
  -- `s.pendingBranch` is always `none` here regardless, since `execInstr`'s
  -- `isBranchLike` check above already intercepts (and halts) any
  -- branch-likely instruction reached with a pending transfer already
  -- scheduled.
  | .beql rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, squashNext := true }
  | .bnel rs rt imm =>
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      StepResult.next { s with pc := pcNext, squashNext := true }
    else
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .blezl rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) ≤ 0 then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, squashNext := true }
  | .bgtzl rs imm =>
    let pcNext := s.pc + 4#32
    if 0 < asSigned (readReg s (regIdx rs)) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, squashNext := true }
  | .bltzl rs imm =>
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) < 0 then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, squashNext := true }
  | .bgezl rs imm =>
    let pcNext := s.pc + 4#32
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      StepResult.next { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s with pc := pcNext, squashNext := true }
  | .bltzall rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if asSigned (readReg s (regIdx rs)) < 0 then
      StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s' with pc := pcNext, squashNext := true }
  | .bgezall rs imm =>
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      StepResult.next { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      StepResult.next { s' with pc := pcNext, squashNext := true }
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
  -- `cfc1`/`ctc1`: no FCSR/FIR control-register state is modeled, so these
  -- reuse the same `fpRegs` array as an addressable 32-bit scratch slot
  -- (`Instruction.cfc1`'s docstring) -- same move shape as `mfc1`/`mtc1`,
  -- just a different `rs`-position sub-opcode.
  | .cfc1 rt fs =>
    mkNext s (writeReg s (regIdx rt) (readFpReg s (regIdx fs)))
  | .ctc1 rt fs =>
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
  -- `ldc1`/`sdc1`: two `readMemWord`/`writeMemWord` calls at `addr`/
  -- `addr + 4` (`Instruction.ldc1`'s docstring) instead of dedicated 64-bit
  -- memory helpers -- reuses `readMemWord`/`writeMemWord`'s already-correct
  -- big-endian byte order and (per-half) alignment checking. Big-endian
  -- doubleword order matches the existing big-endian word order: the word
  -- at the lower address (`addr`) is the *more*-significant half, so it
  -- maps to the high register (`$ft+1`); `addr + 4` is the low register
  -- (`$ft`).
  | .ldc1 rs ft imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    match readMemWord s addr, readMemWord s (addr + 4#32) with
    | some hi, some lo =>
      let s' := writeFpReg s (regIdx ft) lo
      mkNext s (writeFpReg s' (regIdx (ft + 1#32)) hi)
    | _, _ => StepResult.halt (.addressError addr)
  | .sdc1 rs ft imm =>
    let addr := readReg s (regIdx rs) + signExt16 imm
    let lo := readFpReg s (regIdx ft)
    let hi := readFpReg s (regIdx (ft + 1#32))
    match writeMemWord s addr hi with
    | none => StepResult.halt (.addressError addr)
    | some s' =>
      match writeMemWord s' (addr + 4#32) lo with
      | none => StepResult.halt (.addressError addr)
      | some s'' => mkNext s { s'' with llBit := false }
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
  | .sqrtS fd fs =>
    let v := (floatOfBits (readFpReg s (regIdx fs))).sqrt
    mkNext s (writeFpReg s (regIdx fd) (bitsOfFloat v))
  -- `abs.s`/`neg.s`: raw sign-bit operations, no `Float32` arithmetic
  -- involved (`Instruction.absS`/`negS`'s docstrings).
  | .absS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs) &&& 0x7fffffff#32))
  | .negS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs) ^^^ 0x80000000#32))
  | .roundWS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (intBitsOfFloatRound (floatOfBits (readFpReg s (regIdx fs)))))
  -- `trunc.w.s`: numerically identical to `cvtWS` under this model
  -- (`Instruction.truncWS`'s docstring) -- both truncate toward zero.
  | .truncWS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (intBitsOfFloatTrunc (floatOfBits (readFpReg s (regIdx fs)))))
  | .ceilWS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (intBitsOfFloatCeil (floatOfBits (readFpReg s (regIdx fs)))))
  | .floorWS fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (intBitsOfFloatFloor (floatOfBits (readFpReg s (regIdx fs)))))
  | .cFS _ _ =>
    mkNext s { s with fpCondFlag := false }
  -- `c.un.s`/`c.ult.s`/`c.ule.s` are built from `Float32.isNaN` explicitly,
  -- not derived from `<`/`<=` -- those operators already return `false` for
  -- any NaN operand (IEEE-754-correct), so deriving "unordered" from them
  -- would silently be wrong (`Instruction.cUnS`'s docstring).
  | .cUnS fs ft =>
    let a := floatOfBits (readFpReg s (regIdx fs))
    let b := floatOfBits (readFpReg s (regIdx ft))
    mkNext s { s with fpCondFlag := a.isNaN || b.isNaN }
  | .cUeqS fs ft =>
    let a := floatOfBits (readFpReg s (regIdx fs))
    let b := floatOfBits (readFpReg s (regIdx ft))
    mkNext s { s with fpCondFlag := a.beq b || a.isNaN || b.isNaN }
  -- `c.olt.s`/`c.ole.s`: numerically identical to `cLtS`/`cLeS` under this
  -- model (`Instruction.cOltS`/`cOleS`'s docstrings) -- kept as separate
  -- constructors because they are distinct real-MIPS32 encodings.
  | .cOltS fs ft =>
    let flag := (floatOfBits (readFpReg s (regIdx fs))).lt (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s { s with fpCondFlag := flag }
  | .cUltS fs ft =>
    let a := floatOfBits (readFpReg s (regIdx fs))
    let b := floatOfBits (readFpReg s (regIdx ft))
    mkNext s { s with fpCondFlag := a.lt b || a.isNaN || b.isNaN }
  | .cOleS fs ft =>
    let flag := (floatOfBits (readFpReg s (regIdx fs))).le (floatOfBits (readFpReg s (regIdx ft)))
    mkNext s { s with fpCondFlag := flag }
  | .cUleS fs ft =>
    let a := floatOfBits (readFpReg s (regIdx fs))
    let b := floatOfBits (readFpReg s (regIdx ft))
    mkNext s { s with fpCondFlag := a.le b || a.isNaN || b.isNaN }
  -- Double-precision (`.d`): exact same shape as the single-precision cases
  -- above, but operating on `readDoubleReg`/`writeDoubleReg`-composed
  -- 64-bit `Float` values from register pairs instead of `floatOfBits`/
  -- `bitsOfFloat`-composed `Float32` values from single registers (module
  -- docstring; `Instruction.lean`'s double-precision bullet).
  | .addD fd fs ft =>
    let v := (readDoubleReg s fs).add (readDoubleReg s ft)
    mkNext s (writeDoubleReg s fd v)
  | .subD fd fs ft =>
    let v := (readDoubleReg s fs).sub (readDoubleReg s ft)
    mkNext s (writeDoubleReg s fd v)
  | .mulD fd fs ft =>
    let v := (readDoubleReg s fs).mul (readDoubleReg s ft)
    mkNext s (writeDoubleReg s fd v)
  | .divD fd fs ft =>
    -- IEEE-754 division; `$ft == 0` yields +/-Infinity/NaN, never a trap,
    -- same as `divS`.
    let v := (readDoubleReg s fs).div (readDoubleReg s ft)
    mkNext s (writeDoubleReg s fd v)
  -- `mov.d`: raw pair-to-pair bit copy, both 32-bit halves
  -- (`Instruction.movD`'s docstring) -- no `Float` arithmetic involved.
  | .movD fd fs =>
    let s' := writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))
    mkNext s (writeFpReg s' (regIdx (fd + 1#32)) (readFpReg s (regIdx (fs + 1#32))))
  -- `cvt.d.s`/`cvt.s.d`: single<->double numeric conversion, via Lean core's
  -- `Float32.toFloat`/`Float.toFloat32` (`Instruction.cvtDS`/`cvtSD`'s
  -- docstrings).
  | .cvtDS fd fs =>
    mkNext s (writeDoubleReg s fd (floatOfBits (readFpReg s (regIdx fs))).toFloat)
  | .cvtSD fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (bitsOfFloat (readDoubleReg s fs).toFloat32))
  | .cvtDW fd fs =>
    mkNext s (writeDoubleReg s fd (doubleOfIntBits (readFpReg s (regIdx fs))))
  | .cvtWD fd fs =>
    mkNext s (writeFpReg s (regIdx fd) (intBitsOfDoubleTrunc (readDoubleReg s fs)))
  | .cEqD fs ft =>
    let flag := (readDoubleReg s fs).beq (readDoubleReg s ft)
    mkNext s { s with fpCondFlag := flag }
  | .cLtD fs ft =>
    let flag := (readDoubleReg s fs).lt (readDoubleReg s ft)
    mkNext s { s with fpCondFlag := flag }
  | .cLeD fs ft =>
    let flag := (readDoubleReg s fs).le (readDoubleReg s ft)
    mkNext s { s with fpCondFlag := flag }
  | .sqrtD fd fs =>
    mkNext s (writeDoubleReg s fd (readDoubleReg s fs).sqrt)
  -- `abs.d`/`neg.d`: raw sign-bit operations on the **high** half only
  -- (`Instruction.absD`/`negD`'s docstrings) -- a double's sign bit is bit
  -- 63 of the 64-bit value, i.e. bit 31 of the high register; the low
  -- register is copied unchanged, no `Float` arithmetic involved.
  | .absD fd fs =>
    let s' := writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))
    mkNext s (writeFpReg s' (regIdx (fd + 1#32)) (readFpReg s (regIdx (fs + 1#32)) &&& 0x7fffffff#32))
  | .negD fd fs =>
    let s' := writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))
    mkNext s (writeFpReg s' (regIdx (fd + 1#32)) (readFpReg s (regIdx (fs + 1#32)) ^^^ 0x80000000#32))
  | .cFD _ _ =>
    mkNext s { s with fpCondFlag := false }
  | .cUnD fs ft =>
    let a := readDoubleReg s fs
    let b := readDoubleReg s ft
    mkNext s { s with fpCondFlag := a.isNaN || b.isNaN }
  | .cUeqD fs ft =>
    let a := readDoubleReg s fs
    let b := readDoubleReg s ft
    mkNext s { s with fpCondFlag := a.beq b || a.isNaN || b.isNaN }
  | .cOltD fs ft =>
    let flag := (readDoubleReg s fs).lt (readDoubleReg s ft)
    mkNext s { s with fpCondFlag := flag }
  | .cUltD fs ft =>
    let a := readDoubleReg s fs
    let b := readDoubleReg s ft
    mkNext s { s with fpCondFlag := a.lt b || a.isNaN || b.isNaN }
  | .cOleD fs ft =>
    let flag := (readDoubleReg s fs).le (readDoubleReg s ft)
    mkNext s { s with fpCondFlag := flag }
  | .cUleD fs ft =>
    let a := readDoubleReg s fs
    let b := readDoubleReg s ft
    mkNext s { s with fpCondFlag := a.le b || a.isNaN || b.isNaN }
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
  -- Trap-immediate (REGIMM, real MIPS32 ISA; `docs/spec/MIPS-COVERAGE-GAPS.md`
  -- §3.8): same coprocessor-0 trap model as `teq`/`tne`/etc. above, but
  -- comparing `$rs` against a sign-extended 16-bit immediate instead of a
  -- second register. `tgeiu`/`tltiu` sign-extend the immediate to 32 bits
  -- first, then compare the resulting bit pattern as unsigned — same
  -- convention `sltiu` already uses.
  | .teqi rs imm =>
    if readReg s (regIdx rs) == signExt16 imm then takeException s excCodeTr else mkNext s s
  | .tnei rs imm =>
    if readReg s (regIdx rs) ≠ signExt16 imm then takeException s excCodeTr else mkNext s s
  | .tgei rs imm =>
    if asSigned (readReg s (regIdx rs)) ≥ asSigned (signExt16 imm)
    then takeException s excCodeTr else mkNext s s
  | .tgeiu rs imm =>
    if (readReg s (regIdx rs)).toNat ≥ (signExt16 imm).toNat
    then takeException s excCodeTr else mkNext s s
  | .tlti rs imm =>
    if asSigned (readReg s (regIdx rs)) < asSigned (signExt16 imm)
    then takeException s excCodeTr else mkNext s s
  | .tltiu rs imm =>
    if (readReg s (regIdx rs)).toNat < (signExt16 imm).toNat
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
`HaltReason`s rather than partial behavior.

Deliberately does **not** inspect `s.squashNext` at all: `step` is otherwise
unchanged from before the "branch likely" family existed (not touching this
function's behavior keeps every pre-existing `Specs/StepSpec.lean` theorem
about `step` valid with zero changes, since they all reason about a fully
generic `State` with no constraint on `squashNext`). The actual squash
enforcement -- skipping fetch/decode/execution of the instruction sitting
at `pc` when `squashNext` is set -- lives one level up, in `run`'s `go`
loop below, which checks the flag on the *incoming* state before ever
calling `step`. `squashNext` still exists as a `State` field (so the
not-taken branch-likely `execInstr` cases above can set it), `step` just
never reads it back. -/
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
one that produces a halt (if any).

This is also where the "branch likely" family's not-taken squash is
actually enforced (see `State.squashNext`'s docstring in `Types.lean`):
before calling `step` at all, `go` checks the *incoming* state's
`squashNext` flag. If set, the instruction sitting at `pc` is the
nullified delay-slot instruction -- real MIPS32 hardware never fetches or
decodes it -- so `go` skips `step` entirely for this iteration, directly
advancing `pc` by one word, clearing the flag, and consuming one unit of
the step budget (matching real hardware's instruction-issue timing: a
squashed slot still occupies one pipeline cycle, it just has no effect).
This holds even when the word at that address is undecodable garbage --
`step`/`decode` are never even called on it, so no `illegalInstruction`
halt is possible there. Only when `squashNext` is `false` does `go` fall
through to the ordinary `step` call. -/
def run (p : Program) (s₀ : State) (maxSteps : Nat) : RunResult :=
  let rec go : Nat → State → Nat → RunResult
    | 0, s, steps => .limitReached s steps
    | fuel + 1, s, steps =>
      if s.squashNext then
        go fuel { s with pc := s.pc + 4#32, squashNext := false } (steps + 1)
      else
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

/-- Every `State` field except `pc` is unchanged between `s` and `s'`. Used
to confirm a genuinely-no-op instruction (`sync`/`synci`) touches *no*
state at all, not just the few fields any individual existing test happens
to check. -/
private def sameStateExceptPc (s s' : State) : Bool :=
  s'.regs == s.regs && s'.hi == s.hi && s'.lo == s.lo && s'.fpRegs == s.fpRegs &&
    s'.fpCondFlag == s.fpCondFlag && s'.mem == s.mem && s'.out == s.out &&
    s'.pendingBranch == s.pendingBranch && s'.llBit == s.llBit &&
    s'.cp0Status == s.cp0Status && s'.cp0Cause == s.cp0Cause && s'.cp0Epc == s.cp0Epc

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

-- ### madd/maddu/msub/msubu/mthi/mtlo (MIPS32 multiply-accumulate and HI/LO
-- register moves; docs/spec/MIPS-COVERAGE-GAPS.md §3.5). The key property
-- that distinguishes these from mult/multu/mul: starting from a nonzero
-- `seededHiLo` accumulator, the result must be the *sum* (or difference) of
-- the prior accumulator and the product, never just the product alone.

-- madd: positive × positive (product 42, same pair as the plain mult test
-- above) accumulated on top of seededHiLo instead of overwriting it
#guard nextHiLoEq (step (prog1 (.madd 8#32 9#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafef037#32
-- madd: negative × negative (same pair as the mult test whose product is
-- 0x3782dace_9d900000), accumulated onto seededHiLo with a 64-bit carry
-- into the hi word
#guard nextHiLoEq (step (prog1 (.madd 8#32 9#32)) (setRegs seededHiLo [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  0x163099be#32 0x688ef00d#32
-- maddu: unsigned operands > 2^31 (same pair as the multu test above)
#guard nextHiLoEq (step (prog1 (.maddu 8#32 9#32)) (setRegs seededHiLo [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x5b942b40#32 0xad82f00d#32
-- msub: subtracts the product from the prior accumulator (inverse of the
-- positive madd case above)
#guard nextHiLoEq (step (prog1 (.msub 8#32 9#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafeefe3#32
-- msubu: unsigned subtract
#guard nextHiLoEq (step (prog1 (.msubu 8#32 9#32)) (setRegs seededHiLo [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x61c7529e#32 0xe87af00d#32

-- mthi/mtlo: write-direction counterparts to mfhi/mflo. Each sets only its
-- own half, leaving the other half (0 on regs0) untouched
#guard nextHiLoEq (step (prog1 (.mthi 8#32)) (setRegs regs0 [(8, 0x12345678#32)])) 0x12345678#32 0#32
#guard nextHiLoEq (step (prog1 (.mtlo 8#32)) (setRegs regs0 [(8, 0x87654321#32)])) 0#32 0x87654321#32
-- round trip through the register file: mthi $8 then mfhi $9 reads back
-- $8's original value (symmetric for mtlo/mflo)
#guard (match stepState (prog1 (.mthi 8#32)) (setRegs regs0 [(8, 0x12345678#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (step (prog1 (.mfhi 9#32)) s'') 9 0x12345678#32
        | none => false)
#guard (match stepState (prog1 (.mtlo 8#32)) (setRegs regs0 [(8, 0x87654321#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (step (prog1 (.mflo 9#32)) s'') 9 0x87654321#32
        | none => false)

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

-- ### rotr/rotrv/ext/ins/wsbh (MIPS32r2 additions; docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.4)

-- rotr: wrap-around is the whole point -- contrast directly with `srl` on
-- the exact same input (0x80000000 >> 31 would be 1 either way, so use a
-- shamt where zero-fill and wrap-around visibly differ).
#guard nextRegEq (step (prog1 (.rotr 10#32 8#32 4#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x81234567#32  -- rotate right 4: low nibble (0x8) wraps to the top
#guard nextRegEq (step (prog1 (.srl 10#32 8#32 4#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x01234567#32  -- srl on the same input: zero-fills instead of wrapping
#guard nextRegEq (step (prog1 (.rotr 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x12345678#32  -- rotate by 0 is a no-op
#guard nextRegEq (step (prog1 (.rotr 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)]))
  10 1#32  -- rotate right 31 == rotate left 1

-- rotrv: same wrap-around behavior, but the amount comes from a register's
-- low 5 bits (masking case included, mirroring sllv/srlv/srav above).
#guard nextRegEq (step (prog1 (.rotrv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 4#32)]))
  10 0x81234567#32
#guard nextRegEq (step (prog1 (.rotrv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 36#32)]))
  10 0x81234567#32  -- 36 & 0x1f = 4, masks identically to rotrv by 4

-- ext: extract a 10-bit field starting at bit 6 out of a known pattern.
-- 0x12345678 = 0001 0010 0011 0100 0101 0110 0111 1000; bits [15:6]
-- (10 bits starting at pos 6, i.e. (0x12345678 >> 6) & 0x3ff) = 0x159.
#guard nextRegEq (step (prog1 (.ext 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x159#32
-- ext: pos=0, size=32 extracts the whole register unchanged
#guard nextRegEq (step (prog1 (.ext 10#32 8#32 0#32 32#32)) (setRegs regs0 [(8, 0x89abcdef#32)]))
  10 0x89abcdef#32
-- ext: a single bit
#guard nextRegEq (step (prog1 (.ext 10#32 8#32 31#32 1#32)) (setRegs regs0 [(8, 0x80000000#32)]))
  10 1#32

-- ins: insert the low 10 bits of $rs (0x159) at pos 6 into $rt, leaving the
-- bits outside [15:6] unchanged -- round-trips with the `ext` example above.
#guard nextRegEq (step (prog1 (.ins 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0x159#32), (10, 0x12345678#32)]))
  10 0x12345678#32  -- re-inserting the field ext'd out above reproduces the original word
-- ins leaves bits outside the target field unchanged, even when the source
-- register has garbage in its higher bits (only the low `size` bits of $rs
-- are used) and $rt's target field previously held something different.
-- low 10 bits of $rs = 0xfffffc01 & 0x3ff = 0x001, shifted to pos 6 = 0x40;
-- $rt starts at 0, so only that one bit (bit 6) ends up set.
#guard nextRegEq (step (prog1 (.ins 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0xfffffc01#32), (10, 0x00000000#32)]))
  10 0x40#32
-- ext/ins round-trip: ins-ing a field then ext-racting it back gives the
-- original (masked-to-size) value, for an arbitrary field/position.
-- (`prog1` always places its single instruction at `textBase`, so a true
-- two-instruction sequence needs `buildProg`, threading the same program
-- across two `stepState` calls -- the first executes `ins` at `textBase`
-- and advances `pc` to `textBase+4`, where the second call then finds
-- `ext`.)
private def extInsRoundTripProg : Program :=
  buildProg textBase [.ins 10#32 8#32 3#32 7#32, .ext 11#32 10#32 3#32 7#32]
#guard (stepState extInsRoundTripProg (setRegs regs0 [(8, 0x7f#32), (10, 0#32)])).bind
        (fun s' => (stepState extInsRoundTripProg s').map (fun s'' => readReg s'' 11))
  = some 0x7f#32

-- wsbh: swap bytes within each halfword independently, halfwords stay put.
-- 0x12345678 -> halfword0 (0x5678) swaps to 0x7856, halfword1 (0x1234)
-- swaps to 0x3412 -> result 0x34127856.
#guard nextRegEq (step (prog1 (.wsbh 10#32 8#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x34127856#32

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

-- ### lwl/lwr/swl/swr: classic MIPS32 unaligned load/store pair
-- (docs/spec/MIPS-COVERAGE-GAPS.md §3.6; docs/spec/INSTRUCTION-REF.md's
-- dedicated section). `A` below is word-aligned; bytes A..A+7 are
-- 0x11,0x22,...,0x88 so every byte-position merge is individually visible
-- in the resulting word.

private def unalignedBase : W32 := 0x10010000#32

private def unalignedTestState : State :=
  { (setRegs regs0 [(8, unalignedBase)]) with
      mem := (∅ : Std.HashMap W32 UInt8)
                |>.insert (unalignedBase + 0#32) 0x11
                |>.insert (unalignedBase + 1#32) 0x22
                |>.insert (unalignedBase + 2#32) 0x33
                |>.insert (unalignedBase + 3#32) 0x44
                |>.insert (unalignedBase + 4#32) 0x55
                |>.insert (unalignedBase + 5#32) 0x66
                |>.insert (unalignedBase + 6#32) 0x77
                |>.insert (unalignedBase + 7#32) 0x88 }

-- `lwl`: addr % 4 == 0 loads the full word, exactly matching plain `lw`.
#guard nextRegEq (step (prog1 (.lwl 8#32 9#32 0#32)) unalignedTestState) 9 0x11223344#32
#guard nextRegEq (step (prog1 (.lw  8#32 9#32 0#32)) unalignedTestState) 9 0x11223344#32
-- `lwl`: the three misaligned offsets, `$rt`'s untouched low bytes coming
-- from its prior value.
#guard nextRegEq (step (prog1 (.lwl 8#32 9#32 1#32)) (setRegs unalignedTestState [(9, 0x000000ff#32)]))
  9 0x223344ff#32
#guard nextRegEq (step (prog1 (.lwl 8#32 9#32 2#32)) (setRegs unalignedTestState [(9, 0x0000abcd#32)]))
  9 0x3344abcd#32
#guard nextRegEq (step (prog1 (.lwl 8#32 9#32 3#32)) (setRegs unalignedTestState [(9, 0x00112233#32)]))
  9 0x44112233#32
-- `lwl` never halts on a misaligned address (contrast `lw`).
#guard isNext (step (prog1 (.lwl 8#32 9#32 1#32)) unalignedTestState)

-- `lwr`: addr % 4 == 3 loads the full word, exactly matching plain `lw`.
#guard nextRegEq (step (prog1 (.lwr 8#32 9#32 3#32)) unalignedTestState) 9 0x11223344#32
-- `lwr`: the three misaligned offsets, `$rt`'s untouched high bytes coming
-- from its prior value.
#guard nextRegEq (step (prog1 (.lwr 8#32 9#32 0#32)) (setRegs unalignedTestState [(9, 0xaabbcc00#32)]))
  9 0xaabbcc11#32
#guard nextRegEq (step (prog1 (.lwr 8#32 9#32 1#32)) (setRegs unalignedTestState [(9, 0xaabb0000#32)]))
  9 0xaabb1122#32
#guard nextRegEq (step (prog1 (.lwr 8#32 9#32 2#32)) (setRegs unalignedTestState [(9, 0xaa000000#32)]))
  9 0xaa112233#32
-- `lwr` never halts on a misaligned address (contrast `lw`).
#guard isNext (step (prog1 (.lwr 8#32 9#32 1#32)) unalignedTestState)

-- Complementary-pair idiom: `lwl $rt, 1($rs)` then `lwr $rt, 4($rs)`
-- (addresses `A+1` and `A+4`, both unaligned/aligned-boundary-straddling)
-- together reconstruct the unaligned word spanning bytes `A+1..A+4`
-- (`0x22334455`), each byte supplied by exactly one of the two instructions.
private def lwlLwrIdiomProg : Program :=
  buildProg textBase [.lwl 8#32 9#32 1#32, .lwr 8#32 9#32 4#32]
#guard (stepN lwlLwrIdiomProg 2 unalignedTestState).bind (fun s => some (readReg s 9))
  = some 0x22334455#32

-- `swl`: addr % 4 == 0 stores the full word, exactly matching plain `sw`.
private def swTestState : State := setRegs regs0 [(8, unalignedBase), (9, 0xaabbccdd#32)]
#guard (stepState (prog1 (.swl 8#32 9#32 0#32)) swTestState).bind (fun s => readMemWord s unalignedBase)
  = some 0xaabbccdd#32
#guard (stepState (prog1 (.sw  8#32 9#32 0#32)) swTestState).bind (fun s => readMemWord s unalignedBase)
  = some 0xaabbccdd#32
-- `swl`: the three misaligned offsets store only the top `4 - off` bytes,
-- starting at `addr`; bytes before `addr` (and after the stored run) are
-- untouched (read back as the zero-fill default).
#guard (stepState (prog1 (.swl 8#32 9#32 1#32)) swTestState).bind
    (fun s => some (readMemByte s (unalignedBase+1#32), readMemByte s (unalignedBase+2#32),
                     readMemByte s (unalignedBase+3#32), readMemByte s (unalignedBase+4#32)))
  = some (some 0xaa, some 0xbb, some 0xcc, some 0)
#guard (stepState (prog1 (.swl 8#32 9#32 2#32)) swTestState).bind
    (fun s => some (readMemByte s (unalignedBase+2#32), readMemByte s (unalignedBase+3#32)))
  = some (some 0xaa, some 0xbb)
#guard (stepState (prog1 (.swl 8#32 9#32 3#32)) swTestState).bind
    (fun s => readMemByte s (unalignedBase+3#32)) = some 0xaa
-- `swl` never halts on a misaligned address (contrast `sw`), and clears
-- `llBit` like every other store-class instruction.
#guard isNext (step (prog1 (.swl 8#32 9#32 1#32)) swTestState)
#guard (stepState (prog1 (.swl 8#32 9#32 1#32)) { swTestState with llBit := true }).bind
    (fun s => some s.llBit) = some false

-- `swr`: addr % 4 == 3 stores the full word, exactly matching plain `sw`.
#guard (stepState (prog1 (.swr 8#32 9#32 3#32)) swTestState).bind (fun s => readMemWord s unalignedBase)
  = some 0xaabbccdd#32
-- `swr`: the three misaligned offsets store only the bottom `off + 1`
-- bytes, ending at `addr`.
#guard (stepState (prog1 (.swr 8#32 9#32 0#32)) swTestState).bind
    (fun s => readMemByte s unalignedBase) = some 0xdd
#guard (stepState (prog1 (.swr 8#32 9#32 1#32)) swTestState).bind
    (fun s => some (readMemByte s unalignedBase, readMemByte s (unalignedBase+1#32)))
  = some (some 0xcc, some 0xdd)
#guard (stepState (prog1 (.swr 8#32 9#32 2#32)) swTestState).bind
    (fun s => some (readMemByte s unalignedBase, readMemByte s (unalignedBase+1#32),
                     readMemByte s (unalignedBase+2#32)))
  = some (some 0xbb, some 0xcc, some 0xdd)
-- `swr` never halts on a misaligned address (contrast `sw`), and clears
-- `llBit` like every other store-class instruction.
#guard isNext (step (prog1 (.swr 8#32 9#32 1#32)) swTestState)
#guard (stepState (prog1 (.swr 8#32 9#32 1#32)) { swTestState with llBit := true }).bind
    (fun s => some s.llBit) = some false

-- Complementary-pair idiom: `swl $rt, 1($rs)` then `swr $rt, 4($rs)`
-- together store every byte of `$rt` into the unaligned word spanning
-- `A+1..A+4`, exactly once each.
private def swlSwrIdiomProg : Program :=
  buildProg textBase [.swl 8#32 9#32 1#32, .swr 8#32 9#32 4#32]
#guard (stepN swlSwrIdiomProg 2 swTestState).bind
    (fun s => some (readMemByte s (unalignedBase+1#32), readMemByte s (unalignedBase+2#32),
                     readMemByte s (unalignedBase+3#32), readMemByte s (unalignedBase+4#32)))
  = some (some 0xaa, some 0xbb, some 0xcc, some 0xdd)

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

-- ### beql/bnel/blezl/bgtzl/bltzl/bgezl/bltzall/bgezall: "branch likely"
-- family (real MIPS32; deprecated in MIPS32, removed in Release 6 --
-- MIPS-COVERAGE-GAPS.md \u00a73.3). This is the one family in this file that is
-- architecturally *not* a `pendingBranch` variant: a **taken** instance
-- behaves exactly like its non-likely counterpart (`stepThroughDelaySlot`,
-- same as `beq`/`bltz` above); a **not-taken** instance instead squashes
-- (nullifies) its own delay-slot instruction -- `step` never fetches,
-- decodes, or executes whatever word sits there, even if it is
-- undecodable garbage.

-- `beql` taken: identical two-step shape to `beq` taken.
#guard stepThroughDelaySlot textBase (.beql 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 5#32)])
  = some (textBase + 4#32 + 12#32)
-- `beql` not taken: the branch's own step falls through to `pcNext` (the
-- delay-slot instruction's own address) with `squashNext` set and *no*
-- `pendingBranch` scheduled -- unlike the non-likely `beq`'s not-taken
-- case (`mkNext s s`, an ordinary ignorable fallthrough), this flags the
-- next instruction to be skipped rather than executed.
#guard (match step (prog1 (.beql 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.squashNext == true && s.pendingBranch == none
        | .halt _ => false)

-- The key behavioral difference from every other branch in this codebase:
-- when not taken, the delay-slot instruction is skipped entirely -- *even
-- when it is an undecodable garbage word that would otherwise halt with
-- `illegalInstruction`* -- because real hardware never even looks at it.
-- The actual skip is enforced by `run` (not a bare `step` call -- see
-- `run`'s docstring), so this needs `run` with a 2-step budget: step 1 is
-- the not-taken `beql` itself (sets `squashNext`), step 2 is `run`
-- consuming the squashed slot directly without ever calling `step` on it.
private def squashGarbageWord : W32 := (0x11#32 <<< 26) ||| (0x1f#32 <<< 21)  -- undecodable: COP1 fmt 0x1f is not MF/MT/BC1/S/W
private def beqlNotTakenGarbageProg : Program :=
  ((∅ : Program).insert textBase (encode (.beql 8#32 9#32 3#32))).insert (textBase + 4#32) squashGarbageWord
#guard (match run beqlNotTakenGarbageProg (setRegs regs0 [(8, 5#32), (9, 6#32)]) 2 with
        | .limitReached s2 steps => steps == 2 && s2.pc == textBase + 8#32 && s2.squashNext == false
        | .halted _ _ _ => false)  -- must NOT halt (e.g. illegalInstruction) on the squashed garbage word

-- `bnel`: opposite polarity to `beql`, same mechanism.
#guard stepThroughDelaySlot textBase (.bnel 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 4#32 + 12#32)
#guard (match step (prog1 (.bnel 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.squashNext == true && s.pendingBranch == none
        | .halt _ => false)

-- `blezl`/`bgtzl`: same conditions as `blez`/`bgtz`, squash instead of
-- ordinary fallthrough when not taken.
#guard stepThroughDelaySlot textBase (.blezl 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 \u2264 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.blezl 8#32 2#32)) (setRegs regs0 [(8, 5#32)]) with  -- 5 \u2264 0 is false
        | .next s => s.pc == textBase + 4#32 && s.squashNext == true
        | .halt _ => false)
#guard stepThroughDelaySlot textBase (.bgtzl 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 > 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgtzl 8#32 2#32)) (setRegs regs0 [(8, 0#32)]) with  -- 0 > 0 is false
        | .next s => s.pc == textBase + 4#32 && s.squashNext == true
        | .halt _ => false)

-- `bltzl`/`bgezl` (REGIMM): same conditions as `bltz`/`bgez`.
#guard stepThroughDelaySlot textBase (.bltzl 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 < 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bltzl 8#32 2#32)) (setRegs regs0 [(8, 0#32)]) with  -- 0 < 0 is false
        | .next s => s.pc == textBase + 4#32 && s.squashNext == true
        | .halt _ => false)
#guard stepThroughDelaySlot textBase (.bgezl 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 >= 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgezl 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]) with  -- -5>=0 false
        | .next s => s.pc == textBase + 4#32 && s.squashNext == true
        | .halt _ => false)

-- `bltzall`/`bgezall` (REGIMM): same unconditional-`$ra`-link convention as
-- `bltzal`/`bgezal` -- the link happens whether the branch is taken or
-- squashed.
#guard nextRegEq (step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- taken: -5 < 0
#guard nextRegEq (step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- squashed: 5 < 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bltzall 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.squashNext == true
        | .halt _ => false)
#guard nextRegEq (step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- taken: 5 >= 0
#guard nextRegEq (step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- squashed: -5 >= 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bgezall 8#32 2#32) (setRegs regs0 [(8, 5#32)])
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.squashNext == true
        | .halt _ => false)

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
-- `beql` right after a taken `beq` halts the same way (confirms the
-- branch-likely family is included in `isBranchLike`, same `pendingBranch`
-- condition as every other branch/jump -- unrelated to `squashNext`).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beql 8#32 8#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .beql 8#32 8#32 0#32]) s1)
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

-- ### Trap-immediate family (REGIMM, real MIPS32 ISA;
-- docs/spec/MIPS-COVERAGE-GAPS.md §3.8): teqi/tnei/tgei/tgeiu/tlti/tltiu,
-- the sign-extended-16-bit-immediate counterpart of teq/tne/tlt/tge/tltu/tgeu.

-- teqi: trap-taken when `$rs == sext16(imm)`; trap-not-taken behaves like
-- an ordinary instruction and leaves all CP0 state untouched.
#guard cp0Eq (step (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 5#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr
#guard isNext (step (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 6#32)]))
#guard cp0Untouched (step (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 6#32)])) regs0

-- tnei: trap on not-equal (opposite condition from teqi)
#guard cp0Eq (step (prog1 (.tnei 8#32 5#32)) (setRegs regs0 [(8, 6#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr
#guard isNext (step (prog1 (.tnei 8#32 5#32)) (setRegs regs0 [(8, 5#32)]))

-- tgei/tlti: signed comparison against `sext16(imm)`; imm = 0xffff sign-
-- extends to -1.
#guard cp0Eq (step (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr  -- -1 >= -1
#guard isNext (step (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 0xfffffffe#32)]))  -- -2 >= -1 false
#guard cp0Eq (step (prog1 (.tlti 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr  -- -1 < 1
#guard isNext (step (prog1 (.tlti 8#32 1#32)) (setRegs regs0 [(8, 1#32)]))  -- 1 < 1 false

-- tgeiu/tltiu: the immediate is sign-extended to 32 bits first, *then* the
-- comparison is unsigned on the resulting bit pattern -- same convention
-- `sltiu` already uses. Edge case where the signed and unsigned
-- interpretations of the same `$rs` bit pattern disagree: $rs = 0xffffffff
-- (signed -1, unsigned max) against imm = 1 (sext16(1) = 1); unsigned
-- 0xffffffff >=u 1 is true (traps), even though a signed read of the same
-- bits (-1 >= 1) would be false.
#guard cp0Eq (step (prog1 (.tgeiu 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr
#guard isNext (step (prog1 (.tltiu 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))  -- 0xffffffff <u 1 false
#guard cp0Eq (step (prog1 (.tltiu 8#32 1#32)) (setRegs regs0 [(8, 0#32)]))
  textBase (excCodeTr <<< 2) statusExlMask exceptionVectorAddr  -- 0 <u 1 true

-- a negative-immediate edge case: imm = 0xffff (sext16 = -1, i.e. bit
-- pattern 0xffffffff) compared *unsigned* against $rs = 1 does NOT trap
-- (1 >=u 0xffffffff is false) under tgeiu, unlike the signed tgei case
-- with the exact same operands (1 >= -1 is true, traps) -- demonstrating
-- tgeiu really does compare unsigned, not just sign-extend-and-reuse-tgei.
#guard isNext (step (prog1 (.tgeiu 8#32 0xffff#32)) (setRegs regs0 [(8, 1#32)]))
#guard cp0Eq (step (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 1#32)]))
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

-- sync: a documented no-op (no concurrency/out-of-order execution exists to
-- order), falls through to `pc + 4` with *every* other field of `State`
-- left exactly as it was (`sameStateExceptPc`, not just a handful of
-- hand-picked fields the way the `wait` check above does).
#guard nextPcEq (step (prog1 .sync) regs0) (textBase + 4#32)
#guard (match stepState (prog1 .sync) regs0 with
        | some s' => sameStateExceptPc regs0 s'
        | none => false)

-- synci: a documented no-op (no instruction-cache model exists to flush),
-- same full-state-untouched check as `sync` above, run from a state with a
-- nonzero base register so the (unused) address computation actually reads
-- something -- confirms the computation itself has no observable effect.
private def synciTestState : State := setRegs regs0 [(8, 0x10010000#32)]
#guard nextPcEq (step (prog1 (.synci 8#32 4#32)) synciTestState) (textBase + 4#32)
#guard (match stepState (prog1 (.synci 8#32 4#32)) synciTestState with
        | some s' => sameStateExceptPc synciTestState s'
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

-- ### Coprocessor 1 (FPU): cfc1/ctc1 (control-register move, scratch-slot model)

-- ctc1 then cfc1 round-trips an arbitrary bit pattern through the shared
-- `fpRegs` scratch slot (register 31, standing in for FCSR) -- same shape
-- as the mtc1/mfc1 round-trip above.
#guard nextFpRegEq (step (prog1 (.ctc1 8#32 31#32)) (setRegs regs0 [(8, 0x00000003#32)])) 31
  0x00000003#32
#guard (match stepState (prog1 (.ctc1 8#32 31#32)) (setRegs regs0 [(8, 0x00000003#32)]) with
        | some s' => nextRegEq (step (prog1 (.cfc1 9#32 31#32)) { s' with pc := textBase }) 9
            0x00000003#32
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

-- ### Coprocessor 1 (FPU): sqrt.s/abs.s/neg.s

-- sqrt.s: 4.0 (0x40800000) -> 2.0 (0x40000000)
#guard nextFpRegEq (step (prog1 (.sqrtS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40800000#32)])) 10
  0x40000000#32
-- abs.s: -3.0 (0xc0400000) -> 3.0 (0x40400000); 3.0 -> 3.0 (already positive)
#guard nextFpRegEq (step (prog1 (.absS 10#32 8#32)) (setFpRegs regs0 [(8, 0xc0400000#32)])) 10
  0x40400000#32
#guard nextFpRegEq (step (prog1 (.absS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40400000#32)])) 10
  0x40400000#32
-- neg.s: 3.0 (0x40400000) -> -3.0 (0xc0400000); -3.0 -> 3.0
#guard nextFpRegEq (step (prog1 (.negS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40400000#32)])) 10
  0xc0400000#32
#guard nextFpRegEq (step (prog1 (.negS 10#32 8#32)) (setFpRegs regs0 [(8, 0xc0400000#32)])) 10
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

-- ### Coprocessor 1 (FPU): round.w.s/trunc.w.s/ceil.w.s/floor.w.s

-- 5.9 = 0x40bccccd, -5.9 = 0xc0bccccd (reusing cvt.w.s's test values above)
-- round.w.s: nearest integer, ties away from zero (`Float32.round`/`roundf`,
-- not ties-to-even -- see `Instruction.roundWS`'s docstring); 5.9 -> 6,
-- -5.9 -> -6
#guard nextFpRegEq (step (prog1 (.roundWS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40bccccd#32)])) 10
  0x00000006#32
#guard nextFpRegEq (step (prog1 (.roundWS 10#32 8#32)) (setFpRegs regs0 [(8, 0xc0bccccd#32)])) 10
  0xfffffffa#32
-- round.w.s at an exact tie: 2.5 (0x40200000) -> 3, -2.5 (0xc0200000) -> -3
-- (ties away from zero, not to even -- documented divergence from real
-- MIPS32's ties-to-even default)
#guard nextFpRegEq (step (prog1 (.roundWS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40200000#32)])) 10
  0x00000003#32
#guard nextFpRegEq (step (prog1 (.roundWS 10#32 8#32)) (setFpRegs regs0 [(8, 0xc0200000#32)])) 10
  0xfffffffd#32
-- trunc.w.s: truncate toward zero (identical to cvt.w.s under this model);
-- 5.9 -> 5, -5.9 -> -5
#guard nextFpRegEq (step (prog1 (.truncWS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40bccccd#32)])) 10
  0x00000005#32
#guard nextFpRegEq (step (prog1 (.truncWS 10#32 8#32)) (setFpRegs regs0 [(8, 0xc0bccccd#32)])) 10
  0xfffffffb#32
-- ceil.w.s: round toward +Infinity; 5.9 -> 6, -5.9 -> -5
#guard nextFpRegEq (step (prog1 (.ceilWS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40bccccd#32)])) 10
  0x00000006#32
#guard nextFpRegEq (step (prog1 (.ceilWS 10#32 8#32)) (setFpRegs regs0 [(8, 0xc0bccccd#32)])) 10
  0xfffffffb#32
-- floor.w.s: round toward -Infinity; 5.9 -> 5, -5.9 -> -6
#guard nextFpRegEq (step (prog1 (.floorWS 10#32 8#32)) (setFpRegs regs0 [(8, 0x40bccccd#32)])) 10
  0x00000005#32
#guard nextFpRegEq (step (prog1 (.floorWS 10#32 8#32)) (setFpRegs regs0 [(8, 0xc0bccccd#32)])) 10
  0xfffffffa#32

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

-- ### Coprocessor 1 (FPU): c.f.s/c.un.s/c.ueq.s/c.olt.s/c.ult.s/c.ole.s/c.ule.s

-- quiet NaN = 0x7fc00000
-- c.f.s: always false, regardless of operands (even equal, non-NaN ones)
#guard nextFpCondFlagEq (step (prog1 (.cFS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x3f800000#32)])) false  -- 1.0 vs 1.0
-- c.un.s: true iff either operand is NaN ("unordered")
#guard nextFpCondFlagEq (step (prog1 (.cUnS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x7fc00000#32), (9, 0x3f800000#32)])) true   -- NaN vs 1.0
#guard nextFpCondFlagEq (step (prog1 (.cUnS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x3f800000#32)])) false  -- 1.0 vs 1.0
-- c.ueq.s: equal, or unordered
#guard nextFpCondFlagEq (step (prog1 (.cUeqS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x3f800000#32)])) true   -- 1.0 == 1.0
#guard nextFpCondFlagEq (step (prog1 (.cUeqS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x7fc00000#32), (9, 0x3f800000#32)])) true   -- NaN vs 1.0 (unordered)
#guard nextFpCondFlagEq (step (prog1 (.cUeqS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x40000000#32)])) false  -- 1.0 vs 2.0
-- c.olt.s: ordered and less-than; false (not true!) when either operand is
-- NaN, unlike a plain `<` applied carelessly to the "unordered" case
#guard nextFpCondFlagEq (step (prog1 (.cOltS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x40000000#32)])) true   -- 1.0 < 2.0
#guard nextFpCondFlagEq (step (prog1 (.cOltS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x7fc00000#32), (9, 0x3f800000#32)])) false  -- NaN < 1.0 is false
-- c.ult.s: less-than, or unordered
#guard nextFpCondFlagEq (step (prog1 (.cUltS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x7fc00000#32), (9, 0x3f800000#32)])) true   -- NaN vs 1.0 (unordered)
#guard nextFpCondFlagEq (step (prog1 (.cUltS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x40000000#32), (9, 0x3f800000#32)])) false  -- 2.0 < 1.0 is false, not NaN
-- c.ole.s: ordered and less-or-equal
#guard nextFpCondFlagEq (step (prog1 (.cOleS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x3f800000#32), (9, 0x3f800000#32)])) true   -- 1.0 <= 1.0
#guard nextFpCondFlagEq (step (prog1 (.cOleS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x7fc00000#32), (9, 0x3f800000#32)])) false  -- NaN <= 1.0 is false
-- c.ule.s: less-or-equal, or unordered
#guard nextFpCondFlagEq (step (prog1 (.cUleS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x7fc00000#32), (9, 0x3f800000#32)])) true   -- NaN vs 1.0 (unordered)
#guard nextFpCondFlagEq (step (prog1 (.cUleS 8#32 9#32))
  (setFpRegs regs0 [(8, 0x40000000#32), (9, 0x3f800000#32)])) false  -- 2.0 <= 1.0 is false, not NaN

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

-- ### Coprocessor 1 (FPU), double-precision: ldc1/sdc1 (register-pair doubleword load/store)

-- Register-pair convention: `$fN` (low) / `$f(N+1)` (high). Memory is
-- big-endian doubleword order: the word at the lower address is the *more*
-- significant half (the high register), `addr + 4` is the low register --
-- same convention `readMemWord`/`writeMemWord` already use for single
-- words, extended one level up.
-- 1.0 (double) = hi 0x3ff00000, lo 0x00000000.
private def dpMemTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32)]) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010004#32 0x3f).insert 0x10010005#32 0xf0)
               |>.insert 0x10010006#32 0x00 |>.insert 0x10010007#32 0x00 }
#guard nextFpRegEq (step (prog1 (.ldc1 8#32 9#32 4#32)) dpMemTestState) 9 0x00000000#32    -- $f9 (lo)
#guard nextFpRegEq (step (prog1 (.ldc1 8#32 9#32 4#32)) dpMemTestState) 10 0x3ff00000#32   -- $f10 (hi)
#guard (stepState (prog1 (.sdc1 8#32 9#32 4#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32)]) [(9, 0x00000000#32), (10, 0x3ff00000#32)])).bind
        (fun s' => readMemWord s' 0x10010004#32) = some 0x3ff00000#32   -- hi word at addr (low addr = high half)
#guard (stepState (prog1 (.sdc1 8#32 9#32 4#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32)]) [(9, 0x00000000#32), (10, 0x3ff00000#32)])).bind
        (fun s' => readMemWord s' 0x10010008#32) = some 0x00000000#32   -- lo word at addr+4
-- ldc1/sdc1 alignment rules match lwc1/swc1 exactly (each half independently)
#guard isHaltAddr (step (prog1 (.ldc1 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]))
  0x10010001#32

-- ### Coprocessor 1 (FPU), double-precision: add.d/sub.d/mul.d/div.d/mov.d

-- 1.0 = (lo 0, hi 0x3ff00000), 2.0 = (lo 0, hi 0x40000000),
-- 3.0 = (lo 0, hi 0x40080000), 5.0 = (lo 0, hi 0x40140000),
-- 6.0 = (lo 0, hi 0x40180000) (standard IEEE-754 binary64 bit patterns,
-- hand-computed and cross-checked against Python's `struct.pack('>d', v)`).
#guard nextFpRegEq (step (prog1 (.addD 10#32 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0x40000000#32)])) 10 0#32
#guard nextFpRegEq (step (prog1 (.addD 10#32 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0x40000000#32)])) 11 0x40080000#32  -- 1.0+2.0=3.0
#guard nextFpRegEq (step (prog1 (.subD 10#32 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x40140000#32), (6, 0), (7, 0x40000000#32)])) 11 0x40080000#32  -- 5.0-2.0=3.0
#guard nextFpRegEq (step (prog1 (.mulD 10#32 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x40000000#32), (6, 0), (7, 0x40080000#32)])) 11 0x40180000#32  -- 2.0*3.0=6.0
#guard nextFpRegEq (step (prog1 (.divD 10#32 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x40180000#32), (6, 0), (7, 0x40000000#32)])) 11 0x40080000#32  -- 6.0/2.0=3.0
-- div.d by zero: IEEE-754 Infinity, no trap (same as divS)
#guard nextFpRegEq (step (prog1 (.divD 10#32 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0)])) 11 0x7ff00000#32  -- 1.0/0.0=+Inf
#guard nextFpRegEq (step (prog1 (.movD 10#32 8#32))
  (setFpRegs regs0 [(8, 0), (9, 0x40080000#32)])) 10 0#32
#guard nextFpRegEq (step (prog1 (.movD 10#32 8#32))
  (setFpRegs regs0 [(8, 0), (9, 0x40080000#32)])) 11 0x40080000#32

-- ### Coprocessor 1 (FPU), double-precision: sqrt.d/abs.d/neg.d

-- sqrt.d: 4.0 -> 2.0
#guard nextFpRegEq (step (prog1 (.sqrtD 10#32 8#32))
  (setFpRegs regs0 [(8, 0), (9, 0x40100000#32)])) 11 0x40000000#32
-- abs.d: -3.0 -> 3.0 (sign bit lives in the high half only)
#guard nextFpRegEq (step (prog1 (.absD 10#32 8#32))
  (setFpRegs regs0 [(8, 0), (9, 0xc0080000#32)])) 11 0x40080000#32
#guard nextFpRegEq (step (prog1 (.absD 10#32 8#32))
  (setFpRegs regs0 [(8, 0), (9, 0xc0080000#32)])) 10 0#32  -- low half copied unchanged
-- neg.d: 3.0 -> -3.0; -3.0 -> 3.0
#guard nextFpRegEq (step (prog1 (.negD 10#32 8#32))
  (setFpRegs regs0 [(8, 0), (9, 0x40080000#32)])) 11 0xc0080000#32
#guard nextFpRegEq (step (prog1 (.negD 10#32 8#32))
  (setFpRegs regs0 [(8, 0), (9, 0xc0080000#32)])) 11 0x40080000#32

-- ### Coprocessor 1 (FPU), double-precision: cvt.d.s/cvt.s.d/cvt.d.w/cvt.w.d

-- cvt.d.s: single 1.0 (0x3f800000) -> double 1.0 (lo 0, hi 0x3ff00000)
#guard nextFpRegEq (step (prog1 (.cvtDS 10#32 8#32)) (setFpRegs regs0 [(8, 0x3f800000#32)])) 10 0#32
#guard nextFpRegEq (step (prog1 (.cvtDS 10#32 8#32)) (setFpRegs regs0 [(8, 0x3f800000#32)])) 11
  0x3ff00000#32
-- cvt.s.d: double 3.0 (lo 0, hi 0x40080000) -> single 3.0 (0x40400000)
#guard nextFpRegEq (step (prog1 (.cvtSD 10#32 8#32))
  (setFpRegs regs0 [(8, 0), (9, 0x40080000#32)])) 10 0x40400000#32
-- cvt.d.w: int bit pattern -> double value; 5 -> 5.0, -5 (0xfffffffb) -> -5.0
#guard nextFpRegEq (step (prog1 (.cvtDW 10#32 8#32)) (setFpRegs regs0 [(8, 5#32)])) 11
  0x40140000#32
#guard nextFpRegEq (step (prog1 (.cvtDW 10#32 8#32)) (setFpRegs regs0 [(8, 0xfffffffb#32)])) 11
  0xc0140000#32
-- cvt.w.d: double value -> int bit pattern, truncating toward zero;
-- 5.9 (lo 0x9999999a, hi 0x40179999) -> 5, -5.9 (lo 0x9999999a, hi 0xc0179999) -> -5
#guard nextFpRegEq (step (prog1 (.cvtWD 10#32 8#32))
  (setFpRegs regs0 [(8, 0x9999999a#32), (9, 0x40179999#32)])) 10 0x00000005#32
#guard nextFpRegEq (step (prog1 (.cvtWD 10#32 8#32))
  (setFpRegs regs0 [(8, 0x9999999a#32), (9, 0xc0179999#32)])) 10 0xfffffffb#32

-- ### Coprocessor 1 (FPU), double-precision: c.eq.d/c.lt.d/c.le.d and the 7 extra predicates

-- quiet double NaN = (lo 0, hi 0x7ff80000)
#guard nextFpCondFlagEq (step (prog1 (.cEqD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0x3ff00000#32)])) true   -- 1.0 == 1.0
#guard nextFpCondFlagEq (step (prog1 (.cEqD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0x40000000#32)])) false  -- 1.0 != 2.0
#guard nextFpCondFlagEq (step (prog1 (.cLtD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0x40000000#32)])) true   -- 1.0 < 2.0
#guard nextFpCondFlagEq (step (prog1 (.cLeD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0x3ff00000#32)])) true   -- 1.0 <= 1.0
#guard nextFpCondFlagEq (step (prog1 (.cFD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0x3ff00000#32)])) false  -- always false
#guard nextFpCondFlagEq (step (prog1 (.cUnD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x7ff80000#32), (6, 0), (7, 0x3ff00000#32)])) true   -- NaN vs 1.0
#guard nextFpCondFlagEq (step (prog1 (.cUeqD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x7ff80000#32), (6, 0), (7, 0x3ff00000#32)])) true   -- NaN (unordered)
#guard nextFpCondFlagEq (step (prog1 (.cOltD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x7ff80000#32), (6, 0), (7, 0x3ff00000#32)])) false  -- NaN < 1.0 is false
#guard nextFpCondFlagEq (step (prog1 (.cUltD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x7ff80000#32), (6, 0), (7, 0x3ff00000#32)])) true   -- NaN (unordered)
#guard nextFpCondFlagEq (step (prog1 (.cOleD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x3ff00000#32), (6, 0), (7, 0x3ff00000#32)])) true   -- 1.0 <= 1.0
#guard nextFpCondFlagEq (step (prog1 (.cUleD 8#32 6#32))
  (setFpRegs regs0 [(8, 0), (9, 0x7ff80000#32), (6, 0), (7, 0x3ff00000#32)])) true   -- NaN (unordered)

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
