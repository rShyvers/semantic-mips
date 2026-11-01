import Std.Data.HashMap.Basic
import Semantics.Word

/-!
# Types — core simulator datatypes

Foundation module (DESIGN.md §3): `Program`, `State`, `HaltReason`, `StepResult`,
instruction-word constructors, and environment constants. Depends only on `Word`.
-/

/-- A program is a sparse map from program-counter words to raw instruction words. -/
abbrev Program := Std.HashMap W32 W32

/-- The full machine state of the simulator between steps. -/
structure State where
  /-- Program counter. -/
  pc : W32
  /-- General-purpose registers, size 32; index = register number. -/
  regs : Array W32
  /-- `hi` register (mult/div results). -/
  hi : W32
  /-- `lo` register (mult/div results). -/
  lo : W32
  /-- Coprocessor-1 (FPU) single-precision registers `$f0`..`$f31`, size 32;
  index = FP register number. Each holds a raw 32-bit IEEE-754
  single-precision bit pattern (same raw-bit-pattern storage convention as
  `regs`); conversion to/from Lean's `Float32` happens only at the point of
  doing actual arithmetic (`Step.lean`). Double-precision (`$f0`..`$f31`
  used as 16 64-bit pairs) is out of scope for this pass — see
  `docs/spec/INSTRUCTION-REF.md`'s floating-point section. -/
  fpRegs : Array W32
  /-- The single FPU condition flag set by `c.eq.s`/`c.lt.s`/`c.le.s` and
  tested by `bc1t`/`bc1f`. Real MIPS32 has 8 FP condition-code registers
  (`cc` field); this v1.x addition models only `cc = 0`, matching the
  single-flag subset in `docs/spec/INSTRUCTION-REF.md`. -/
  fpCondFlag : Bool
  /-- Byte-addressable, sparse memory. -/
  mem : Std.HashMap W32 UInt8
  /-- Accumulated syscall output. -/
  out : String
  /-- A branch/jump target scheduled by a taken branch or jump
  (`beq`/`bne`/`blez`/`bgtz`/`j`/`jal`) but not yet applied to `pc`. Models
  real MIPS32's architecturally-mandated one-instruction branch delay slot
  (SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3): a taken
  branch/jump leaves `pc` at the delay-slot instruction (`pc + 4`) and
  records its real target here; the *next* step applies it (see
  `Step.lean`'s `advance`). `none` means no transfer is pending — the
  common case, and the only one `initialState` ever produces. -/
  pendingBranch : Option W32 := none
  /-- Set by a **not-taken** branch-likely instruction (`beql`/`bnel`/
  `blezl`/`bgtzl`/`bltzl`/`bgezl`/`bltzall`/`bgezall`, MIPS32 "branch
  likely" family -- real MIPS32, deprecated in MIPS32 and removed in
  Release 6, MD00086 Rev 2.50 §3.2, Table 3-10, p. 28; see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.3 and `docs/spec/INSTRUCTION-REF.md`).
  This is an architecturally different mechanism from `pendingBranch`
  above, not a variant of it: every other branch/jump in this document
  always executes its delay-slot instruction, taken or not -- that is what
  `pendingBranch` models. Branch-likely instructions do not: if *not*
  taken, the delay-slot instruction is architecturally nullified
  ("squashed") -- it is never fetched, decoded, or executed, and control
  falls straight through to `pc + 8` (past both the branch and its
  squashed delay slot). A not-taken branch-likely instruction sets this
  flag and advances `pc` only to `pc + 4` (the squashed instruction's own
  address); `Step.lean`'s `run` loop -- deliberately **not** `step` itself,
  so every pre-existing `step`-level theorem in `Specs/StepSpec.lean`
  stays valid unchanged -- checks this flag on the *incoming* state before
  calling `step` on each iteration and, if set, skips fetch/decode/
  execution of whatever word is sitting at `pc` entirely: it advances `pc`
  by one more word and clears the flag directly, without ever calling
  `step`/`decode` -- regardless of whether that word even decodes to a
  valid instruction. A **taken** branch-likely instruction never touches
  this field at all: it behaves exactly like an ordinary taken branch via
  `pendingBranch` (the delay slot *does* execute in that case). Defaults
  `false`, matching `initialState` (no branch-likely instruction has
  executed yet). -/
  squashNext : Bool := false
  /-- The link bit (`LLbit`) set by `ll` and tested/cleared by `sc` (real
  MIPS32 `ll`/`sc`, MD00086 Rev 2.50 §3.2; see `docs/spec/INSTRUCTION-REF.md`).
  Real hardware clears `LLbit` on `sc` execution (success or failure) and on
  events this single-hart simulator has no notion of (context switches,
  cache-coherence traffic from other cores). The one such event that *is*
  observable without real concurrency, and so is the only one modeled here,
  is architecturally mandated even on a single core: any store instruction
  that executes after `ll` clears `LLbit`, which is what makes a
  subsequent `sc` fail if something else wrote memory in between. Every
  store-class instruction (`sw`, `sh`, `swc1`; this model has no `sb`)
  clears this field as part of its own effect; `sc` also always clears it,
  success or fail. Defaults `false`, matching `initialState` (no `ll` has
  executed yet). -/
  llBit : Bool := false
  /-- Coprocessor 0 `Status` register. This minimal model only ever sets bit
  1 (`EXL`, exception level) when an exception is taken (see `excCodeBp`/
  `excCodeTr` and `exceptionVectorAddr` below); no interrupt-mask bits, mode
  bits, or any other `Status` field are modeled. Out of scope: everything
  else in real CP0 `Status` (IM7..IM0, BEV, ERL, KSU, UM, IE, ...). -/
  cp0Status : W32
  /-- Coprocessor 0 `Cause` register. This minimal model only ever writes the
  `ExcCode` field (real MIPS32 bits 6..2) via `excCodeBp`/`excCodeTr` shifted
  into position; all other `Cause` fields (`BD`, `CE`, `IV`, `WP`, the `IP`
  pending-interrupt bits, ...) are out of scope and always read as whatever
  was last written verbatim (i.e. this field is just "ExcCode << 2" with no
  other bits ever set by this model). -/
  cp0Cause : W32
  /-- Coprocessor 0 `EPC` register: the address of the instruction that
  caused the most recent exception, set on trap/`break` so a (hypothetical,
  out-of-v1-scope) handler at `exceptionVectorAddr` could resume with `eret`.
  `eret` itself is not modeled (no instruction reads this register back). -/
  cp0Epc : W32

/-- Reasons the simulator halts instead of producing a next state. -/
inductive HaltReason where
  /-- Clean exit via syscall 10/17. -/
  | exit
  /-- Fetched/attempted to execute a word that does not decode to a known instruction. -/
  | illegalInstruction (word : W32)
  /-- A memory access was out of range or misaligned. -/
  | addressError (addr : W32)
  /-- An add/sub overflow trap fired (no handler installed in v1). -/
  | arithmeticOverflow
  /-- A branch/jump instruction (`beq`/`bne`/`blez`/`bgtz`/`j`/`jal`) was
  fetched while a previous branch/jump's delay-slot transfer was still
  pending (`State.pendingBranch = some _`) — i.e. a branch/jump occurring
  itself in another's delay slot. Real MIPS32 leaves this
  architecturally discouraged/implementation-defined; rather than pick an
  arbitrary behavior, `step` halts with this reason so the condition stays
  diagnosable (SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3). -/
  | branchInDelaySlot
  deriving Repr, DecidableEq

/-- Result of a single simulation step: either a new state, or a halt. -/
inductive StepResult where
  | next (s : State)
  | halt (r : HaltReason)

/-- Mask `w` to `n` bits and shift it left by `shift`. Internal helper for the
instruction-word constructors below. -/
private def field (n shift : Nat) (w : W32) : W32 :=
  (maskLow n w) <<< shift

/-- Build an R-format instruction word from its fields.
Layout: `rs` bits 25..21, `rt` bits 20..16, `rd` bits 15..11, `shamt` bits 10..6,
`funct` bits 5..0 (opcode field is implicitly 0, as for all R-type instructions). -/
def mkRT (rs rt rd shamt funct : W32) : W32 :=
  field 5 21 rs ||| field 5 16 rt ||| field 5 11 rd ||| field 5 6 shamt ||| field 6 0 funct

/-- Build an I-format instruction word from its fields.
Layout: `opcode` bits 31..26, `rs` bits 25..21, `rt` bits 20..16, `imm` bits 15..0. -/
def mkIT (opcode rs rt imm : W32) : W32 :=
  field 6 26 opcode ||| field 5 21 rs ||| field 5 16 rt ||| field 16 0 imm

/-- Build a J-format instruction word's target field.
Layout: `target` in bits 25..0 (opcode is left as 0; callers combine as needed). -/
def mkJT (target : W32) : W32 :=
  field 26 0 target

/-- Base address of the `.text` segment (MARS default configuration). -/
def textBase : W32 := 0x00400000

/-- Initial value of `$sp` (MARS default configuration). -/
def spInit : W32 := 0x7fffeffc

/-- MIPS32 general exception vector address, used when `Status.BEV = 0` (the
normal, non-bootstrap case) for every exception other than TLB-refill/
XTLB-refill/cache-error (which this v1 model has no notion of, having no
TLB or cache) -- standard MIPS32 architecture constant (MIPS32 Architecture
Reference Manual, Volume III: the System Control Coprocessor, "Exception
Vector Locations" table). This is also the same v1-scope assumption already
named in `docs/spec/INSTRUCTION-REF.md` Global rule 5's discussion of
address-error halts ("no exception handler installed at `0x80000180`"); this
definition makes that address a named, documented constant instead of a
literal repeated at each exception site. -/
def exceptionVectorAddr : W32 := 0x80000180

/-- Coprocessor 0 `Cause` register `ExcCode` value for the `break`
instruction's exception ("Bp" -- Breakpoint), per the standard MIPS32
`Cause` register `ExcCode` field encoding (ExcCode 9). -/
def excCodeBp : W32 := 9

/-- Coprocessor 0 `Cause` register `ExcCode` value for the trap-on-condition
family `teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu` ("Tr" -- Trap), per the standard
MIPS32 `Cause` register `ExcCode` field encoding (ExcCode 13). All six trap
instructions share this one `ExcCode`: real MIPS32 hardware does not
distinguish *which* trap condition fired in `Cause` -- a handler would have
to re-fetch and re-decode the faulting instruction word via `EPC` to tell
them apart. That re-decoding is not modeled here (out of scope: no exception
handler is installed in v1). -/
def excCodeTr : W32 := 13

/-- Coprocessor 0 `Status` register `EXL` (exception level) bit, as a mask
ready to `|||` into `cp0Status`, per the standard MIPS32 `Status` register
bit layout (bit 1). This minimal model sets it on every exception and never
clears it (clearing is normally `eret`'s job; `eret` is out of scope for
v1). -/
def statusExlMask : W32 := 0x2

-- ## Tests

-- `mkRT`: rs=5, rt=6, rd=7, shamt=3, funct=0x20 (add)
-- 000000 00101 00110 00111 00011 100000
example :
    mkRT (5#32) (6#32) (7#32) (3#32) (0x20#32)
      = 0b00000000101001100011100011100000#32 := by decide
#guard mkRT (5#32) (6#32) (7#32) (3#32) (0x20#32)
    = 0b00000000101001100011100011100000#32

-- masking: out-of-range field bits are discarded
example : mkRT (0xff#32) (0#32) (0#32) (0#32) (0#32) = field 5 21 (0xff#32) := by decide

-- `mkIT`: opcode=0x23 (lw), rs=29 ($sp), rt=8 ($t0), imm=0x1234
example :
    mkIT (0x23#32) (29#32) (8#32) (0x1234#32)
      = 0b100011_11101_01000_0001001000110100#32 := by decide
#guard mkIT (0x23#32) (29#32) (8#32) (0x1234#32)
    = 0b100011_11101_01000_0001001000110100#32

-- `mkJT`: target = 0x3ffffff (all 26 bits set)
example : mkJT (0x3ffffff#32) = 0x3ffffff#32 := by decide
#guard mkJT (0xffffffff#32) = 0x3ffffff#32

-- `State` construction and field read-back
def sampleState : State :=
  { pc := textBase
    regs := (Array.replicate 32 (0#32)).set! 29 spInit
    hi := 0#32
    lo := 0#32
    fpRegs := Array.replicate 32 (0#32)
    fpCondFlag := false
    mem := ∅
    out := ""
    cp0Status := 0#32
    cp0Cause := 0#32
    cp0Epc := 0#32 }

example : sampleState.pc = textBase := by decide
example : sampleState.regs.size = 32 := by decide
example : sampleState.regs[29]! = spInit := by decide
example : sampleState.fpRegs.size = 32 := by decide
example : sampleState.fpRegs[0]! = 0#32 := by decide
example : sampleState.fpCondFlag = false := by decide
example : sampleState.out = "" := by decide
#guard sampleState.pc = textBase
#guard sampleState.regs.size = 32
#guard sampleState.regs[29]! = spInit
#guard sampleState.fpRegs.size = 32
#guard sampleState.fpCondFlag = false

-- `HaltReason` / `StepResult` sanity
example : HaltReason.exit ≠ HaltReason.arithmeticOverflow := by decide
example : HaltReason.branchInDelaySlot ≠ HaltReason.arithmeticOverflow := by decide
example : (StepResult.halt HaltReason.exit) = (StepResult.halt HaltReason.exit) := by rfl

-- `State.pendingBranch` defaults to `none` when omitted from a literal
example : sampleState.pendingBranch = none := by decide
#guard sampleState.pendingBranch = none
-- `State.llBit` defaults to `false` when omitted from a literal
example : sampleState.llBit = false := by decide
#guard sampleState.llBit = false
-- `State.squashNext` defaults to `false` when omitted from a literal
example : sampleState.squashNext = false := by decide
#guard sampleState.squashNext = false
-- CP0 fields: `sampleState` reads back the zero-initialized fields; the
-- exception constants are distinct small values as documented.
example : sampleState.cp0Status = 0#32 := by decide
example : sampleState.cp0Cause = 0#32 := by decide
example : sampleState.cp0Epc = 0#32 := by decide
#guard sampleState.cp0Status = 0#32
example : exceptionVectorAddr = 0x80000180#32 := by decide
example : excCodeBp ≠ excCodeTr := by decide
example : excCodeBp = 9#32 := by decide
example : excCodeTr = 13#32 := by decide
example : statusExlMask = 2#32 := by decide
