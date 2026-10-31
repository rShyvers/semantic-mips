import Std.Data.HashMap.Basic
import MipsSim.Word

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
  /-- Byte-addressable, sparse memory. -/
  mem : Std.HashMap W32 UInt8
  /-- Accumulated syscall output. -/
  out : String

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
    mem := ∅
    out := "" }

example : sampleState.pc = textBase := by decide
example : sampleState.regs.size = 32 := by decide
example : sampleState.regs[29]! = spInit := by decide
example : sampleState.out = "" := by decide
#guard sampleState.pc = textBase
#guard sampleState.regs.size = 32
#guard sampleState.regs[29]! = spInit

-- `HaltReason` / `StepResult` sanity
example : HaltReason.exit ≠ HaltReason.arithmeticOverflow := by decide
example : (StepResult.halt HaltReason.exit) = (StepResult.halt HaltReason.exit) := by rfl
