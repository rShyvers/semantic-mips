import Std.Data.HashMap.Basic
import MipsSim.Word
import MipsSim.Types

/-!
# State — hardware operations on `State`

Wave 1 module (DESIGN.md §4, worker B): initial-state construction, register
read/write (with the `$zero`-is-write-ignored rule), instruction fetch, and
byte/halfword/word memory access with MIPS/MARS alignment and big-endian
composition rules (SPEC-NOTES §1,§4,§7; INSTRUCTION-REF Global rules §2,§4,§5).

Depends only on the foundation (`Word`, `Types`); read-only there.
-/

/-- The initial machine state at program counter `pc`: all general-purpose
registers are `0` except `$sp` (register 29), which is seeded with `spInit`;
`hi`/`lo` are `0`; memory is empty; accumulated output is empty. -/
def initialState (pc : W32) : State :=
  { pc := pc
    regs := (Array.replicate 32 (0#32)).set! 29 spInit
    hi := 0#32
    lo := 0#32
    mem := ∅
    out := "" }

/-- Read general-purpose register `i`. Register `0` (`$zero`) always reads as
`0` by construction of `initialState`/`writeReg`, but this also tolerates any
state built otherwise since it just indexes the register array (out-of-range
indices, which should not occur for `Fin 32`, default to `0`). -/
def readReg (s : State) (i : Fin 32) : W32 :=
  s.regs.getD i.val 0#32

/-- Write `v` into general-purpose register `i`, returning the updated state.
Per the `$zero` hardwiring rule (INSTRUCTION-REF Global rule §2), writes to
register `0` are silently ignored and the state is returned unchanged. -/
def writeReg (s : State) (i : Fin 32) (v : W32) : State :=
  if i == 0 then s else { s with regs := s.regs.set! i.val v }

/-- Fetch the instruction word at `pc` from program `p`. Returns `none` if
`pc` is not word-aligned (a multiple of 4) or if no instruction is recorded
at that address (SPEC-NOTES §1; INSTRUCTION-REF Global rule §4). -/
def fetchWord (p : Program) (pc : W32) : Option W32 :=
  if pc.toNat % 4 ≠ 0 then none else p.get? pc

/-- Read a single byte from memory at `addr`. Bytes that have never been
written read as `0` (MARS memory is zero-filled); byte access has no
alignment requirement. -/
def readMemByte (s : State) (addr : W32) : Option UInt8 :=
  some (s.mem.get? addr |>.getD 0)

/-- Read a big-endian halfword (2 bytes) starting at `addr`. The byte at
`addr` is the most-significant byte, the byte at `addr + 1` the
least-significant. Returns `none` if `addr` is not halfword-aligned
(a multiple of 2). Unwritten bytes read as `0`. -/
def readMemHalf (s : State) (addr : W32) : Option W32 :=
  if addr.toNat % 2 ≠ 0 then none
  else
    let hi := s.mem.get? addr |>.getD 0
    let lo := s.mem.get? (addr + 1#32) |>.getD 0
    some ((BitVec.ofNat 32 hi.toNat <<< 8) ||| BitVec.ofNat 32 lo.toNat)

/-- Read a big-endian word (4 bytes) starting at `addr`. The byte at `addr`
is the most-significant byte, down to `addr + 3` as the least-significant.
Returns `none` if `addr` is not word-aligned (a multiple of 4). Unwritten
bytes read as `0`. -/
def readMemWord (s : State) (addr : W32) : Option W32 :=
  if addr.toNat % 4 ≠ 0 then none
  else
    let b0 := s.mem.get? addr |>.getD 0
    let b1 := s.mem.get? (addr + 1#32) |>.getD 0
    let b2 := s.mem.get? (addr + 2#32) |>.getD 0
    let b3 := s.mem.get? (addr + 3#32) |>.getD 0
    some ((BitVec.ofNat 32 b0.toNat <<< 24) ||| (BitVec.ofNat 32 b1.toNat <<< 16) |||
          (BitVec.ofNat 32 b2.toNat <<< 8) ||| BitVec.ofNat 32 b3.toNat)

/-- Write a single byte `v` to memory at `addr`. Byte access has no alignment
requirement, so this always succeeds. -/
def writeMemByte (s : State) (addr : W32) (v : UInt8) : Option State :=
  some { s with mem := s.mem.insert addr v }

/-- Write a big-endian halfword `v` (low 16 bits used) to memory at `addr`:
the most-significant byte goes to `addr`, the least-significant to
`addr + 1`. Returns `none` if `addr` is not halfword-aligned. -/
def writeMemHalf (s : State) (addr : W32) (v : W32) : Option State :=
  if addr.toNat % 2 ≠ 0 then none
  else
    let hi : UInt8 := ((v >>> 8) &&& 0xff#32).toNat.toUInt8
    let lo : UInt8 := (v &&& 0xff#32).toNat.toUInt8
    some { s with mem := (s.mem.insert addr hi).insert (addr + 1#32) lo }

/-- Write a big-endian word `v` to memory at `addr`: the most-significant
byte goes to `addr`, down to the least-significant byte at `addr + 3`.
Returns `none` if `addr` is not word-aligned. -/
def writeMemWord (s : State) (addr : W32) (v : W32) : Option State :=
  if addr.toNat % 4 ≠ 0 then none
  else
    let b0 : UInt8 := ((v >>> 24) &&& 0xff#32).toNat.toUInt8
    let b1 : UInt8 := ((v >>> 16) &&& 0xff#32).toNat.toUInt8
    let b2 : UInt8 := ((v >>> 8) &&& 0xff#32).toNat.toUInt8
    let b3 : UInt8 := (v &&& 0xff#32).toNat.toUInt8
    some { s with
      mem := (((s.mem.insert addr b0).insert (addr + 1#32) b1).insert
                (addr + 2#32) b2).insert (addr + 3#32) b3 }

-- ## Tests

-- `initialState`: sp init, all others zero, pc as given, empty mem/out
example : (initialState textBase).pc = textBase := by decide
example : (initialState textBase).regs[29]! = spInit := by decide
example : (initialState textBase).regs[0]! = 0#32 := by decide
example : (initialState textBase).regs[1]! = 0#32 := by decide
example : (initialState textBase).regs[31]! = 0#32 := by decide
example : (initialState textBase).hi = 0#32 := by decide
example : (initialState textBase).lo = 0#32 := by decide
example : (initialState textBase).out = "" := by decide
-- `Std.HashMap` has no `DecidableEq`, and its operations are not kernel-reducible
-- (`decide`/`rfl`); check emptiness via a lookup checked with `#guard` instead.
#guard (initialState textBase).regs[29]! = spInit
#guard (initialState textBase).regs[0]! = 0#32
#guard (initialState textBase).mem.get? 0x10010000#32 = none

-- `readReg` / `writeReg`: `$zero` write-ignore
example : readReg (initialState textBase) 0 = 0#32 := by decide
example : readReg (writeReg (initialState textBase) 0 0xdeadbeef#32) 0 = 0#32 := by decide
-- writes to `$zero` leave the register file unchanged (checked field-by-field,
-- since `State`/`Std.HashMap` have no `DecidableEq`)
example :
    (writeReg (initialState textBase) 0 0xdeadbeef#32).regs
      = (initialState textBase).regs := by rfl
#guard readReg (initialState textBase) 0 = 0#32
#guard (writeReg (initialState textBase) 0 0xdeadbeef#32).regs = (initialState textBase).regs

-- `writeReg` / `readReg` round-trip for a non-zero register
example : readReg (writeReg (initialState textBase) 8 0x12345678#32) 8 = 0x12345678#32 := by
  decide
#guard readReg (writeReg (initialState textBase) 8 0x12345678#32) 8 = 0x12345678#32

-- writing one register leaves others untouched
example :
    readReg (writeReg (initialState textBase) 8 0x12345678#32) 9 = 0#32 := by decide

-- `fetchWord`: alignment failure, hit, miss
def testProg : Program := (∅ : Program).insert textBase 0xdeadbeef#32
-- alignment failure short-circuits before touching the map, so `decide` works;
-- hit/miss require evaluating the (cbv_opaque) `Std.HashMap`, so those are
-- checked only with `#guard` (compiled evaluation).
example : fetchWord testProg (textBase + 1#32) = none := by decide
#guard fetchWord testProg (textBase + 1#32) = none
#guard fetchWord testProg textBase = some 0xdeadbeef#32
#guard fetchWord testProg (textBase + 4#32) = none

-- `readMemByte`: absent bytes read as 0
#guard readMemByte (initialState textBase) 0x10010000#32 = some 0

-- big-endian composition for half: bytes 0x12,0x34 at a,a+1 → 0x1234
def halfTestState : State :=
  { (initialState textBase) with
      mem := ((∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0x12)
               |>.insert 0x10010001#32 0x34 }
#guard readMemHalf halfTestState 0x10010000#32 = some 0x1234#32

-- half misalignment rejected
example : readMemHalf halfTestState 0x10010001#32 = none := by decide
#guard readMemHalf halfTestState 0x10010001#32 = none

-- big-endian composition for word: bytes 0x12,0x34,0x56,0x78 at a..a+3 → 0x12345678
def wordTestState : State :=
  { (initialState textBase) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0x12).insert 0x10010001#32 0x34
                |>.insert 0x10010002#32 0x56).insert 0x10010003#32 0x78 }
#guard readMemWord wordTestState 0x10010000#32 = some 0x12345678#32

-- word misalignment rejected
example : readMemWord wordTestState 0x10010002#32 = none := by decide
#guard readMemWord wordTestState 0x10010002#32 = none

-- `writeMemByte`/`writeMemHalf`/`writeMemWord` round-trips
-- all memory writes/round-trips exercise the (cbv_opaque) `Std.HashMap`, so
-- these are checked with `#guard` (compiled evaluation) rather than `decide`.
#guard (writeMemByte (initialState textBase) 0x10010000#32 0x7f).bind
        (fun s => readMemByte s 0x10010000#32) = some 0x7f

#guard (writeMemHalf (initialState textBase) 0x10010000#32 0x1234#32).bind
        (fun s => readMemHalf s 0x10010000#32) = some 0x1234#32

#guard (writeMemWord (initialState textBase) 0x10010000#32 0x12345678#32).bind
        (fun s => readMemWord s 0x10010000#32) = some 0x12345678#32

-- big-endian byte layout after a word write: MSB at addr, LSB at addr+3
#guard (writeMemWord (initialState textBase) 0x10010000#32 0x12345678#32).bind
        (fun s => readMemByte s 0x10010000#32) = some 0x12
#guard (writeMemWord (initialState textBase) 0x10010000#32 0x12345678#32).bind
        (fun s => readMemByte s 0x10010003#32) = some 0x78

-- misaligned writes rejected
example : writeMemHalf (initialState textBase) 0x10010001#32 0x1234#32 = none := by decide
example : writeMemWord (initialState textBase) 0x10010001#32 0x12345678#32 = none := by decide
#guard writeMemHalf (initialState textBase) 0x10010001#32 0x1234#32 = none
#guard writeMemWord (initialState textBase) 0x10010001#32 0x12345678#32 = none
