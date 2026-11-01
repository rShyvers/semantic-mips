/-!
# Word — 32-bit word type and bit-level helpers

Foundation module (DESIGN.md §3). `BitVec 32` is provided by Lean core
(`Init.Data.BitVec`), which is always in scope, so no extra imports are needed.
-/

/-- A 32-bit machine word. -/
abbrev W32 := BitVec 32

/-- Sign-extend the low 16 bits of a word to 32 bits.
Used for I-format immediates (e.g. `addi`, `lw`, `beq` offsets). -/
def signExt16 (w : W32) : W32 :=
  (w.extractLsb 15 0).signExtend 32

/-- Interpret a word as a two's-complement signed integer. -/
def asSigned (w : W32) : Int :=
  w.toInt

/-- Wrap an arbitrary integer into its 32-bit two's-complement representation. -/
def ofInt32 (i : Int) : W32 :=
  BitVec.ofInt 32 i

/-- Zero-extend the low 16 bits of a word to 32 bits.
Used for I-format immediates in logical/unsigned contexts (e.g. `andi`, `ori`, `lui`). -/
def zeroExt16 (w : W32) : W32 :=
  (w.extractLsb 15 0).zeroExtend 32

/-- Take the low `n` bits of a word (as a `W32`), masking off any higher bits.
Used to mask instruction-word fields to their declared widths before shifting. -/
def maskLow (n : Nat) (w : W32) : W32 :=
  w &&& ((1#32 <<< n) - 1#32)

-- ## Tests

-- `signExt16`
example : signExt16 (0x00007fff#32) = 0x00007fff#32 := by decide
example : signExt16 (0x00008000#32) = 0xffff8000#32 := by decide
example : signExt16 (0x0000ffff#32) = 0xffffffff#32 := by decide
#guard signExt16 (0x00007fff#32) = 0x00007fff#32
#guard signExt16 (0x00008000#32) = 0xffff8000#32
#guard signExt16 (0x0000ffff#32) = 0xffffffff#32

-- `asSigned` / `ofInt32` round-trips
example : asSigned (0x00000000#32) = 0 := by decide
example : asSigned (0x00000001#32) = 1 := by decide
example : asSigned (0xffffffff#32) = -1 := by decide
example : asSigned (0x80000000#32) = -(2 ^ 31 : Int) := by decide
example : ofInt32 (-1) = 0xffffffff#32 := by decide
example : ofInt32 ((-2 ^ 31 : Int)) = 0x80000000#32 := by decide
example : ofInt32 (42 : Int) = 42#32 := by decide
-- wrap-around: values outside the 32-bit signed range wrap modulo 2^32
example : ofInt32 ((2 ^ 32 : Int) + 5) = 5#32 := by decide
example : asSigned (ofInt32 (-1)) = -1 := by decide
example : ofInt32 (asSigned (0xdeadbeef#32)) = 0xdeadbeef#32 := by decide
#guard asSigned (0x80000000#32) = -(2 ^ 31 : Int)
#guard ofInt32 (-1 : Int) = 0xffffffff#32

-- `zeroExt16`
example : zeroExt16 (0x0000ffff#32) = 0x0000ffff#32 := by decide
example : zeroExt16 (0xffff8000#32) = 0x00008000#32 := by decide
#guard zeroExt16 (0xffffffff#32) = 0x0000ffff#32

-- `maskLow`
example : maskLow 5 (0xffffffff#32) = 0x1f#32 := by decide
example : maskLow 6 (0b111111#32) = 0b111111#32 := by decide
example : maskLow 5 (0b100000#32) = 0#32 := by decide
#guard maskLow 16 (0xffffffff#32) = 0x0000ffff#32
