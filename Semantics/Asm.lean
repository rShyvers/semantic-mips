import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.Instruction

/-!
# Asm — v1 MIPS assembler

Converts assembler source text for the v1 MIPS subset (DESIGN.md §4) into a
`Program` (`Std.HashMap W32 W32`, PC → instruction word). Builds raw instruction
words directly via `mkRT` / `mkIT` / `mkJT` (Types.lean) — this module does
**not** depend on an `Instruction` enum.

## Supported syntax
- Labels (`name:`), optionally followed by an instruction/directive on the
  same line.
- Directives: `.text`, `.data`, `.word`, `.half`, `.byte`, `.asciiz`, `.space`.
- `#` line comments (honoring `"..."` string literals, so `#` inside an
  `.asciiz` string is not treated as a comment start).
- All v1 real instructions (`docs/spec/INSTRUCTION-REF.md`): R-type arith/
  logic/shift/mult-div/mfhi/mflo, I-type immediate/logic/memory, J-type,
  branches, and `syscall` (zero operands, all fields zero except
  funct = 0x0c, i.e. word `0x0000000C`). Plus the MIPS32/MIPS32r2 additions
  `movn`/`movz` (fit the `rd, rs, rt` R-type shape exactly, table-driven like
  `add`), and `clo`/`clz`/`seb`/`seh` (SPECIAL2/SPECIAL3 opcodes, hand-encoded
  below since they don't fit any existing `RForm`).
- Further MIPS32 additions (docs/spec/MIPS-COVERAGE-GAPS.md section 3.4/3.5):
  `sllv`/`srlv`/`srav` (`rd, rt, rs` -- same opcode-0 shape as `shift` but the
  shift amount is a register, table-driven via a new `.shiftv` `RForm`), and
  `mul` (`rd, rs, rt` -- SPECIAL2-opcoded like `clo`/`clz`, hand-encoded
  alongside them since `rTable` only handles opcode-0 forms); and `jr`/`jalr`
  (real MIPS32 register-indirect jump/call, opcode 0 funct 0x08/0x09,
  hand-encoded below since neither fits any existing `RForm` either --
  `jr $rs` is one-operand, `jalr $rd, $rs` is two-operand with `rd` first per
  real MIPS32 assembly syntax (opposite order from the `rs`-then-`rd` field
  layout); `jalr $rs` -- the one-operand sugar for `jalr $ra, $rs` -- is also
  supported); `madd`/`maddu`/`msub`/`msubu` (`rs, rt` -- same shape as `mult`/
  `div`, but SPECIAL2-opcoded like `mul`, so hand-encoded alongside it); and
  `mthi`/`mtlo` (`rs` -- opcode 0, funct 0x11/0x13, the write-direction
  counterparts to `mfhi`/`mflo`, same one-operand shape as `jr` so
  hand-encoded alongside it).
- MIPS32r2 rotate/bitfield additions (docs/spec/MIPS-COVERAGE-GAPS.md section
  3.4), all hand-encoded alongside `clo`/`clz`/`seb`/`seh` since none fits an
  existing `RForm`: `rotr $rd, $rt, $sa` / `rotrv $rd, $rt, $rs` (same
  `rd, rt, shamt`/`rd, rt, rs` shapes as `shift`/`shiftv`, but overload the
  normally-unused `rs`/`shamt` field to `0x01` to select rotate over `srl`/
  `srlv`); `wsbh $rd, $rt` (same BSHFL family as `seb`/`seh`, sub-field
  `0x02`); `ext $rt, $rs, pos, size` / `ins $rt, $rs, pos, size` (SPECIAL3
  opcode 0x1f, funct 0x00/0x04 -- see `Instruction.lean`'s `.ext`/`.ins`
  docstrings for the `pos`/`size` field-packing details).
- The coprocessor-0 trap/exception family (real MIPS32 ISA, added on top of
  the original v1 set -- see `docs/spec/INSTRUCTION-REF.md`): `teq`/`tne`/
  `tlt`/`tge`/`tltu`/`tgeu` (`rs, rt` operands, same shape as `mult`/`div`),
  and `break` (zero operands, like `syscall`; funct = 0x0d, word
  `0x0000000D`). Plus the immediate-operand trap family
  (docs/spec/MIPS-COVERAGE-GAPS.md section 3.8): `teqi`/`tnei`/`tgei`/
  `tgeiu`/`tlti`/`tltiu` (`rs, imm` operands; REGIMM opcode 0x01, same
  opcode as `bltz`/`bgez`/etc. below, distinguished by the `rt` field).
- `ll`/`sc` (real MIPS32 atomic synchronization primitives, added on top of
  the original v1 set -- see `docs/spec/INSTRUCTION-REF.md`): identical
  `rt, offset(rs)` shape and parsing to `lw`/`sw`, table-driven the same way
  (opcodes 0x30/0x38).
- `lwl`/`lwr`/`swl`/`swr` (real MIPS32 classic, pre-r6 unaligned load/store
  pair, added on top of the original v1 set -- see `docs/spec/
  MIPS-COVERAGE-GAPS.md` section 3.6 and `docs/spec/INSTRUCTION-REF.md`):
  identical `rt, offset(rs)` shape and parsing to `lw`/`sw`, table-driven the
  same way (opcodes 0x22/0x26/0x2a/0x2e).
- Coprocessor-1 (FPU) single-precision subset (docs/spec/INSTRUCTION-REF.md's
  floating-point section): `mtc1`/`mfc1`, `cfc1`/`ctc1`, `lwc1`/`swc1`,
  `add.s`/`sub.s`/`mul.s`/`div.s`, `mov.s`, `sqrt.s`/`abs.s`/`neg.s`,
  `round.w.s`/`trunc.w.s`/`ceil.w.s`/`floor.w.s`, `cvt.s.w`/`cvt.w.s`,
  `c.eq.s`/`c.lt.s`/`c.le.s`/`c.f.s`/`c.un.s`/`c.ueq.s`/`c.olt.s`/`c.ult.s`/
  `c.ole.s`/`c.ule.s`, `bc1t`/`bc1f`.
- Coprocessor-1 (FPU) double-precision subset (v2 addition,
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.9A; `docs/spec/INSTRUCTION-REF.md`'s
  double-precision section): `ldc1`/`sdc1`, `add.d`/`sub.d`/`mul.d`/`div.d`,
  `mov.d`, `sqrt.d`/`abs.d`/`neg.d`, `cvt.d.s`/`cvt.s.d`/`cvt.d.w`/`cvt.w.d`,
  `c.eq.d`/`c.lt.d`/`c.le.d`/`c.f.d`/`c.un.d`/`c.ueq.d`/`c.olt.d`/`c.ult.d`/
  `c.ole.d`/`c.ule.d`. `$fN` operands name the *low* register of the
  register pair the double value occupies (same `$fN` parsing as the
  single-precision instructions above, `parseFpRegister`); the assembler
  does not check/enforce that `N` is even.
- Coprocessor-0 (CP0) register move / execution control (real MIPS32 ISA,
  `docs/spec/MIPS-COVERAGE-GAPS.md` \u00a73.10A; see `Instruction.lean`/
  `Step.lean`): `mfc0 $rt, rd` / `mtc0 $rt, rd` (`rd` is a plain numeric CP0
  register reference, e.g. `mfc0 $t0, 12` \u2014 this model has no named CP0
  register aliases, unlike `$f0`..`$f31` for coprocessor 1), and `eret`/
  `wait` (zero operands, like `break`).
- Pseudo-ops: `li`, `la` (label only — see deviation note below), `move`,
  `nop`, expanded per `vendor/mars-src/PseudoOps.txt`.
- Register names `$zero,$at,$v0,$v1,$a0..$a3,$t0..$t7,$s0..$s7,$t8,$t9,
  $k0,$k1,$gp,$sp,$fp,$ra` plus raw numeric `$0`..`$31`, and FP register names
  `$f0`..`$f31` for the coprocessor-1 instructions.

## Layout
`.text` code words are placed sequentially starting at `textBase` (0x00400000);
`.data` starts at `dataBase` (0x10010000, SPEC-NOTES §1). `.word` aligns the
current segment pointer up to a multiple of 4 before emitting; `.half` aligns
to a multiple of 2; `.byte`/`.asciiz`/`.space` require no alignment. A program
may use either or both segments, and `.text`/`.data` directives may switch
segments more than once.

## Deviation from MARS `la`
MARS's `la` pseudo-op has many address-forms (`la $t,100($t2)`,
`la $t,label+100000($t2)`, a `COMPACT` single-instruction form when the
resolved address fits 16 bits, etc. — see `PseudoOps.txt` lines 249-258).
Per DESIGN.md §4 ("`la` = `li` of a label address"), this assembler supports
exactly `la $rt, label` (register + bare label, two tokens). Since every v1
label address is `>= textBase` or `>= dataBase`, both far above 16 bits, the
general two-instruction `lui $at,hi16 ; ori $rt,$at,lo16` expansion (the same
one MARS uses for non-compact `la`/large `li`) is always exactly correct and
the `COMPACT` single-instruction case can never trigger. Any other `la` form
is a `badOperand` error. (Flagged for the Wave 3 DiffHarness worker: keep the
differential corpus's `la` usage to `la $rt, label`.)
-/

/-- Errors produced by `assemble`. Each case carries a human-readable message
and the 1-based source line number where the problem was detected. -/
inductive AsmError where
  | unknownMnemonic (msg : String) (line : Nat)
  | badRegister (msg : String) (line : Nat)
  | undefinedLabel (msg : String) (line : Nat)
  | badImmediate (msg : String) (line : Nat)
  | badDirective (msg : String) (line : Nat)
  | badOperand (msg : String) (line : Nat)
  | duplicateLabel (msg : String) (line : Nat)
  deriving Repr, DecidableEq

/-- Result of assembling source text: either a `Program` or the first error
encountered. -/
abbrev AsmResult := Except AsmError Program

/-- Base address of the `.data` segment (SPEC-NOTES §1; `textBase` lives in
`Types.lean`). -/
def dataBase : W32 := 0x10010000

/-- `$at` (register 1), the scratch register used by the `li`/`la` two-word
expansion, matching MARS's convention (`PseudoOps.txt`). -/
def atReg : Nat := 1

/-- `$zero`, used as the implicit source for `move`/`li`'s one-word forms. -/
def zeroReg : Nat := 0

-- ====================================================================
-- Tokenizing helpers
-- ====================================================================

private def natToW32 (n : Nat) : W32 := BitVec.ofNat 32 n

private def trimStr (s : String) : String := s.trimAscii.toString

/-- `String.drop`/`.take`/`.dropEnd` return `String.Slice` in this Lean
version; these wrappers convert back to `String` for uniform downstream use. -/
private def dropS (s : String) (n : Nat) : String := (s.drop n).toString
private def takeS (s : String) (n : Nat) : String := (s.take n).toString
private def dropEndS (s : String) (n : Nat) : String := (s.dropEnd n).toString

/-- Strip a `#` line comment, but not one occurring inside a `"..."` string
literal (so `.asciiz "a # b"` keeps its `#`). -/
private def stripComment (l : String) : String := Id.run do
  let mut result : List Char := []
  let mut inStr := false
  let mut esc := false
  for c in l.toList do
    if inStr then
      result := c :: result
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
    else
      if c == '#' then
        break
      else
        if c == '"' then inStr := true
        result := c :: result
  return String.ofList result.reverse

/-- Split a line into an optional label and the remainder (trimmed). -/
private def splitLabel (line : String) : Option String × String :=
  match line.splitOn ":" with
  | [one] => (none, one)
  | first :: rest => (some (trimStr first), trimStr (String.intercalate ":" rest))
  | [] => (none, line)

/-- Split whitespace-separated tokens, dropping empty pieces. -/
private def wsTokens (s : String) : List String :=
  (s.splitToList (·.isWhitespace)).filter (fun t => !t.isEmpty)

/-- Find the index of the first occurrence of `c` in `s`, if any. -/
private def findChar (s : String) (c : Char) : Option Nat :=
  s.toList.findIdx? (· == c)

/-- Find the matching `"` for an opening `"` at the start of `s`, decoding
simple backslash escapes (`\n \t \0 \\ \"`). Returns the decoded content and
the number of source characters consumed (including both quotes). -/
private def scanQuotedString (s : String) : Option (String × Nat) := Id.run do
  let chars := s.toList
  if chars.isEmpty || chars.head! != '"' then
    return none
  let mut out : List Char := []
  let mut i : Nat := 1
  let n := chars.length
  let mut done := false
  let mut ok := false
  while !done && i < n do
    let c := chars[i]!
    if c == '\\' && i + 1 < n then
      let e := chars[i + 1]!
      let decoded :=
        match e with
        | 'n' => '\n'
        | 't' => '\t'
        | '0' => Char.ofNat 0
        | '\\' => '\\'
        | '"' => '"'
        | other => other
      out := decoded :: out
      i := i + 2
    else if c == '"' then
      ok := true
      done := true
      i := i + 1
    else
      out := c :: out
      i := i + 1
  if ok then
    return some (String.ofList out.reverse, i)
  else
    return none

/-- A single parsed source line: optional label, optional mnemonic (`none`
for a label-only or blank line), and its operand tokens. -/
structure ParsedLine where
  label : Option String
  mnemonic : Option String
  operands : List String
  lineNo : Nat

private def parseLine (lineNo : Nat) (rawLine : String) : Except AsmError ParsedLine := do
  let noComment := stripComment rawLine
  let trimmed := trimStr noComment
  if trimmed.isEmpty then
    return { label := none, mnemonic := none, operands := [], lineNo }
  let (label, remRaw) := splitLabel trimmed
  let rem := trimStr remRaw
  if rem.isEmpty then
    return { label, mnemonic := none, operands := [], lineNo }
  -- `.asciiz` needs special handling: its single operand is a quoted string
  -- that may itself contain whitespace/commas.
  if rem.startsWith ".asciiz" then
    let afterMnem := trimStr (dropS rem ".asciiz".length)
    match scanQuotedString afterMnem with
    | some (decoded, _) => return { label, mnemonic := some ".asciiz", operands := [decoded], lineNo }
    | none => throw (.badOperand s!".asciiz expects a quoted string" lineNo)
  else
    let toks := wsTokens rem
    match toks with
    | [] => return { label, mnemonic := none, operands := [], lineNo }
    | mnem :: restToks =>
      let operandStr := String.intercalate " " restToks
      let operands := (operandStr.splitOn ",").map trimStr |>.filter (fun t => !t.isEmpty)
      return { label, mnemonic := some mnem, operands, lineNo }

-- ====================================================================
-- Registers and immediates
-- ====================================================================

private def regTable : List (String × Nat) :=
  [("zero", 0), ("at", 1), ("v0", 2), ("v1", 3),
   ("a0", 4), ("a1", 5), ("a2", 6), ("a3", 7),
   ("t0", 8), ("t1", 9), ("t2", 10), ("t3", 11), ("t4", 12), ("t5", 13), ("t6", 14), ("t7", 15),
   ("s0", 16), ("s1", 17), ("s2", 18), ("s3", 19), ("s4", 20), ("s5", 21), ("s6", 22), ("s7", 23),
   ("t8", 24), ("t9", 25),
   ("k0", 26), ("k1", 27),
   ("gp", 28), ("sp", 29), ("fp", 30), ("ra", 31)]

private def parseRegister (tok : String) (line : Nat) : Except AsmError Nat := do
  if !(tok.startsWith "$") then
    throw (.badRegister s!"register name must start with '$': '{tok}'" line)
  let body := dropS tok 1
  match regTable.find? (fun p => p.1 == body) with
  | some (_, n) => pure n
  | none =>
    match body.toNat? with
    | some n => if n < 32 then pure n else throw (.badRegister s!"register number out of range (0-31): '{tok}'" line)
    | none => throw (.badRegister s!"unknown register: '{tok}'" line)

/-- `$f0`..`$f31`, the coprocessor-1 (FPU) single-precision register names. -/
private def fpRegTable : List (String × Nat) :=
  (List.range 32).map (fun i => (s!"f{i}", i))

/-- Parse an FP register operand. Unlike `parseRegister`, there is no raw
numeric fallback (`$5` is never an FP register) \u2014 FPU operands always use
the `$fN` spelling, matching real MIPS32 assembly syntax. -/
private def parseFpRegister (tok : String) (line : Nat) : Except AsmError Nat := do
  if !(tok.startsWith "$") then
    throw (.badRegister s!"FP register name must start with '$': '{tok}'" line)
  let body := dropS tok 1
  match fpRegTable.find? (fun p => p.1 == body) with
  | some (_, n) => pure n
  | none => throw (.badRegister s!"unknown FP register (expected '$f0'..'$f31'): '{tok}'" line)

/-- Parse a `mfc0`/`mtc0` CP0-register-number operand: a plain numeric
token (`12`, not `$12`) in range 0-31 \u2014 this model has no named CP0
register aliases (`Asm.lean` module docstring), so the operand is always a
raw register number, same convention real MIPS32 assembly uses for `mfc0`/
`mtc0`'s `rd` operand. Only 12/13/14 are semantically meaningful
(`Step.lean` halts on any other value at execution time), but the
assembler accepts the full 0-31 range here, matching the real encoding's
5-bit field. -/
private def parseCp0Register (tok : String) (line : Nat) : Except AsmError Nat := do
  match tok.toNat? with
  | some n => if n < 32 then pure n else throw (.badRegister s!"CP0 register number out of range (0-31): '{tok}'" line)
  | none => throw (.badRegister s!"expected a numeric CP0 register number, got '{tok}'" line)

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseHexNat (s : String) : Option Nat :=
  if s.isEmpty then none
  else
    s.toList.foldl
      (fun acc c => acc.bind fun a => (hexDigit? c).map fun d => a * 16 + d)
      (some 0)

/-- Parse a numeric literal token: decimal (`123`, `-123`) or hex
(`0x1A`, `-0x1A`). -/
private def parseImmediate (tok : String) (line : Nat) : Except AsmError Int := do
  if tok.isEmpty then
    throw (.badImmediate s!"empty immediate" line)
  let neg := tok.startsWith "-"
  let body := if neg then dropS tok 1 else tok
  let valOpt : Option Nat :=
    if body.startsWith "0x" ∨ body.startsWith "0X" then parseHexNat (dropS body 2)
    else body.toNat?
  match valOpt with
  | some n => pure (if neg then -(n : Int) else (n : Int))
  | none => throw (.badImmediate s!"invalid immediate: '{tok}'" line)

/-- Does this token look like a numeric literal (vs. a label reference)? -/
private def looksNumeric (tok : String) : Bool :=
  !tok.isEmpty ∧
    (tok.front.isDigit ∨ (tok.startsWith "-" ∧ tok.length > 1 ∧ (dropS tok 1).front.isDigit))

/-- Parse a `offset(reg)` or `(reg)` memory operand. -/
private def parseMemOperand (tok : String) (line : Nat) : Except AsmError (Int × Nat) := do
  match findChar tok '(' with
  | none => throw (.badOperand s!"expected 'offset(register)' operand, got '{tok}'" line)
  | some i =>
    let immStr := takeS tok i
    let rest := dropS tok (i + 1)
    if !(rest.endsWith ")") then
      throw (.badOperand s!"missing closing ')' in operand '{tok}'" line)
    else
      let regStr := dropEndS rest 1
      let imm ← if immStr.isEmpty then pure (0 : Int) else parseImmediate immStr line
      let reg ← parseRegister regStr line
      pure (imm, reg)

-- ====================================================================
-- Mnemonic classification
-- ====================================================================

private inductive RForm
  | arith3   -- rd, rs, rt
  | shift    -- rd, rt, shamt
  | shiftv   -- rd, rt, rs (variable shift; shamt field unused/0)
  | multdiv  -- rs, rt
  | hilo     -- rd

private inductive IForm
  | arith    -- rt, rs, imm
  | lui      -- rt, imm
  | mem      -- rt, offset(rs)
  | trapImm (rtField : Nat)  -- rs, imm (rt field fixed to the given REGIMM trap selector)

private inductive BForm
  | two          -- rs, rt, target
  | one          -- rs, target (rt field fixed 0, e.g. blez/bgtz)
  | regimm (rt : Nat)  -- rs, target (rt field fixed to the given REGIMM sub-opcode selector)

/-- Static table of R-type mnemonics: (name, funct, form). -/
private def rTable : List (String × Nat × RForm) :=
  [("add", 0x20, .arith3), ("addu", 0x21, .arith3), ("sub", 0x22, .arith3), ("subu", 0x23, .arith3),
   ("and", 0x24, .arith3), ("or", 0x25, .arith3), ("xor", 0x26, .arith3), ("nor", 0x27, .arith3),
   ("slt", 0x2a, .arith3), ("sltu", 0x2b, .arith3),
   ("movn", 0x0b, .arith3), ("movz", 0x0a, .arith3),  -- MIPS32r2; same opcode-0 `rd, rs, rt` shape as `add`
   ("sll", 0x00, .shift), ("srl", 0x02, .shift), ("sra", 0x03, .shift),
   -- Variable shifts (MIPS32; docs/spec/MIPS-COVERAGE-GAPS.md section 3.4):
   -- same opcode-0 `rd, rt, rs` shape as `shift`, but the third operand is a
   -- register (the shift amount), not an immediate shamt.
   ("sllv", 0x04, .shiftv), ("srlv", 0x06, .shiftv), ("srav", 0x07, .shiftv),
   ("mult", 0x18, .multdiv), ("multu", 0x19, .multdiv), ("div", 0x1a, .multdiv), ("divu", 0x1b, .multdiv),
   ("mfhi", 0x10, .hilo), ("mflo", 0x12, .hilo),
   -- Trap-on-condition family (same `rs, rt` shape as `mult`/`div`): real
   -- MIPS32 SPECIAL-opcode funct values (see `Instruction.lean`/
   -- `docs/spec/INSTRUCTION-REF.md`), not MARS-derived.
   ("teq", 0x34, .multdiv), ("tne", 0x36, .multdiv), ("tlt", 0x32, .multdiv),
   ("tge", 0x30, .multdiv), ("tltu", 0x33, .multdiv), ("tgeu", 0x31, .multdiv)]

/-- Static table of I-type mnemonics: (name, opcode, form). -/
private def iTable : List (String × Nat × IForm) :=
  [("addi", 0x08, .arith), ("addiu", 0x09, .arith), ("slti", 0x0a, .arith), ("sltiu", 0x0b, .arith),
   ("andi", 0x0c, .arith), ("ori", 0x0d, .arith), ("xori", 0x0e, .arith),
   ("lui", 0x0f, .lui),
   ("lw", 0x23, .mem), ("sw", 0x2b, .mem), ("lb", 0x20, .mem), ("lbu", 0x24, .mem),
   ("lh", 0x21, .mem), ("lhu", 0x25, .mem), ("sh", 0x29, .mem),
   -- `ll`/`sc`: real MIPS32 atomic synchronization primitives (opcodes
   -- 0x30/0x38; MD00086 Rev 2.50 §3.2), same `rt, offset(rs)` shape as
   -- `lw`/`sw` (see `Instruction.lean`/`docs/spec/INSTRUCTION-REF.md`).
   ("ll", 0x30, .mem), ("sc", 0x38, .mem),
   -- Trap-immediate family (REGIMM, real MIPS32 ISA; opcode 0x01, same
   -- opcode as `bltz`/`bgez`/etc. in `bTable`, distinguished by the `rt`
   -- field -- see `Instruction.lean`/`docs/spec/MIPS-COVERAGE-GAPS.md` §3.8).
   -- Operand shape is `rs, imm` (a plain immediate, not a branch target).
   ("teqi", 0x01, .trapImm 0x0c), ("tnei", 0x01, .trapImm 0x0e),
   ("tgei", 0x01, .trapImm 0x08), ("tgeiu", 0x01, .trapImm 0x09),
   ("tlti", 0x01, .trapImm 0x0a), ("tltiu", 0x01, .trapImm 0x0b),
   -- `lwl`/`lwr`/`swl`/`swr`: real MIPS32 classic (pre-r6) unaligned
   -- load/store pair (opcodes 0x22/0x26/0x2a/0x2e; MD00086 Rev 2.50
   -- §3.2, Table 3-4), same `rt, offset(rs)` shape as `lw`/`sw` (see
   -- `Instruction.lean`/`docs/spec/INSTRUCTION-REF.md`).
   ("lwl", 0x22, .mem), ("lwr", 0x26, .mem), ("swl", 0x2a, .mem), ("swr", 0x2e, .mem)]

/-- Static table of J-type mnemonics: (name, opcode). -/
private def jTable : List (String × Nat) := [("j", 0x02), ("jal", 0x03)]

/-- Static table of branch mnemonics: (name, opcode, form). The REGIMM
zero-comparison branches (`bltz`/`bgez`/`bltzal`/`bgezal`) all share opcode
0x01; the `rt` field (carried in `.regimm`, not a separate opcode) is what
selects which one, per MD00086 Rev 2.50 §3.2, Table 3-2 (see
`Instruction.lean`'s decode/encode and `docs/spec/INSTRUCTION-REF.md`). -/
private def bTable : List (String × Nat × BForm) :=
  [("beq", 0x04, .two), ("bne", 0x05, .two), ("blez", 0x06, .one), ("bgtz", 0x07, .one),
   ("bltz", 0x01, .regimm 0x00), ("bgez", 0x01, .regimm 0x01),
   ("bltzal", 0x01, .regimm 0x10), ("bgezal", 0x01, .regimm 0x11)]

/-- Coprocessor-1 (FPU) mnemonic operand shapes. The static parameters
(`fmt`/`opcode`/`funct`/`tf`) needed to build each instruction's word are
carried directly in the constructor — see `cop1Table` and
`docs/spec/INSTRUCTION-REF.md`'s floating-point section for the exact
encodings (same values as `Instruction.lean`'s `encode`). -/
private inductive Cop1Form
  | moveGpFp (fmt : Nat)        -- mtc1 ($rt,$fs; fmt=4) / mfc1 ($rt,$fs; fmt=0) /
                                -- ctc1 ($rt,$fs; fmt=CT=6) / cfc1 ($rt,$fs; fmt=CF=2)
  | mem (opcode : Nat)          -- lwc1 ($ft, offset($rs); 0x31) / swc1 (0x39)
  | arith3 (fmt funct : Nat)    -- add.s/sub.s/mul.s/div.s: $fd, $fs, $ft
  | unary (fmt funct : Nat)     -- mov.s/cvt.s.w/cvt.w.s/sqrt.s/abs.s/neg.s/
                                -- round.w.s/trunc.w.s/ceil.w.s/floor.w.s: $fd, $fs
  | compare (fmt funct : Nat)   -- c.eq.s/c.lt.s/c.le.s/c.f.s/c.un.s/c.ueq.s/
                                -- c.olt.s/c.ult.s/c.ole.s/c.ule.s (fmt=S) and
                                -- their c.cond.d counterparts (fmt=D): $fs, $ft
  | branch (tf : Nat)           -- bc1t (tf=1) / bc1f (tf=0): target

/-- Static table of coprocessor-1 (FPU) mnemonics: (name, form). -/
private def cop1Table : List (String × Cop1Form) :=
  [("mtc1", .moveGpFp 4), ("mfc1", .moveGpFp 0),
   ("cfc1", .moveGpFp 2), ("ctc1", .moveGpFp 6),
   ("lwc1", .mem 0x31), ("swc1", .mem 0x39),
   ("add.s", .arith3 0x10 0x00), ("sub.s", .arith3 0x10 0x01),
   ("mul.s", .arith3 0x10 0x02), ("div.s", .arith3 0x10 0x03),
   ("mov.s", .unary 0x10 0x06),
   ("sqrt.s", .unary 0x10 0x04), ("abs.s", .unary 0x10 0x05), ("neg.s", .unary 0x10 0x07),
   ("round.w.s", .unary 0x10 0x0c), ("trunc.w.s", .unary 0x10 0x0d),
   ("ceil.w.s", .unary 0x10 0x0e), ("floor.w.s", .unary 0x10 0x0f),
   ("cvt.s.w", .unary 0x14 0x20), ("cvt.w.s", .unary 0x10 0x24),
   ("c.eq.s", .compare 0x10 0x32), ("c.lt.s", .compare 0x10 0x3c), ("c.le.s", .compare 0x10 0x3e),
   ("c.f.s", .compare 0x10 0x30), ("c.un.s", .compare 0x10 0x31), ("c.ueq.s", .compare 0x10 0x33),
   ("c.olt.s", .compare 0x10 0x34), ("c.ult.s", .compare 0x10 0x35),
   ("c.ole.s", .compare 0x10 0x36), ("c.ule.s", .compare 0x10 0x37),
   ("bc1t", .branch 1), ("bc1f", .branch 0),
   -- Double-precision (`.d`) -- v2 addition, `docs/spec/MIPS-COVERAGE-GAPS.md`
   -- §3.9A; `fmt` = `D` = 0x11 (see `Instruction.lean`'s double-precision
   -- bullet for the register-pair convention `$fN` operands follow here).
   ("ldc1", .mem 0x35), ("sdc1", .mem 0x3d),
   ("add.d", .arith3 0x11 0x00), ("sub.d", .arith3 0x11 0x01),
   ("mul.d", .arith3 0x11 0x02), ("div.d", .arith3 0x11 0x03),
   ("mov.d", .unary 0x11 0x06),
   ("sqrt.d", .unary 0x11 0x04), ("abs.d", .unary 0x11 0x05), ("neg.d", .unary 0x11 0x07),
   -- `cvt.d.s`: source is single, so `fmt` = S = 0x10 (names the *source*
   -- format, same convention as `cvt.s.w`/`cvt.w.s` above); `cvt.d.w`:
   -- source is a word, `fmt` = W = 0x14.
   ("cvt.d.s", .unary 0x10 0x21), ("cvt.s.d", .unary 0x11 0x20),
   ("cvt.d.w", .unary 0x14 0x21), ("cvt.w.d", .unary 0x11 0x24),
   ("c.eq.d", .compare 0x11 0x32), ("c.lt.d", .compare 0x11 0x3c), ("c.le.d", .compare 0x11 0x3e),
   ("c.f.d", .compare 0x11 0x30), ("c.un.d", .compare 0x11 0x31), ("c.ueq.d", .compare 0x11 0x33),
   ("c.olt.d", .compare 0x11 0x34), ("c.ult.d", .compare 0x11 0x35),
   ("c.ole.d", .compare 0x11 0x36), ("c.ule.d", .compare 0x11 0x37)]

-- `break` is a real instruction, not a pseudo-op, but it is zero-operand
-- (like `syscall`) rather than fitting any `RForm` with register operands,
-- so it is special-cased alongside `syscall` the same way throughout this
-- file (`isKnownMnemonic`, `wordsForMnemonic`, `encodeInstruction`).
private def pseudoSet : List String := ["li", "la", "move", "nop", "syscall", "break"]
private def directiveSet : List String := [".text", ".data", ".word", ".half", ".byte", ".asciiz", ".space"]

/-- SPECIAL2/SPECIAL3 mnemonics with an opcode-bearing R-type-like shape that
doesn't fit any existing `RForm` (nonzero opcode and/or an operand count
that doesn't match `arith3`/`shift`/`shiftv`/`multdiv`/`hilo`); hand-encoded
directly in `encodeInstruction` below instead of via `rTable`. `mul` has the
same `rd, rs, rt` operand shape as `arith3`, but is SPECIAL2-opcoded (0x1c)
like `clo`/`clz` rather than plain SPECIAL (opcode 0), so it is hand-encoded
here too rather than via `rTable`. -/
private def bshflMnemonics : List String := ["clo", "clz", "seb", "seh", "mul"]

/-- SPECIAL2 multiply-accumulate (MIPS32): `madd`/`maddu`/`msub`/`msubu` have
the same `rs, rt` operand shape as `mult`/`multu`/`div`/`divu` (`RForm.
multdiv`), but unlike those, are SPECIAL2-opcoded (0x1c) like `mul`/`clo`/
`clz` above, so they can't go through the opcode-0 `rTable` either; hand-
encoded directly in `encodeInstruction` below (docs/spec/MIPS-COVERAGE-GAPS.md
§3.5). -/
private def multAccumMnemonics : List String := ["madd", "maddu", "msub", "msubu"]

/-- Real MIPS32 register-indirect jump/call (opcode 0, funct 0x08/0x09):
`jr $rs` (one operand) and `jalr $rd, $rs` (two operands, also accepting the
`jalr $rs` one-operand sugar for `jalr $ra, $rs`) don't fit any existing
`RForm`'s fixed operand count, so they're hand-encoded directly in
`encodeInstruction` below, the same way `bshflMnemonics` are. -/
private def jrJalrMnemonics : List String := ["jr", "jalr"]

/-- Write-direction HI/LO register moves (real MIPS32 `mthi`/`mtlo`, opcode
0, funct 0x11/0x13): single-operand `rs` only, the same shape as `jr`, so
like `jrJalrMnemonics` they don't fit any existing `RForm`'s fixed operand
count and are hand-encoded directly in `encodeInstruction` below. The
write-direction counterparts to `mfhi`/`mflo` (`RForm.hilo`), needed for OS
context switching and setjmp/longjmp to save/restore `hi`/`lo` (see
docs/spec/MIPS-COVERAGE-GAPS.md §3.5). -/
private def hiLoMoveMnemonics : List String := ["mthi", "mtlo"]
/-- MIPS32r2 rotate/bitfield mnemonics (docs/spec/MIPS-COVERAGE-GAPS.md
section 3.4): `rotr`/`rotrv` overload `srl`/`srlv`'s opcode/funct via the
`rs`/`shamt` field (so they don't fit `rTable`'s `.shift`/`.shiftv` forms,
which always encode `rs`/`shamt` as 0); `wsbh` is another BSHFL sub-op like
`seb`/`seh`; `ext`/`ins` are SPECIAL3-opcoded with a four-operand
`rt, rs, pos, size` shape no existing `RForm` has. All hand-encoded in
`encodeInstruction` below, the same way `bshflMnemonics` are. -/
private def bitfieldMnemonics : List String := ["rotr", "rotrv", "wsbh", "ext", "ins"]
/-- Coprocessor-0 (CP0) register move / execution-control mnemonics
(docs/spec/MIPS-COVERAGE-GAPS.md \u00a73.10A). `mfc0`/`mtc0` share `mfc1`/
`mtc1`'s move-shape but address a plain numeric CP0 register instead of an
`$fN` FP register, and `eret`/`wait` are zero-operand like `break`, so none
of the four fit `Cop1Form`/`RForm`/the existing zero-operand special cases
exactly -- hand-encoded directly in `encodeInstruction` below, the same way
`bshflMnemonics`/`jrJalrMnemonics` are. -/
private def cop0Mnemonics : List String := ["mfc0", "mtc0", "eret", "wait"]

private def isKnownMnemonic (m : String) : Bool :=
  rTable.any (·.1 == m) ∨ iTable.any (·.1 == m) ∨ jTable.any (·.1 == m) ∨
    bTable.any (·.1 == m) ∨ cop1Table.any (·.1 == m) ∨ pseudoSet.contains m ∨
    directiveSet.contains m ∨ bshflMnemonics.contains m ∨ jrJalrMnemonics.contains m ∨
    multAccumMnemonics.contains m ∨ hiLoMoveMnemonics.contains m ∨
    bitfieldMnemonics.contains m ∨ cop0Mnemonics.contains m

/-- Number of 32-bit words a `li $rt, v` expansion emits, per
`PseudoOps.txt` lines 245-247: sign-extendable-16-bit values use a single
`addiu`; zero-extendable-16-bit (unsigned) values use a single `ori`;
everything else needs the `lui`/`ori` two-word split. -/
private def liWordCount (v : Int) : Nat :=
  if (-32768 : Int) ≤ v ∧ v ≤ -1 then 1
  else if (0 : Int) ≤ v ∧ v ≤ 65535 then 1
  else 2

-- ====================================================================
-- Program-building helpers (byte/half-word packing, big-endian)
-- ====================================================================

/-- Round `a` up to the next multiple of `n` (`n > 0`). -/
private def alignUp (a : W32) (n : Nat) : W32 :=
  let an := a.toNat
  natToW32 (((an + n - 1) / n) * n)

/-- Write a single byte into `prog` at `addr`, merging it into the
big-endian-packed 4-byte-aligned word that contains it (other bytes of that
word are left untouched, defaulting to 0 if the word doesn't exist yet). -/
private def putByte (prog : Program) (addr : W32) (b : Nat) : Program :=
  let wordAddr := natToW32 ((addr.toNat / 4) * 4)
  let byteIdx := addr.toNat % 4          -- 0 = most-significant byte (big-endian)
  let shift := (3 - byteIdx) * 8
  let existing := prog.getD wordAddr 0
  let mask : W32 := natToW32 (0xff <<< shift)
  let cleared := existing &&& (natToW32 0xffffffff ^^^ mask)
  let inserted := cleared ||| (natToW32 (b % 256) <<< shift)
  prog.insert wordAddr inserted

private def putHalf (prog : Program) (addr : W32) (h : Nat) : Program :=
  let hi := (h / 256) % 256
  let lo := h % 256
  let prog := putByte prog addr hi
  putByte prog (addr + 1#32) lo

private def putWord (prog : Program) (addr : W32) (w : W32) : Program :=
  prog.insert addr w

private def putString (prog : Program) (addr : W32) (s : String) : Program :=
  let bytes := s.toList.map (fun c => c.toNat % 256)
  let withNull := bytes ++ [0]
  withNull.foldl (fun (p, a) b => (putByte p a b, a + 1#32)) (prog, addr) |>.1

-- ====================================================================
-- Pass 1: layout (addresses + labels), pass-1 word/byte counts only
-- ====================================================================

/-- A line with real content (label-only lines are folded into the label
table and otherwise dropped). -/
private structure RawItem where
  lineNo : Nat
  addr : W32
  mnemonic : String
  operands : List String

private structure LState where
  inText : Bool
  textAddr : W32
  dataAddr : W32
  labels : Std.HashMap String W32
  items : Array RawItem

private def LState.curAddr (s : LState) : W32 := if s.inText then s.textAddr else s.dataAddr
private def LState.setAddr (s : LState) (a : W32) : LState :=
  if s.inText then { s with textAddr := a } else { s with dataAddr := a }

/-- Number of bytes a non-text-segment directive's data occupies, and any
required alignment (applied to the segment pointer before recording the
item's address). Does not include `.text`/`.data` (segment switches, handled
separately) or real/pseudo instructions (handled by `wordsForMnemonic`). -/
private def directiveLayout (mnemonic : String) (operands : List String) (lineNo : Nat) :
    Except AsmError (Nat × Nat) := -- (alignment, byteCount)
  match mnemonic with
  | ".word" => pure (4, 4 * operands.length)
  | ".half" => pure (2, 2 * operands.length)
  | ".byte" => pure (1, operands.length)
  | ".asciiz" =>
    match operands with
    | [s] => pure (1, s.length + 1)
    | _ => throw (.badOperand s!".asciiz expects exactly one string operand" lineNo)
  | ".space" =>
    match operands with
    | [tok] => do
        let n ← parseImmediate tok lineNo
        if n < 0 then throw (.badImmediate s!".space requires a non-negative count" lineNo)
        pure (1, n.toNat)
    | _ => throw (.badOperand s!".space expects exactly one operand" lineNo)
  | _ => throw (.badDirective s!"unknown directive '{mnemonic}'" lineNo)

/-- Word count (×4 = byte count) for a real or pseudo instruction mnemonic,
without needing label resolution (see module docstring: `li`'s numeric
literal determines its size directly; `la`'s label-address form is always
the general 2-word case since every label address exceeds 16 bits). -/
private def wordsForMnemonic (mnemonic : String) (operands : List String) (lineNo : Nat) :
    Except AsmError Nat :=
  match mnemonic with
  | "li" =>
    match operands with
    | [_, valTok] => do
        let v ← parseImmediate valTok lineNo
        pure (liWordCount v)
    | _ => throw (.badOperand s!"li expects 'li $reg, imm'" lineNo)
  | "la" =>
    match operands with
    | [_, lbl] =>
      if looksNumeric lbl then
        throw (.badOperand s!"la requires a label operand (use li for numeric constants): '{lbl}'" lineNo)
      else pure 2
    | _ => throw (.badOperand s!"la expects 'la $reg, label'" lineNo)
  | "move" =>
    match operands with
    | [_, _] => pure 1
    | _ => throw (.badOperand s!"move expects 'move $dst, $src'" lineNo)
  | "nop" =>
    match operands with
    | [] => pure 1
    | _ => throw (.badOperand s!"nop takes no operands" lineNo)
  | "syscall" =>
    match operands with
    | [] => pure 1
    | _ => throw (.badOperand s!"syscall takes no operands" lineNo)
  | "break" =>
    match operands with
    | [] => pure 1
    | _ => throw (.badOperand s!"break takes no operands" lineNo)
  | _ => pure 1

private def layoutLine (s : LState) (pl : ParsedLine) : Except AsmError LState := do
  let s ←
    match pl.label with
    | none => pure s
    | some lbl =>
      if s.labels.contains lbl then
        throw (.duplicateLabel s!"label '{lbl}' already defined" pl.lineNo)
      else
        pure { s with labels := s.labels.insert lbl s.curAddr }
  match pl.mnemonic with
  | none => pure s
  | some ".text" => pure { s with inText := true }
  | some ".data" => pure { s with inText := false }
  | some m =>
    if directiveSet.contains m then do
      let (align, bytes) ← directiveLayout m pl.operands pl.lineNo
      let aligned := alignUp s.curAddr align
      let s := s.setAddr aligned
      let item : RawItem := { lineNo := pl.lineNo, addr := aligned, mnemonic := m, operands := pl.operands }
      let s := s.setAddr (aligned + natToW32 bytes)
      pure { s with items := s.items.push item }
    else if isKnownMnemonic m then do
      let n ← wordsForMnemonic m pl.operands pl.lineNo
      let addr := s.curAddr
      let item : RawItem := { lineNo := pl.lineNo, addr, mnemonic := m, operands := pl.operands }
      let s := s.setAddr (addr + natToW32 (4 * n))
      pure { s with items := s.items.push item }
    else
      throw (.unknownMnemonic s!"unknown mnemonic '{m}'" pl.lineNo)

-- ====================================================================
-- Pass 2: encode (labels now fully resolved)
-- ====================================================================

/-- Resolve a branch/jump target token: a numeric literal is used directly
(as a word-granular value, i.e. already the field to encode); a label is
looked up in the label table. -/
private def resolveLabel (labels : Std.HashMap String W32) (tok : String) (lineNo : Nat) :
    Except AsmError W32 :=
  match labels.get? tok with
  | some addr => pure addr
  | none => throw (.undefinedLabel s!"undefined label '{tok}'" lineNo)

private def rtWord (rs rt rd shamt funct : Nat) : W32 :=
  mkRT (natToW32 rs) (natToW32 rt) (natToW32 rd) (natToW32 shamt) (natToW32 funct)

private def itWord (opcode rs rt : Nat) (imm : W32) : W32 :=
  mkIT (natToW32 opcode) (natToW32 rs) (natToW32 rt) imm

private def jWord (opcode : Nat) (targetWordAddr : Nat) : W32 :=
  (natToW32 opcode <<< 26) ||| mkJT (natToW32 targetWordAddr)

/-- Build a nonzero-opcode R-type-like word (`clo`/`clz`/`seb`/`seh`:
SPECIAL2/SPECIAL3), same as `rtWord` but with the real opcode OR'd into the
top 6 bits (mirrors `jWord`'s `opcode <<< 26` composition, since `mkRT`
always leaves the opcode field as 0). -/
private def opRtWord (opcode rs rt rd shamt funct : Nat) : W32 :=
  (natToW32 opcode <<< 26) ||| rtWord rs rt rd shamt funct

/-- Build a coprocessor-1 (FPU) R-type-shaped word: `mkRT`'s opcode field is
always 0 (correct for plain R-type), so this ORs in opcode 0x11 explicitly,
the same way `jWord` ORs its opcode over `mkJT`'s target-only field. -/
private def cop1RtWord (fmt rt rd shamt funct : Nat) : W32 :=
  (natToW32 0x11 <<< 26) ||| rtWord fmt rt rd shamt funct

/-- Build a coprocessor-0 (CP0) R-type-shaped word: same opcode-OR
convention as `cop1RtWord`, but opcode 0x10 (COP0). -/
private def cop0RtWord (fmt rt rd shamt funct : Nat) : W32 :=
  (natToW32 0x10 <<< 26) ||| rtWord fmt rt rd shamt funct

/-- Encode an `li $rt, v` expansion per `PseudoOps.txt` (see `liWordCount`). -/
private def encodeLi (rt : Nat) (v : Int) : List W32 :=
  if (-32768 : Int) ≤ v ∧ v ≤ -1 then
    [itWord 0x09 zeroReg rt (ofInt32 v)]           -- addiu rt, $zero, v
  else if (0 : Int) ≤ v ∧ v ≤ 65535 then
    [itWord 0x0d zeroReg rt (ofInt32 v)]           -- ori rt, $zero, v
  else
    let w := ofInt32 v
    let hi16 := w >>> 16
    let lo16 := w &&& 0xffff#32
    [itWord 0x0f 0 atReg hi16,                     -- lui $at, hi16
     itWord 0x0d atReg rt lo16]                    -- ori rt, $at, lo16

private def encodeRForm (name : String) (funct : Nat) (form : RForm) (operands : List String)
    (lineNo : Nat) : Except AsmError W32 :=
  match form with
  | .arith3 =>
    match operands with
    | [rdT, rsT, rtT] => do
        let rd ← parseRegister rdT lineNo
        let rs ← parseRegister rsT lineNo
        let rt ← parseRegister rtT lineNo
        pure (rtWord rs rt rd 0 funct)
    | _ => throw (.badOperand s!"{name} expects 'rd, rs, rt'" lineNo)
  | .shift =>
    match operands with
    | [rdT, rtT, shT] => do
        let rd ← parseRegister rdT lineNo
        let rt ← parseRegister rtT lineNo
        let sh ← parseImmediate shT lineNo
        if sh < 0 ∨ sh > 31 then throw (.badImmediate s!"{name} shamt out of range (0-31)" lineNo)
        pure (rtWord 0 rt rd sh.toNat funct)
    | _ => throw (.badOperand s!"{name} expects 'rd, rt, shamt'" lineNo)
  | .shiftv =>
    match operands with
    | [rdT, rtT, rsT] => do
        let rd ← parseRegister rdT lineNo
        let rt ← parseRegister rtT lineNo
        let rs ← parseRegister rsT lineNo
        pure (rtWord rs rt rd 0 funct)
    | _ => throw (.badOperand s!"{name} expects 'rd, rt, rs'" lineNo)
  | .multdiv =>
    match operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT lineNo
        let rt ← parseRegister rtT lineNo
        pure (rtWord rs rt 0 0 funct)
    | _ => throw (.badOperand s!"{name} expects 'rs, rt'" lineNo)
  | .hilo =>
    match operands with
    | [rdT] => do
        let rd ← parseRegister rdT lineNo
        pure (rtWord 0 0 rd 0 funct)
    | _ => throw (.badOperand s!"{name} expects 'rd'" lineNo)

private def encodeIForm (name : String) (opcode : Nat) (form : IForm) (operands : List String)
    (lineNo : Nat) : Except AsmError W32 :=
  match form with
  | .arith =>
    match operands with
    | [rtT, rsT, immT] => do
        let rt ← parseRegister rtT lineNo
        let rs ← parseRegister rsT lineNo
        let imm ← parseImmediate immT lineNo
        pure (itWord opcode rs rt (ofInt32 imm))
    | _ => throw (.badOperand s!"{name} expects 'rt, rs, imm'" lineNo)
  | .lui =>
    match operands with
    | [rtT, immT] => do
        let rt ← parseRegister rtT lineNo
        let imm ← parseImmediate immT lineNo
        pure (itWord opcode 0 rt (ofInt32 imm))
    | _ => throw (.badOperand s!"{name} expects 'rt, imm'" lineNo)
  | .mem =>
    match operands with
    | [rtT, memT] => do
        let rt ← parseRegister rtT lineNo
        let (imm, rs) ← parseMemOperand memT lineNo
        pure (itWord opcode rs rt (ofInt32 imm))
    | _ => throw (.badOperand s!"{name} expects 'rt, offset(rs)'" lineNo)
  | .trapImm rtField =>
    match operands with
    | [rsT, immT] => do
        let rs ← parseRegister rsT lineNo
        let imm ← parseImmediate immT lineNo
        pure (itWord opcode rs rtField (ofInt32 imm))
    | _ => throw (.badOperand s!"{name} expects 'rs, imm'" lineNo)

private def encodeJForm (labels : Std.HashMap String W32) (opcode : Nat) (operands : List String)
    (lineNo : Nat) : Except AsmError W32 :=
  match operands with
  | [tgt] => do
      let addr ←
        if looksNumeric tgt then do
          let v ← parseImmediate tgt lineNo
          if v < 0 then throw (.badImmediate s!"jump target must be non-negative" lineNo)
          pure (natToW32 v.toNat)
        else resolveLabel labels tgt lineNo
      if addr.toNat % 4 ≠ 0 then throw (.badOperand s!"jump target must be word-aligned" lineNo)
      pure (jWord opcode (addr.toNat / 4))
  | _ => throw (.badOperand s!"jump expects a single target operand" lineNo)

private def branchOffset (labels : Std.HashMap String W32) (tgt : String) (instrAddr : W32)
    (lineNo : Nat) : Except AsmError Int :=
  if looksNumeric tgt then
    parseImmediate tgt lineNo
  else do
    let target ← resolveLabel labels tgt lineNo
    let nextPc := instrAddr.toNat + 4
    pure (((target.toNat : Int) - (nextPc : Int)) / 4)

private def encodeBForm (labels : Std.HashMap String W32) (name : String) (opcode : Nat)
    (form : BForm) (operands : List String) (instrAddr : W32) (lineNo : Nat) :
    Except AsmError W32 :=
  match form with
  | .two =>
    match operands with
    | [rsT, rtT, tgt] => do
        let rs ← parseRegister rsT lineNo
        let rt ← parseRegister rtT lineNo
        let off ← branchOffset labels tgt instrAddr lineNo
        pure (itWord opcode rs rt (ofInt32 off))
    | _ => throw (.badOperand s!"{name} expects 'rs, rt, target'" lineNo)
  | .one =>
    match operands with
    | [rsT, tgt] => do
        let rs ← parseRegister rsT lineNo
        let off ← branchOffset labels tgt instrAddr lineNo
        pure (itWord opcode rs 0 (ofInt32 off))
    | _ => throw (.badOperand s!"{name} expects 'rs, target'" lineNo)
  | .regimm rtField =>
    match operands with
    | [rsT, tgt] => do
        let rs ← parseRegister rsT lineNo
        let off ← branchOffset labels tgt instrAddr lineNo
        pure (itWord opcode rs rtField (ofInt32 off))
    | _ => throw (.badOperand s!"{name} expects 'rs, target'" lineNo)

/-- Encode a coprocessor-1 (FPU) mnemonic's operand list into its word, per
`Cop1Form`'s shape and the static parameters carried in `cop1Table`. -/
private def encodeCop1Form (labels : Std.HashMap String W32) (name : String) (form : Cop1Form)
    (operands : List String) (instrAddr : W32) (lineNo : Nat) : Except AsmError W32 :=
  match form with
  | .moveGpFp fmt =>
    match operands with
    | [rtT, fsT] => do
        let rt ← parseRegister rtT lineNo
        let fs ← parseFpRegister fsT lineNo
        pure (cop1RtWord fmt rt fs 0 0)
    | _ => throw (.badOperand s!"{name} expects '$rt, $fs'" lineNo)
  | .mem opcode =>
    match operands with
    | [ftT, memT] => do
        let ft ← parseFpRegister ftT lineNo
        let (imm, rs) ← parseMemOperand memT lineNo
        pure (itWord opcode rs ft (ofInt32 imm))
    | _ => throw (.badOperand s!"{name} expects '$ft, offset($rs)'" lineNo)
  | .arith3 fmt funct =>
    match operands with
    | [fdT, fsT, ftT] => do
        let fd ← parseFpRegister fdT lineNo
        let fs ← parseFpRegister fsT lineNo
        let ft ← parseFpRegister ftT lineNo
        pure (cop1RtWord fmt ft fs fd funct)
    | _ => throw (.badOperand s!"{name} expects '$fd, $fs, $ft'" lineNo)
  | .unary fmt funct =>
    match operands with
    | [fdT, fsT] => do
        let fd ← parseFpRegister fdT lineNo
        let fs ← parseFpRegister fsT lineNo
        pure (cop1RtWord fmt 0 fs fd funct)
    | _ => throw (.badOperand s!"{name} expects '$fd, $fs'" lineNo)
  | .compare fmt funct =>
    match operands with
    | [fsT, ftT] => do
        let fs ← parseFpRegister fsT lineNo
        let ft ← parseFpRegister ftT lineNo
        pure (cop1RtWord fmt ft fs 0 funct)
    | _ => throw (.badOperand s!"{name} expects '$fs, $ft'" lineNo)
  | .branch tf =>
    match operands with
    | [tgt] => do
        let off ← branchOffset labels tgt instrAddr lineNo
        pure (itWord 0x11 0x08 tf (ofInt32 off))
    | _ => throw (.badOperand s!"{name} expects a single target operand" lineNo)

/-- Encode one real/pseudo instruction item into its emitted word(s). -/
private def encodeInstruction (labels : Std.HashMap String W32) (item : RawItem) :
    Except AsmError (List W32) := do
  let name := item.mnemonic
  match rTable.find? (·.1 == name) with
  | some (_, funct, form) => return [← encodeRForm name funct form item.operands item.lineNo]
  | none =>
  match iTable.find? (·.1 == name) with
  | some (_, opcode, form) => return [← encodeIForm name opcode form item.operands item.lineNo]
  | none =>
  match jTable.find? (·.1 == name) with
  | some (_, opcode) => return [← encodeJForm labels opcode item.operands item.lineNo]
  | none =>
  match bTable.find? (·.1 == name) with
  | some (_, opcode, form) => return [← encodeBForm labels name opcode form item.operands item.addr item.lineNo]
  | none =>
  match cop1Table.find? (·.1 == name) with
  | some (_, form) => return [← encodeCop1Form labels name form item.operands item.addr item.lineNo]
  | none =>
  match name with
  | "li" =>
    match item.operands with
    | [rtT, valT] => do
        let rt ← parseRegister rtT item.lineNo
        let v ← parseImmediate valT item.lineNo
        pure (encodeLi rt v)
    | _ => throw (.badOperand s!"li expects 'li $reg, imm'" item.lineNo)
  | "la" =>
    match item.operands with
    | [rtT, lbl] => do
        let rt ← parseRegister rtT item.lineNo
        let addr ← resolveLabel labels lbl item.lineNo
        pure (encodeLi rt (addr.toNat : Int))
    | _ => throw (.badOperand s!"la expects 'la $reg, label'" item.lineNo)
  | "move" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord 0 rs rd 0 0x21]              -- addu rd, $zero, rs
    | _ => throw (.badOperand s!"move expects 'move $dst, $src'" item.lineNo)
  | "nop" => pure [0#32]
  | "syscall" =>
    match item.operands with
    | [] => pure [0x0000000C#32]              -- all fields zero except funct = 0x0c
    | _ => throw (.badOperand s!"syscall takes no operands" item.lineNo)
  -- SPECIAL2 bit-count (MIPS32): `clo $rd, $rs` / `clz $rd, $rs`. The raw
  -- encoding's rt-position field duplicates rd (real hardware quirk, see
  -- `Instruction.lean`'s `.clo`/`.clz` docstrings).
  | "clo" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [opRtWord 0x1c rs rd rd 0 0x21]
    | _ => throw (.badOperand s!"clo expects 'rd, rs'" item.lineNo)
  | "clz" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [opRtWord 0x1c rs rd rd 0 0x20]
    | _ => throw (.badOperand s!"clz expects 'rd, rs'" item.lineNo)
  -- SPECIAL2 GPR multiply (MIPS32): `mul $rd, $rs, $rt`. Plain `rs, rt, rd`
  -- shape, unlike `clo`/`clz` -- no duplicated-field quirk -- but still
  -- SPECIAL2-opcoded (0x1c), so it needs `opRtWord` rather than plain
  -- `rtWord`/`rTable` (docs/spec/MIPS-COVERAGE-GAPS.md §3.5).
  | "mul" =>
    match item.operands with
    | [rdT, rsT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt rd 0 0x02]
    | _ => throw (.badOperand s!"mul expects 'rd, rs, rt'" item.lineNo)
  -- SPECIAL2 multiply-accumulate (MIPS32): `madd $rs, $rt` / `maddu $rs, $rt`
  -- / `msub $rs, $rt` / `msubu $rs, $rt`. Same `rs, rt` shape as `mult`/
  -- `div` (RForm.multdiv), but SPECIAL2-opcoded like `mul` above, so it
  -- needs `opRtWord` rather than `rTable` (docs/spec/MIPS-COVERAGE-GAPS.md
  -- §3.5).
  | "madd" =>
    match item.operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt 0 0 0x00]
    | _ => throw (.badOperand s!"madd expects 'rs, rt'" item.lineNo)
  | "maddu" =>
    match item.operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt 0 0 0x01]
    | _ => throw (.badOperand s!"maddu expects 'rs, rt'" item.lineNo)
  | "msub" =>
    match item.operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt 0 0 0x04]
    | _ => throw (.badOperand s!"msub expects 'rs, rt'" item.lineNo)
  | "msubu" =>
    match item.operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt 0 0 0x05]
    | _ => throw (.badOperand s!"msubu expects 'rs, rt'" item.lineNo)
  -- SPECIAL3 BSHFL sign-extend (MIPS32r2): `seb $rd, $rt` / `seh $rd, $rt`.
  -- `rs` is unused/fixed 0; the shamt-position field (0x10/0x18) selects
  -- which BSHFL sub-op this is.
  | "seb" =>
    match item.operands with
    | [rdT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1f 0 rt rd 0x10 0x20]
    | _ => throw (.badOperand s!"seb expects 'rd, rt'" item.lineNo)
  | "seh" =>
    match item.operands with
    | [rdT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1f 0 rt rd 0x18 0x20]
    | _ => throw (.badOperand s!"seh expects 'rd, rt'" item.lineNo)
  -- `wsbh $rd, $rt`: SPECIAL3 BSHFL (MIPS32r2), same family/shape as
  -- `seb`/`seh`, sub-field 0x02.
  | "wsbh" =>
    match item.operands with
    | [rdT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1f 0 rt rd 0x02 0x20]
    | _ => throw (.badOperand s!"wsbh expects 'rd, rt'" item.lineNo)
  -- `rotr $rd, $rt, $sa` (MIPS32r2): same `rd, rt, shamt` shape as `srl`
  -- (the `.shift` `RForm`), but overloads the normally-0 `rs` field to
  -- 0x01 to select rotate (see `Instruction.lean`'s `.rotr` docstring).
  | "rotr" =>
    match item.operands with
    | [rdT, rtT, saT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        let sa ← parseImmediate saT item.lineNo
        if sa < 0 ∨ sa > 31 then throw (.badImmediate s!"rotr shamt out of range (0-31)" item.lineNo)
        pure [rtWord 1 rt rd sa.toNat 0x02]
    | _ => throw (.badOperand s!"rotr expects 'rd, rt, sa'" item.lineNo)
  -- `rotrv $rd, $rt, $rs` (MIPS32r2): same `rd, rt, rs` shape as `srlv`
  -- (the `.shiftv` `RForm`), but overloads the normally-0 `shamt` field to
  -- 0x01 to select rotate.
  | "rotrv" =>
    match item.operands with
    | [rdT, rtT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs rt rd 1 0x06]
    | _ => throw (.badOperand s!"rotrv expects 'rd, rt, rs'" item.lineNo)
  -- `ext $rt, $rs, pos, size` / `ins $rt, $rs, pos, size` (MIPS32r2
  -- bitfield extract/insert, SPECIAL3 opcode 0x1f): `pos`/`size` are
  -- compile-time constants (not registers). Real hardware packs `pos`
  -- into the `shamt` field for both, but the `rd`-position field differs
  -- (`size - 1` for `ext`, `pos + size - 1` for `ins`) -- see
  -- `Instruction.lean`'s `.ext`/`.ins` docstrings. Both fields must fit
  -- their 5-bit encoding slots, so `pos` is 0-31, `size` is 1-32, and
  -- `pos + size <= 32` (the real architectural constraint; violating it
  -- is UNPREDICTABLE on real hardware, so this assembler rejects it
  -- outright rather than silently truncating).
  | "ext" =>
    match item.operands with
    | [rtT, rsT, posT, sizeT] => do
        let rt ← parseRegister rtT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        let pos ← parseImmediate posT item.lineNo
        let size ← parseImmediate sizeT item.lineNo
        if pos < 0 ∨ pos > 31 then throw (.badImmediate s!"ext pos out of range (0-31)" item.lineNo)
        if size < 1 ∨ size > 32 then throw (.badImmediate s!"ext size out of range (1-32)" item.lineNo)
        if pos + size > 32 then throw (.badImmediate s!"ext pos + size must be <= 32" item.lineNo)
        pure [opRtWord 0x1f rs rt (size - 1).toNat pos.toNat 0x00]
    | _ => throw (.badOperand s!"ext expects 'rt, rs, pos, size'" item.lineNo)
  | "ins" =>
    match item.operands with
    | [rtT, rsT, posT, sizeT] => do
        let rt ← parseRegister rtT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        let pos ← parseImmediate posT item.lineNo
        let size ← parseImmediate sizeT item.lineNo
        if pos < 0 ∨ pos > 31 then throw (.badImmediate s!"ins pos out of range (0-31)" item.lineNo)
        if size < 1 ∨ size > 32 then throw (.badImmediate s!"ins size out of range (1-32)" item.lineNo)
        if pos + size > 32 then throw (.badImmediate s!"ins pos + size must be <= 32" item.lineNo)
        pure [opRtWord 0x1f rs rt (pos + size - 1).toNat pos.toNat 0x04]
    | _ => throw (.badOperand s!"ins expects 'rt, rs, pos, size'" item.lineNo)
  -- Register-indirect jump/call (real MIPS32 `jr`/`jalr`, opcode 0, funct
  -- 0x08/0x09; see `Instruction.lean`'s `.jr`/`.jalr` docstrings). `rt`/
  -- `shamt` are unused/fixed 0 in the real encoding.
  | "jr" =>
    match item.operands with
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 0 0 0x08]
    | _ => throw (.badOperand s!"jr expects 'rs'" item.lineNo)
  | "jalr" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 rd 0 0x09]
    -- One-operand sugar: `jalr $rs` == `jalr $ra, $rs` (rd defaults to 31),
    -- per real MIPS32 assembly syntax.
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 31 0 0x09]
    | _ => throw (.badOperand s!"jalr expects 'rd, rs' or 'rs'" item.lineNo)
  -- Write-direction HI/LO moves (real MIPS32 `mthi`/`mtlo`, opcode 0, funct
  -- 0x11/0x13 -- the next funct values immediately after `mfhi`'s 0x10/
  -- `mflo`'s 0x12; see `Instruction.lean`'s `.mthi`/`.mtlo` docstrings).
  | "mthi" =>
    match item.operands with
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 0 0 0x11]
    | _ => throw (.badOperand s!"mthi expects 'rs'" item.lineNo)
  | "mtlo" =>
    match item.operands with
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 0 0 0x13]
    | _ => throw (.badOperand s!"mtlo expects 'rs'" item.lineNo)
  | "break" =>
    match item.operands with
    | [] => pure [0x0000000D#32]              -- all fields zero except funct = 0x0d
    | _ => throw (.badOperand s!"break takes no operands" item.lineNo)
  -- Coprocessor-0 (CP0) register move / execution control (real MIPS32
  -- ISA, docs/spec/MIPS-COVERAGE-GAPS.md \u00a73.10A; see `Instruction.lean`/
  -- `Step.lean`). `rd` is a plain numeric CP0 register reference (0-31);
  -- only 12/13/14 (Status/Cause/EPC) are meaningful in this model.
  | "mfc0" =>
    match item.operands with
    | [rtT, rdT] => do
        let rt ← parseRegister rtT item.lineNo
        let rd ← parseCp0Register rdT item.lineNo
        pure [cop0RtWord 0x00 rt rd 0 0]
    | _ => throw (.badOperand s!"mfc0 expects '$rt, rd'" item.lineNo)
  | "mtc0" =>
    match item.operands with
    | [rtT, rdT] => do
        let rt ← parseRegister rtT item.lineNo
        let rd ← parseCp0Register rdT item.lineNo
        pure [cop0RtWord 0x04 rt rd 0 0]
    | _ => throw (.badOperand s!"mtc0 expects '$rt, rd'" item.lineNo)
  | "eret" =>
    match item.operands with
    | [] => pure [cop0RtWord 0x10 0 0 0 0x18]
    | _ => throw (.badOperand s!"eret takes no operands" item.lineNo)
  | "wait" =>
    match item.operands with
    | [] => pure [cop0RtWord 0x10 0 0 0 0x20]
    | _ => throw (.badOperand s!"wait takes no operands" item.lineNo)
  | _ => throw (.unknownMnemonic s!"unknown mnemonic '{name}'" item.lineNo)

private def applyItem (labels : Std.HashMap String W32) (prog : Program) (item : RawItem) :
    Except AsmError Program :=
  match item.mnemonic with
  | ".word" => do
      let mut p := prog
      let mut a := item.addr
      for tok in item.operands do
        let v ←
          if looksNumeric tok then parseImmediate tok item.lineNo
          else do
            let addr ← resolveLabel labels tok item.lineNo
            pure ((addr.toNat : Int))
        p := putWord p a (ofInt32 v)
        a := a + 4#32
      pure p
  | ".half" => do
      let mut p := prog
      let mut a := item.addr
      for tok in item.operands do
        let v ← parseImmediate tok item.lineNo
        p := putHalf p a (ofInt32 v).toNat
        a := a + 2#32
      pure p
  | ".byte" => do
      let mut p := prog
      let mut a := item.addr
      for tok in item.operands do
        let v ← parseImmediate tok item.lineNo
        p := putByte p a (ofInt32 v).toNat
        a := a + 1#32
      pure p
  | ".asciiz" =>
    match item.operands with
    | [s] => pure (putString prog item.addr s)
    | _ => throw (.badOperand s!".asciiz expects exactly one string operand" item.lineNo)
  | ".space" => pure prog  -- reserved bytes default to 0 (sparse map, unread = 0)
  | _ => do
      let words ← encodeInstruction labels item
      let mut p := prog
      let mut a := item.addr
      for w in words do
        p := putWord p a w
        a := a + 4#32
      pure p

-- ====================================================================
-- Top level
-- ====================================================================

/-- Assemble v1 MIPS subset source text into a `Program` (PC → instruction
word map covering both `.text` and `.data` contents). See module docstring
for supported syntax and layout conventions. -/
def assemble (src : String) : AsmResult := do
  let rawLines := src.splitOn "\n"
  let numbered := rawLines.zipIdx.map (fun (l, i) => (i + 1, l))
  let initial : LState :=
    { inText := true, textAddr := textBase, dataAddr := dataBase, labels := ∅, items := #[] }
  let final ← numbered.foldlM
    (fun s (lineNo, line) => do
      let pl ← parseLine lineNo line
      layoutLine s pl)
    initial
  final.items.foldlM (fun prog item => applyItem final.labels prog item) (∅ : Program)

-- ====================================================================
-- ## Tests
-- ====================================================================

-- Note: these golden tests use `#guard` exclusively, not `by decide`/`by rfl`.
-- `Std.HashMap`'s `getD`/`contains` do not kernel-reduce (`by decide` gets
-- stuck on the underlying imperative array operations — confirmed against
-- a minimal `Std.HashMap Nat Nat` repro), so `by decide`/`by rfl` are not
-- usable for any `Program`-valued assertion in this Lean/Std version.
-- `#guard` (compiled evaluation) is explicitly sanctioned by DESIGN.md §5
-- and works correctly here; all checks below use it.

-- A `.text` program mixing `add`/`addi`/`beq`/`jal` with labels.
-- loop:  addi $t0, $zero, 1
--        add  $t1, $t0, $t0
--        beq  $t1, $zero, loop
--        jal  loop
def prog1Src : String :=
"loop: addi $t0, $zero, 1\n" ++
"      add $t1, $t0, $t0\n" ++
"      beq $t1, $zero, loop\n" ++
"      jal loop\n"

def prog1 : Program :=
  match assemble prog1Src with
  | .ok p => p
  | .error _ => ∅

-- addr 0x400000: addi $t0,$zero,1 -> opcode 0x09? no addi is 0x08.
#guard prog1.getD textBase 0 = mkIT (8#32) (0#32) (8#32) (1#32)

#guard prog1.getD (textBase + 4#32) 0 = mkRT (8#32) (8#32) (9#32) (0#32) (0x20#32)

-- beq $t1,$zero,loop: instrAddr = textBase+8, nextPc = textBase+12,
-- target = textBase (loop), offset = (textBase - (textBase+12))/4 = -3
#guard prog1.getD (textBase + 8#32) 0 = mkIT (4#32) (9#32) (0#32) (ofInt32 (-3))

-- jal loop: target = textBase, targetWordAddr = textBase/4
#guard prog1.getD (textBase + 12#32) 0 = (natToW32 0x03 <<< 26) ||| mkJT (textBase >>> 2)

-- `li` needing the lui+ori split: 0x12345 = 74565, hi16 = 1, lo16 = 0x2345.
def liSplitSrc : String := "li $t0, 0x12345\n"
def liSplitProg : Program :=
  match assemble liSplitSrc with
  | .ok p => p
  | .error _ => ∅

#guard liSplitProg.getD textBase 0 = mkIT (0x0f#32) (0#32) (1#32) (1#32)
#guard liSplitProg.getD (textBase + 4#32) 0 = mkIT (0x0d#32) (1#32) (8#32) (0x2345#32)

-- A negative `li`: -1 is within [-32768,-1], single `addiu` with imm = 0xffff.
def liNegSrc : String := "li $t0, -1\n"
def liNegProg : Program :=
  match assemble liNegSrc with
  | .ok p => p
  | .error _ => ∅

#guard liNegProg.getD textBase 0 = mkIT (0x09#32) (0#32) (8#32) (0xffff#32)
#guard liNegProg.size = 1

-- `.data` with `.word`/`.asciiz`/`.space`, big-endian byte layout at dataBase.
def dataSrc : String :=
".data\n" ++
"x: .word 0x01020304\n" ++
"y: .asciiz \"Hi\"\n" ++
"z: .space 4\n" ++
"w: .word 7\n"

def dataProg : Program :=
  match assemble dataSrc with
  | .ok p => p
  | .error _ => ∅

-- x at dataBase, full word stored as-is.
#guard dataProg.getD dataBase 0 = 0x01020304#32

-- y at dataBase+4: bytes 'H'(0x48) 'i'(0x69) 0x00 0x00 (padding byte unset -> 0)
#guard dataProg.getD (dataBase + 4#32) 0 = 0x48690000#32

-- z: .space 4 reserves dataBase+7 .. dataBase+10, no entries written (0 default);
-- w: .word 7 lands at dataBase+11 rounded up to 4-alignment = dataBase+12.
#guard dataProg.getD (dataBase + 12#32) 0 = 7#32
#guard dataProg.contains (dataBase + 8#32) = false

-- `move`/`nop` expansions.
def moveNopSrc : String := "move $t0, $t1\nnop\n"
def moveNopProg : Program :=
  match assemble moveNopSrc with
  | .ok p => p
  | .error _ => ∅

#guard moveNopProg.getD textBase 0 = mkRT (0#32) (9#32) (8#32) (0#32) (0x21#32)
#guard moveNopProg.getD (textBase + 4#32) 0 = 0#32

-- `syscall`: zero operands, all fields zero except funct = 0x0c (0x0000000C),
-- per MARS's own runtime table (`InstructionSet.java` lines 1188-1191,
-- "000000 ccccc ccccc ccccc ccccc 001100"); also matches `Instruction.lean`'s
-- `encode .syscall`.
def syscallSrc : String := "addi $t0, $zero, 1\nsyscall\n"
def syscallProg : Program :=
  match assemble syscallSrc with
  | .ok p => p
  | .error _ => ∅

#guard syscallProg.getD (textBase + 4#32) 0 = 0x0000000C#32
#guard decode (syscallProg.getD (textBase + 4#32) 0) = some .syscall

-- `movn`/`movz`: table-driven like `add`, 'rd, rs, rt' operand order.
def movSrc : String := "movn $t0, $t1, $t2\nmovz $t0, $t1, $t2\n"
def movProg : Program :=
  match assemble movSrc with
  | .ok p => p
  | .error _ => ∅

#guard movProg.getD textBase 0 = mkRT (9#32) (10#32) (8#32) (0#32) (0x0b#32)
#guard movProg.getD (textBase + 4#32) 0 = mkRT (9#32) (10#32) (8#32) (0#32) (0x0a#32)
#guard decode (movProg.getD textBase 0) = some (.movn 9#32 10#32 8#32)
#guard decode (movProg.getD (textBase + 4#32) 0) = some (.movz 9#32 10#32 8#32)

-- `sllv`/`srlv`/`srav $rd, $rt, $rs`: table-driven like `shift`, but the
-- third operand is a register (the shift amount), opcode 0.
def shiftvSrc : String := "sllv $t0, $t1, $t2\nsrlv $t0, $t1, $t2\nsrav $t0, $t1, $t2\n"
def shiftvProg : Program :=
  match assemble shiftvSrc with
  | .ok p => p
  | .error _ => ∅

#guard shiftvProg.getD textBase 0 = mkRT (10#32) (9#32) (8#32) (0#32) (0x04#32)
#guard shiftvProg.getD (textBase + 4#32) 0 = mkRT (10#32) (9#32) (8#32) (0#32) (0x06#32)
#guard shiftvProg.getD (textBase + 8#32) 0 = mkRT (10#32) (9#32) (8#32) (0#32) (0x07#32)
#guard decode (shiftvProg.getD textBase 0) = some (.sllv 8#32 9#32 10#32)
#guard decode (shiftvProg.getD (textBase + 4#32) 0) = some (.srlv 8#32 9#32 10#32)
#guard decode (shiftvProg.getD (textBase + 8#32) 0) = some (.srav 8#32 9#32 10#32)

-- `clo $rd, $rs` / `clz $rd, $rs`: SPECIAL2 opcode 0x1c, rt field duplicates rd.
def cloClzSrc : String := "clo $t0, $t1\nclz $t0, $t1\n"
def cloClzProg : Program :=
  match assemble cloClzSrc with
  | .ok p => p
  | .error _ => ∅

#guard cloClzProg.getD textBase 0 = (natToW32 0x1c <<< 26) ||| mkRT (9#32) (8#32) (8#32) (0#32) (0x21#32)
#guard cloClzProg.getD (textBase + 4#32) 0 = (natToW32 0x1c <<< 26) ||| mkRT (9#32) (8#32) (8#32) (0#32) (0x20#32)
#guard decode (cloClzProg.getD textBase 0) = some (.clo 9#32 8#32)
#guard decode (cloClzProg.getD (textBase + 4#32) 0) = some (.clz 9#32 8#32)

-- `mul $rd, $rs, $rt`: SPECIAL2 opcode 0x1c, plain rs/rt/rd shape (no
-- duplicated-field quirk, unlike clo/clz).
def mulSrc : String := "mul $t0, $t1, $t2\n"
def mulProg : Program :=
  match assemble mulSrc with
  | .ok p => p
  | .error _ => ∅

#guard mulProg.getD textBase 0 = (natToW32 0x1c <<< 26) ||| mkRT (9#32) (10#32) (8#32) (0#32) (0x02#32)
#guard decode (mulProg.getD textBase 0) = some (.mul 9#32 10#32 8#32)

-- `madd`/`maddu`/`msub`/`msubu $rs, $rt`: SPECIAL2 opcode 0x1c, `rs, rt`
-- shape (no `rd` field), cross-checked against `Instruction.encode`.
def multAccumSrc : String := "madd $t0, $t1\nmaddu $t0, $t1\nmsub $t0, $t1\nmsubu $t0, $t1\n"
def multAccumProg : Program :=
  match assemble multAccumSrc with
  | .ok p => p
  | .error _ => ∅

#guard multAccumProg.getD textBase 0 = encode (.madd 8#32 9#32)
#guard multAccumProg.getD (textBase + 4#32) 0 = encode (.maddu 8#32 9#32)
#guard multAccumProg.getD (textBase + 8#32) 0 = encode (.msub 8#32 9#32)
#guard multAccumProg.getD (textBase + 12#32) 0 = encode (.msubu 8#32 9#32)
#guard decode (multAccumProg.getD textBase 0) = some (.madd 8#32 9#32)
#guard decode (multAccumProg.getD (textBase + 4#32) 0) = some (.maddu 8#32 9#32)
#guard decode (multAccumProg.getD (textBase + 8#32) 0) = some (.msub 8#32 9#32)
#guard decode (multAccumProg.getD (textBase + 12#32) 0) = some (.msubu 8#32 9#32)
#guard (assemble "madd $t0, $t1, $t2\n").isOk = false
#guard (assemble "madd $t0\n").isOk = false

-- `seb $rd, $rt` / `seh $rd, $rt`: SPECIAL3 opcode 0x1f, funct 0x20, the
-- shamt-position sub-field (0x10/0x18) selects seb vs seh.
def sebSehSrc : String := "seb $t0, $t1\nseh $t0, $t1\n"
def sebSehProg : Program :=
  match assemble sebSehSrc with
  | .ok p => p
  | .error _ => ∅

#guard sebSehProg.getD textBase 0 = (natToW32 0x1f <<< 26) ||| mkRT (0#32) (9#32) (8#32) (0x10#32) (0x20#32)
#guard sebSehProg.getD (textBase + 4#32) 0 = (natToW32 0x1f <<< 26) ||| mkRT (0#32) (9#32) (8#32) (0x18#32) (0x20#32)
#guard decode (sebSehProg.getD textBase 0) = some (.seb 8#32 9#32)
#guard decode (sebSehProg.getD (textBase + 4#32) 0) = some (.seh 8#32 9#32)

-- `wsbh $rd, $rt`: SPECIAL3 opcode 0x1f, funct 0x20, same BSHFL family as
-- seb/seh, sub-field 0x02.
def wsbhSrc : String := "wsbh $t0, $t1\n"
def wsbhProg : Program :=
  match assemble wsbhSrc with
  | .ok p => p
  | .error _ => ∅

#guard wsbhProg.getD textBase 0 = (natToW32 0x1f <<< 26) ||| mkRT (0#32) (9#32) (8#32) (0x02#32) (0x20#32)
#guard decode (wsbhProg.getD textBase 0) = some (.wsbh 8#32 9#32)

-- `rotr $rd, $rt, $sa` / `rotrv $rd, $rt, $rs` (MIPS32r2): same opcode/funct
-- as srl/srlv, but overload the rs/shamt field to 0x01 to select rotate.
def rotrSrc : String := "rotr $t0, $t1, 5\nrotrv $t0, $t1, $t2\n"
def rotrProg : Program :=
  match assemble rotrSrc with
  | .ok p => p
  | .error _ => ∅

#guard rotrProg.getD textBase 0 = mkRT (1#32) (9#32) (8#32) (5#32) (0x02#32)
#guard rotrProg.getD (textBase + 4#32) 0 = mkRT (10#32) (9#32) (8#32) (1#32) (0x06#32)
#guard decode (rotrProg.getD textBase 0) = some (.rotr 8#32 9#32 5#32)
#guard decode (rotrProg.getD (textBase + 4#32) 0) = some (.rotrv 8#32 9#32 10#32)
-- rotr shamt out of range is rejected, same as shift's shamt check
#guard (assemble "rotr $t0, $t1, 32\n").isOk = false

-- `ext $rt, $rs, pos, size` / `ins $rt, $rs, pos, size` (MIPS32r2 bitfield
-- extract/insert): SPECIAL3 opcode 0x1f, funct 0x00/0x04. `pos`/`size` are
-- compile-time constants (pos=6, size=10 here), packed per the
-- `Instruction.lean`'s `.ext`/`.ins` docstrings (`rd`-position field is
-- `size-1=9` for ext, `pos+size-1=15` for ins).
def extInsSrc : String := "ext $t0, $t1, 6, 10\nins $t0, $t1, 6, 10\n"
def extInsProg : Program :=
  match assemble extInsSrc with
  | .ok p => p
  | .error _ => ∅

#guard extInsProg.getD textBase 0 = (natToW32 0x1f <<< 26) ||| mkRT (9#32) (8#32) (9#32) (6#32) (0x00#32)
#guard extInsProg.getD (textBase + 4#32) 0 = (natToW32 0x1f <<< 26) ||| mkRT (9#32) (8#32) (15#32) (6#32) (0x04#32)
#guard decode (extInsProg.getD textBase 0) = some (.ext 8#32 9#32 6#32 10#32)
#guard decode (extInsProg.getD (textBase + 4#32) 0) = some (.ins 8#32 9#32 6#32 10#32)
-- out-of-range pos/size, and pos+size > 32, are all rejected
#guard (assemble "ext $t0, $t1, 32, 1\n").isOk = false   -- pos out of range
#guard (assemble "ext $t0, $t1, 0, 33\n").isOk = false    -- size out of range
#guard (assemble "ext $t0, $t1, 30, 10\n").isOk = false   -- pos + size > 32
#guard (assemble "ins $t0, $t1, 30, 10\n").isOk = false   -- pos + size > 32

-- `jr $rs` / `jalr $rd, $rs`: real MIPS32 register-indirect jump/call,
-- opcode 0, funct 0x08/0x09. Also covers the `jalr $rs` one-operand sugar
-- (rd defaults to $ra = 31).
def jrJalrSrc : String := "jr $ra\njalr $t0, $t1\njalr $t2\n"
def jrJalrProg : Program :=
  match assemble jrJalrSrc with
  | .ok p => p
  | .error _ => ∅

#guard jrJalrProg.getD textBase 0 = mkRT (31#32) (0#32) (0#32) (0#32) (0x08#32)
#guard jrJalrProg.getD (textBase + 4#32) 0 = mkRT (9#32) (0#32) (8#32) (0#32) (0x09#32)
#guard jrJalrProg.getD (textBase + 8#32) 0 = mkRT (10#32) (0#32) (31#32) (0#32) (0x09#32)
#guard decode (jrJalrProg.getD textBase 0) = some (.jr 31#32)
#guard decode (jrJalrProg.getD (textBase + 4#32) 0) = some (.jalr 9#32 8#32)
#guard decode (jrJalrProg.getD (textBase + 8#32) 0) = some (.jalr 10#32 31#32)
-- operand-count errors: zero/three operands are rejected for both mnemonics.
#guard (assemble "jr\n").isOk = false
#guard (assemble "jr $t0, $t1\n").isOk = false
#guard (assemble "jalr\n").isOk = false
#guard (assemble "jalr $t0, $t1, $t2\n").isOk = false

-- `mthi`/`mtlo $rs`: opcode 0, funct 0x11/0x13, single-operand `rs` shape
-- (same as `jr`), cross-checked against `Instruction.encode`.
def mthiMtloSrc : String := "mthi $t0\nmtlo $t0\n"
def mthiMtloProg : Program :=
  match assemble mthiMtloSrc with
  | .ok p => p
  | .error _ => ∅

#guard mthiMtloProg.getD textBase 0 = encode (.mthi 8#32)
#guard mthiMtloProg.getD (textBase + 4#32) 0 = encode (.mtlo 8#32)
#guard decode (mthiMtloProg.getD textBase 0) = some (.mthi 8#32)
#guard decode (mthiMtloProg.getD (textBase + 4#32) 0) = some (.mtlo 8#32)
#guard (assemble "mthi\n").isOk = false
#guard (assemble "mthi $t0, $t1\n").isOk = false

-- `break`: zero operands, all fields zero except funct = 0x0d (0x0000000D);
-- real MIPS32 encoding (the funct value immediately after `syscall`'s
-- 0x0c) -- see `Instruction.lean`'s `encode .break`.
def breakSrc : String := "break\n"
def breakProg : Program :=
  match assemble breakSrc with
  | .ok p => p
  | .error _ => ∅

#guard breakProg.getD textBase 0 = 0x0000000D#32
#guard decode (breakProg.getD textBase 0) = some .break
#guard (assemble "break $t0\n").isOk = false

-- trap-on-condition family: `rs, rt` operands, same shape as `mult`/`div`.
def trapSrc : String := "teq $t0, $t1\ntne $t0, $t1\ntlt $t0, $t1\ntge $t0, $t1\ntltu $t0, $t1\ntgeu $t0, $t1\n"
def trapProg : Program :=
  match assemble trapSrc with
  | .ok p => p
  | .error _ => ∅

#guard trapProg.getD textBase 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x34#32)
#guard decode (trapProg.getD textBase 0) = some (.teq 8#32 9#32)
#guard trapProg.getD (textBase + 4#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x36#32)
#guard decode (trapProg.getD (textBase + 4#32) 0) = some (.tne 8#32 9#32)
#guard trapProg.getD (textBase + 8#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x32#32)
#guard decode (trapProg.getD (textBase + 8#32) 0) = some (.tlt 8#32 9#32)
#guard trapProg.getD (textBase + 12#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x30#32)
#guard decode (trapProg.getD (textBase + 12#32) 0) = some (.tge 8#32 9#32)
#guard trapProg.getD (textBase + 16#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x33#32)
#guard decode (trapProg.getD (textBase + 16#32) 0) = some (.tltu 8#32 9#32)
#guard trapProg.getD (textBase + 20#32) 0 = mkRT (8#32) (9#32) (0#32) (0#32) (0x31#32)
#guard decode (trapProg.getD (textBase + 20#32) 0) = some (.tgeu 8#32 9#32)
#guard (assemble "teq $t0\n").isOk = false

-- REGIMM zero-comparison branches: `bltz`/`bgez`/`bltzal`/`bgezal` all
-- share opcode 0x01 (distinguished only by the `rt` field — see
-- `Instruction.lean`/`docs/spec/INSTRUCTION-REF.md`); operand shape is
-- `rs, target`, same as `blez`/`bgtz`.
def regimmSrc : String :=
"loop: bltz $t0, loop\n" ++
"bgez $t0, loop\n" ++
"bltzal $t0, loop\n" ++
"bgezal $t0, loop\n"
def regimmProg : Program :=
  match assemble regimmSrc with
  | .ok p => p
  | .error _ => ∅

-- `loop: bltz $t0, loop`: instrAddr = textBase = target; nextPc = +4;
-- offset = (target - nextPc)/4 = -1.
#guard regimmProg.getD textBase 0 = mkIT (0x01#32) (8#32) (0x00#32) (ofInt32 (-1))
#guard decode (regimmProg.getD textBase 0) = some (.bltz 8#32 0xffff#32)
-- `bgez $t0, loop`: instrAddr = textBase+4, nextPc = textBase+8,
-- target = textBase (loop); offset = (0 - 8)/4 = -2.
#guard regimmProg.getD (textBase + 4#32) 0 = mkIT (0x01#32) (8#32) (0x01#32) (ofInt32 (-2))
#guard decode (regimmProg.getD (textBase + 4#32) 0) = some (.bgez 8#32 0xfffe#32)
-- `bltzal $t0, loop`: instrAddr = textBase+8, nextPc = textBase+12;
-- offset = (0 - 12)/4 = -3.
#guard regimmProg.getD (textBase + 8#32) 0 = mkIT (0x01#32) (8#32) (0x10#32) (ofInt32 (-3))
#guard decode (regimmProg.getD (textBase + 8#32) 0) = some (.bltzal 8#32 0xfffd#32)
-- `bgezal $t0, loop`: instrAddr = textBase+12, nextPc = textBase+16;
-- offset = (0 - 16)/4 = -4.
#guard regimmProg.getD (textBase + 12#32) 0 = mkIT (0x01#32) (8#32) (0x11#32) (ofInt32 (-4))
#guard decode (regimmProg.getD (textBase + 12#32) 0) = some (.bgezal 8#32 0xfffc#32)
#guard (assemble "bltz $t0\n").isOk = false

-- Trap-immediate family: `rs, imm` operands (a plain immediate, not a
-- branch target), same REGIMM opcode 0x01 as `bltz`/etc. above, selected
-- by the `rt` field (docs/spec/MIPS-COVERAGE-GAPS.md section 3.8).
def trapImmSrc : String :=
  "teqi $t0, 5\n" ++ "tnei $t0, 5\n" ++ "tgei $t0, 5\n" ++
  "tgeiu $t0, 5\n" ++ "tlti $t0, 5\n" ++ "tltiu $t0, 5\n"
def trapImmProg : Program :=
  match assemble trapImmSrc with
  | .ok p => p
  | .error _ => ∅

#guard trapImmProg.getD textBase 0 = mkIT (0x01#32) (8#32) (0x0c#32) (5#32)
#guard decode (trapImmProg.getD textBase 0) = some (.teqi 8#32 5#32)
#guard trapImmProg.getD (textBase + 4#32) 0 = mkIT (0x01#32) (8#32) (0x0e#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 4#32) 0) = some (.tnei 8#32 5#32)
#guard trapImmProg.getD (textBase + 8#32) 0 = mkIT (0x01#32) (8#32) (0x08#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 8#32) 0) = some (.tgei 8#32 5#32)
#guard trapImmProg.getD (textBase + 12#32) 0 = mkIT (0x01#32) (8#32) (0x09#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 12#32) 0) = some (.tgeiu 8#32 5#32)
#guard trapImmProg.getD (textBase + 16#32) 0 = mkIT (0x01#32) (8#32) (0x0a#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 16#32) 0) = some (.tlti 8#32 5#32)
#guard trapImmProg.getD (textBase + 20#32) 0 = mkIT (0x01#32) (8#32) (0x0b#32) (5#32)
#guard decode (trapImmProg.getD (textBase + 20#32) 0) = some (.tltiu 8#32 5#32)
#guard (assemble "teqi $t0\n").isOk = false

-- Coprocessor-1 (FPU) mnemonics: cross-checked word-for-word against
-- `Instruction.encode` (an independent encoding path from this assembler's
-- `cop1RtWord`/`itWord`), covering registers/`$fN` parsing and every form.
def cop1Src : String :=
"mtc1 $t0, $f3\n" ++
"mfc1 $t1, $f3\n" ++
"lwc1 $f5, 4($sp)\n" ++
"swc1 $f5, 4($sp)\n" ++
"add.s $f8, $f7, $f6\n" ++
"sub.s $f8, $f7, $f6\n" ++
"mul.s $f8, $f7, $f6\n" ++
"div.s $f8, $f7, $f6\n" ++
"mov.s $f8, $f7\n" ++
"cvt.s.w $f8, $f7\n" ++
"cvt.w.s $f8, $f7\n" ++
"c.eq.s $f7, $f6\n" ++
"c.lt.s $f7, $f6\n" ++
"c.le.s $f7, $f6\n" ++
"loop: bc1t loop\n" ++
"bc1f loop\n" ++
"cfc1 $t0, $f31\n" ++
"ctc1 $t0, $f31\n" ++
"sqrt.s $f8, $f7\n" ++
"abs.s $f8, $f7\n" ++
"neg.s $f8, $f7\n" ++
"round.w.s $f8, $f7\n" ++
"trunc.w.s $f8, $f7\n" ++
"ceil.w.s $f8, $f7\n" ++
"floor.w.s $f8, $f7\n" ++
"c.f.s $f7, $f6\n" ++
"c.un.s $f7, $f6\n" ++
"c.ueq.s $f7, $f6\n" ++
"c.olt.s $f7, $f6\n" ++
"c.ult.s $f7, $f6\n" ++
"c.ole.s $f7, $f6\n" ++
"c.ule.s $f7, $f6\n"

def cop1Prog : Program :=
  match assemble cop1Src with
  | .ok p => p
  | .error _ => ∅

#guard cop1Prog.getD textBase 0 = encode (.mtc1 8#32 3#32)
#guard cop1Prog.getD (textBase + 4#32) 0 = encode (.mfc1 9#32 3#32)
#guard cop1Prog.getD (textBase + 8#32) 0 = encode (.lwc1 29#32 5#32 4#32)
#guard cop1Prog.getD (textBase + 12#32) 0 = encode (.swc1 29#32 5#32 4#32)
#guard cop1Prog.getD (textBase + 16#32) 0 = encode (.addS 8#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 20#32) 0 = encode (.subS 8#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 24#32) 0 = encode (.mulS 8#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 28#32) 0 = encode (.divS 8#32 7#32 6#32)
#guard cop1Prog.getD (textBase + 32#32) 0 = encode (.movS 8#32 7#32)
#guard cop1Prog.getD (textBase + 36#32) 0 = encode (.cvtSW 8#32 7#32)
#guard cop1Prog.getD (textBase + 40#32) 0 = encode (.cvtWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 44#32) 0 = encode (.cEqS 7#32 6#32)
#guard cop1Prog.getD (textBase + 48#32) 0 = encode (.cLtS 7#32 6#32)
#guard cop1Prog.getD (textBase + 52#32) 0 = encode (.cLeS 7#32 6#32)
-- `loop: bc1t loop`: instrAddr = textBase+56 = target; nextPc = +4;
-- offset = (target - nextPc)/4 = -1.
#guard cop1Prog.getD (textBase + 56#32) 0 = encode (.bc1t (ofInt32 (-1)))
-- `bc1f loop`: instrAddr = textBase+60, nextPc = textBase+64, target = loop
-- (textBase+56); offset = (56 - 64)/4 = -2.
#guard cop1Prog.getD (textBase + 60#32) 0 = encode (.bc1f (ofInt32 (-2)))
-- every emitted COP1 word also round-trips through `decode`
#guard decode (cop1Prog.getD textBase 0) = some (.mtc1 8#32 3#32)
#guard decode (cop1Prog.getD (textBase + 16#32) 0) = some (.addS 8#32 7#32 6#32)
-- `decode`'s `imm` is the raw 16-bit field (zero-extended), not the
-- sign-extended offset value, per `Instruction.lean`'s "raw field" convention
-- (same as `beq`/`bne`'s `imm`); -1 as that raw 16-bit field is 0xffff.
#guard decode (cop1Prog.getD (textBase + 56#32) 0) = some (.bc1t 0xffff#32)
-- v1.x addition mnemonics appended after `bc1f loop` (textBase+64 onward,
-- unlabeled so earlier addresses/offsets above are unaffected)
#guard cop1Prog.getD (textBase + 64#32) 0 = encode (.cfc1 8#32 31#32)
#guard cop1Prog.getD (textBase + 68#32) 0 = encode (.ctc1 8#32 31#32)
#guard cop1Prog.getD (textBase + 72#32) 0 = encode (.sqrtS 8#32 7#32)
#guard cop1Prog.getD (textBase + 76#32) 0 = encode (.absS 8#32 7#32)
#guard cop1Prog.getD (textBase + 80#32) 0 = encode (.negS 8#32 7#32)
#guard cop1Prog.getD (textBase + 84#32) 0 = encode (.roundWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 88#32) 0 = encode (.truncWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 92#32) 0 = encode (.ceilWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 96#32) 0 = encode (.floorWS 8#32 7#32)
#guard cop1Prog.getD (textBase + 100#32) 0 = encode (.cFS 7#32 6#32)
#guard cop1Prog.getD (textBase + 104#32) 0 = encode (.cUnS 7#32 6#32)
#guard cop1Prog.getD (textBase + 108#32) 0 = encode (.cUeqS 7#32 6#32)
#guard cop1Prog.getD (textBase + 112#32) 0 = encode (.cOltS 7#32 6#32)
#guard cop1Prog.getD (textBase + 116#32) 0 = encode (.cUltS 7#32 6#32)
#guard cop1Prog.getD (textBase + 120#32) 0 = encode (.cOleS 7#32 6#32)
#guard cop1Prog.getD (textBase + 124#32) 0 = encode (.cUleS 7#32 6#32)
-- a couple of the new words also round-trip through `decode`
#guard decode (cop1Prog.getD (textBase + 64#32) 0) = some (.cfc1 8#32 31#32)
#guard decode (cop1Prog.getD (textBase + 72#32) 0) = some (.sqrtS 8#32 7#32)
#guard decode (cop1Prog.getD (textBase + 100#32) 0) = some (.cFS 7#32 6#32)

-- an unknown `$f` register is a `badRegister` error
#guard (assemble "mov.s $f8, $f32\n").isOk = false

-- Coprocessor-1 (FPU) double-precision mnemonics (v2 addition): same
-- cross-check style as `cop1Src` above -- every emitted word is checked
-- word-for-word against `Instruction.encode`.
def cop1DSrc : String :=
"ldc1 $f5, 4($sp)\n" ++
"sdc1 $f5, 4($sp)\n" ++
"add.d $f8, $f7, $f6\n" ++
"sub.d $f8, $f7, $f6\n" ++
"mul.d $f8, $f7, $f6\n" ++
"div.d $f8, $f7, $f6\n" ++
"mov.d $f8, $f7\n" ++
"sqrt.d $f8, $f7\n" ++
"abs.d $f8, $f7\n" ++
"neg.d $f8, $f7\n" ++
"cvt.d.s $f8, $f7\n" ++
"cvt.s.d $f8, $f7\n" ++
"cvt.d.w $f8, $f7\n" ++
"cvt.w.d $f8, $f7\n" ++
"c.eq.d $f7, $f6\n" ++
"c.lt.d $f7, $f6\n" ++
"c.le.d $f7, $f6\n" ++
"c.f.d $f7, $f6\n" ++
"c.un.d $f7, $f6\n" ++
"c.ueq.d $f7, $f6\n" ++
"c.olt.d $f7, $f6\n" ++
"c.ult.d $f7, $f6\n" ++
"c.ole.d $f7, $f6\n" ++
"c.ule.d $f7, $f6\n"

def cop1DProg : Program :=
  match assemble cop1DSrc with
  | .ok p => p
  | .error _ => ∅

#guard cop1DProg.getD textBase 0 = encode (.ldc1 29#32 5#32 4#32)
#guard cop1DProg.getD (textBase + 4#32) 0 = encode (.sdc1 29#32 5#32 4#32)
#guard cop1DProg.getD (textBase + 8#32) 0 = encode (.addD 8#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 12#32) 0 = encode (.subD 8#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 16#32) 0 = encode (.mulD 8#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 20#32) 0 = encode (.divD 8#32 7#32 6#32)
#guard cop1DProg.getD (textBase + 24#32) 0 = encode (.movD 8#32 7#32)
#guard cop1DProg.getD (textBase + 28#32) 0 = encode (.sqrtD 8#32 7#32)
#guard cop1DProg.getD (textBase + 32#32) 0 = encode (.absD 8#32 7#32)
#guard cop1DProg.getD (textBase + 36#32) 0 = encode (.negD 8#32 7#32)
#guard cop1DProg.getD (textBase + 40#32) 0 = encode (.cvtDS 8#32 7#32)
#guard cop1DProg.getD (textBase + 44#32) 0 = encode (.cvtSD 8#32 7#32)
#guard cop1DProg.getD (textBase + 48#32) 0 = encode (.cvtDW 8#32 7#32)
#guard cop1DProg.getD (textBase + 52#32) 0 = encode (.cvtWD 8#32 7#32)
#guard cop1DProg.getD (textBase + 56#32) 0 = encode (.cEqD 7#32 6#32)
#guard cop1DProg.getD (textBase + 60#32) 0 = encode (.cLtD 7#32 6#32)
#guard cop1DProg.getD (textBase + 64#32) 0 = encode (.cLeD 7#32 6#32)
#guard cop1DProg.getD (textBase + 68#32) 0 = encode (.cFD 7#32 6#32)
#guard cop1DProg.getD (textBase + 72#32) 0 = encode (.cUnD 7#32 6#32)
#guard cop1DProg.getD (textBase + 76#32) 0 = encode (.cUeqD 7#32 6#32)
#guard cop1DProg.getD (textBase + 80#32) 0 = encode (.cOltD 7#32 6#32)
#guard cop1DProg.getD (textBase + 84#32) 0 = encode (.cUltD 7#32 6#32)
#guard cop1DProg.getD (textBase + 88#32) 0 = encode (.cOleD 7#32 6#32)
#guard cop1DProg.getD (textBase + 92#32) 0 = encode (.cUleD 7#32 6#32)
-- every emitted double-precision word also round-trips through `decode`
#guard decode (cop1DProg.getD textBase 0) = some (.ldc1 29#32 5#32 4#32)
#guard decode (cop1DProg.getD (textBase + 8#32) 0) = some (.addD 8#32 7#32 6#32)
#guard decode (cop1DProg.getD (textBase + 40#32) 0) = some (.cvtDS 8#32 7#32)
#guard decode (cop1DProg.getD (textBase + 56#32) 0) = some (.cEqD 7#32 6#32)

-- `ll`/`sc`: identical `rt, offset(rs)` parsing to `lw`/`sw`, cross-checked
-- against `Instruction.encode`.
def llscSrc : String :=
"ll $t0, 4($sp)\n" ++
"sc $t0, 4($sp)\n"

def llscProg : Program :=
  match assemble llscSrc with
  | .ok p => p
  | .error _ => ∅

#guard llscProg.getD textBase 0 = encode (.ll 29#32 8#32 4#32)
#guard llscProg.getD (textBase + 4#32) 0 = encode (.sc 29#32 8#32 4#32)
#guard decode (llscProg.getD textBase 0) = some (.ll 29#32 8#32 4#32)
#guard decode (llscProg.getD (textBase + 4#32) 0) = some (.sc 29#32 8#32 4#32)

-- Coprocessor-0 (CP0) register move / execution control: `mfc0`/`mtc0`
-- (`$rt, rd` with `rd` a plain numeric CP0 register reference, e.g.
-- `mfc0 $t0, 12` -- this model has no named CP0 register aliases) and
-- `eret`/`wait` (zero operands, like `break`). Cross-checked word-for-word
-- against `Instruction.encode`, same convention as the COP1 block above.
def cop0Src : String :=
"mfc0 $t0, 12\n" ++
"mtc0 $t0, 12\n" ++
"mfc0 $t1, 13\n" ++
"mtc0 $t1, 13\n" ++
"mfc0 $t2, 14\n" ++
"mtc0 $t2, 14\n" ++
"eret\n" ++
"wait\n"

def cop0Prog : Program :=
  match assemble cop0Src with
  | .ok p => p
  | .error _ => ∅

#guard cop0Prog.getD textBase 0 = encode (.mfc0 8#32 12#32)
#guard cop0Prog.getD (textBase + 4#32) 0 = encode (.mtc0 8#32 12#32)
#guard cop0Prog.getD (textBase + 8#32) 0 = encode (.mfc0 9#32 13#32)
#guard cop0Prog.getD (textBase + 12#32) 0 = encode (.mtc0 9#32 13#32)
#guard cop0Prog.getD (textBase + 16#32) 0 = encode (.mfc0 10#32 14#32)
#guard cop0Prog.getD (textBase + 20#32) 0 = encode (.mtc0 10#32 14#32)
#guard cop0Prog.getD (textBase + 24#32) 0 = encode .eret
#guard cop0Prog.getD (textBase + 28#32) 0 = encode .wait
-- every emitted CP0 word also round-trips through `decode`
#guard decode (cop0Prog.getD textBase 0) = some (.mfc0 8#32 12#32)
#guard decode (cop0Prog.getD (textBase + 4#32) 0) = some (.mtc0 8#32 12#32)
#guard decode (cop0Prog.getD (textBase + 24#32) 0) = some .eret
#guard decode (cop0Prog.getD (textBase + 28#32) 0) = some .wait
-- operand errors: wrong operand count, and a non-numeric `rd` token
-- (`mfc0`/`mtc0`'s second operand is a raw register number, not a `$`-named
-- register -- `parseCp0Register` has no label/register fallback).
#guard (assemble "mfc0 $t0\n").isOk = false
#guard (assemble "mfc0 $t0, $t1\n").isOk = false
#guard (assemble "mfc0 $t0, 32\n").isOk = false
#guard (assemble "eret $t0\n").isOk = false
#guard (assemble "wait $t0\n").isOk = false
-- `lwl`/`lwr`/`swl`/`swr`: identical `rt, offset(rs)` parsing to `lw`/`sw`,
-- cross-checked against `Instruction.encode`.
def unalignedSrc : String :=
"lwl $t0, 1($sp)\n" ++
"lwr $t0, 4($sp)\n" ++
"swl $t0, 1($sp)\n" ++
"swr $t0, 4($sp)\n"

def unalignedProg : Program :=
  match assemble unalignedSrc with
  | .ok p => p
  | .error _ => ∅

#guard unalignedProg.getD textBase 0 = encode (.lwl 29#32 8#32 1#32)
#guard unalignedProg.getD (textBase + 4#32) 0 = encode (.lwr 29#32 8#32 4#32)
#guard unalignedProg.getD (textBase + 8#32) 0 = encode (.swl 29#32 8#32 1#32)
#guard unalignedProg.getD (textBase + 12#32) 0 = encode (.swr 29#32 8#32 4#32)
#guard decode (unalignedProg.getD textBase 0) = some (.lwl 29#32 8#32 1#32)
#guard decode (unalignedProg.getD (textBase + 4#32) 0) = some (.lwr 29#32 8#32 4#32)
#guard decode (unalignedProg.getD (textBase + 8#32) 0) = some (.swl 29#32 8#32 1#32)
#guard decode (unalignedProg.getD (textBase + 12#32) 0) = some (.swr 29#32 8#32 4#32)

-- One error case per major `AsmError` kind.
#guard (assemble "frobnicate $t0, $t1\n").isOk = false

#guard (assemble "add $t0, $bogus, $t1\n").isOk = false

#guard (assemble "j nosuchlabel\n").isOk = false

#guard (assemble "li $t0, notanumber\n").isOk = false

#guard (assemble ".bogus 1,2,3\n").isOk = false

#guard (assemble "add $t0, $t1\n").isOk = false

#guard (assemble "foo: add $t0,$zero,$zero\nfoo: add $t1,$zero,$zero\n").isOk = false
