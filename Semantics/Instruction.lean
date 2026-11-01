import Semantics.Word
import Semantics.Types

/-!
# Instruction — the v1 MIPS instruction set, decode, and encode

Wave 1 module (DESIGN.md §4, worker C). Depends only on `Word` and `Types`
(foundation, read-only). Ground truth for every encoding below is
`docs/spec/INSTRUCTION-REF.md`.

All instruction variants carry their **raw** field values as `W32`s (not yet
sign/zero-extended, not yet interpreted as signed shift amounts, etc.) — the
Wave 2 `Step` worker is responsible for applying `signExt16` / `zeroExt16` /
`.toNat` / `.toInt` as each instruction's semantics require. This keeps
`decode`/`encode` a pure, total, reversible bit-layout transformation with no
semantic interpretation baked in.

Field-shape summary (see each constructor's docstring for details):
- R-type reg/reg/reg (`rs rt rd`): `add addu sub subu and or xor nor slt sltu
  movn movz` — `movn`/`movz` share the exact add/sub field shape but write
  `$rd` only conditionally on `$rt`.
- R-type shift (`rd rt shamt`): `sll srl sra` — note `rs` is unused/ignored.
- R-type variable shift (`rd rt rs`), MIPS32 (opcode 0, funct 0x04/0x06/0x07):
  `sllv srlv srav` — the shift amount is the *register* `$rs`'s low 5 bits
  (masked at execution time by `Step`), not a fixed `shamt` field; `shamt`
  itself is unused/fixed 0 in the encoding (v1.x addition; see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.4).
- R-type mult/div (`rs rt`): `mult multu div divu` — `rd`/`shamt` unused.
- R-type move (`rd`): `mflo mfhi` — `rs`/`rt`/`shamt` unused.
- R-type jump register (`rs`): `jr` — `rt`/`rd`/`shamt` unused. (`rs rd`): `jalr`
  — `rt`/`shamt` unused. Real MIPS32 register-indirect jump/call (MD00086
  §3.2); like `j`/`jal`, these get the standard one-instruction delay slot
  via `pendingBranch`, but the target comes from a register read instead of
  the 26-bit `target` field.
- R-type bit-count (`rs rd`), SPECIAL2 (opcode 0x1c): `clo clz` — the raw 32-bit
  encoding's `rt` field duplicates `rd` (a real MIPS32 hardware quirk; see each
  constructor's docstring), so it is not modeled as a separate `Instruction`
  field.
- R-type GPR multiply (`rs rt rd`), SPECIAL2 (opcode 0x1c, funct 0x02): `mul`
  — same `rs rt rd` field shape as `add`, but SPECIAL2-opcoded like `clo`/
  `clz`; writes the low 32 bits of the signed product directly to `$rd`
  (v1.x addition; see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5).
- R-type sign-extend (`rd rt`), SPECIAL3 BSHFL (opcode 0x1f, funct 0x20):
  `seb seh` — `rs` unused/fixed 0; distinguished from each other (and from
  other BSHFL sub-ops, none of which are in scope here) by the
  shamt-position sub-field (`0x10` for `seb`, `0x18` for `seh`).
- I-type arith/logic (`rs rt imm`): `addi addiu slti sltiu andi ori xori`.
- I-type `lui` (`rt imm`): `rs` is unused/fixed 0.
- I-type load/store (`rs rt imm`): `lw sw lb lbu lh lhu sh` — `rs` is the base
  register, `rt` is the destination (loads) or source (stores) register,
  `imm` is the raw 16-bit offset field (not yet sign-extended).
- I-type load-linked/store-conditional (`rs rt imm`), same field shape as
  `lw`/`sw`: `ll sc` — real MIPS32 atomic synchronization primitives (opcodes
  0x30/0x38); not part of the original v1 instruction set, added as the
  `State.llBit` single-hart model (see `Types.lean`'s `llBit` docstring and
  `docs/spec/INSTRUCTION-REF.md`).
- I-type branch reg/reg (`rs rt imm`): `beq bne`.
- I-type branch reg-only (`rs imm`): `blez bgtz` — `rt` is unused/fixed 0.
- J-type (`target`): `j jal` — raw 26-bit target field (not yet shifted/combined
  with `PC_next`'s top 4 bits; that composition is `Step`'s job).
- No fields: `syscall` — the syscall *number* lives in `$v0` at execution
  time (MARS convention), so the instruction word carries no operand data
  beyond `opcode=0`/`funct=0x0c`.
- R-type trap-on-condition (`rs rt`, same shape as `mult`/`div`; `rd`/`shamt`
  unused): `teq tne tlt tge tltu tgeu` — real MIPS32 SPECIAL-opcode trap
  family, not part of the original v1 instruction set but added as a
  minimal coprocessor-0 trap/exception model (see `docs/spec/INSTRUCTION-REF.md`
  and `Semantics/Step.lean` for the exception-taken semantics). Ground
  truth is the real MIPS32 ISA (not MARS, which models exceptions only very
  loosely) — funct values are cited per-constructor below.
- No fields: `break` — same shape as `syscall` (opcode 0, funct 0x0d, the
  very next funct value after `syscall`'s 0x0c), always raises an exception
  unconditionally; no operand data of any kind (real MIPS32 `break` does
  have an optional 20-bit "code" field packed into bits 25..6, but it is
  purely a software-visible hint with no architecturally-defined effect on
  the exception itself, so it is out of scope here — this is a deliberate
  simplification, not an oversight).
- Coprocessor-1 (FPU) single-precision subset — opcode `0x11` (COP1); real
  MIPS32 encoding, ground truth is the MIPS32 ISA (not MARS), cited in each
  constructor's docstring and in `docs/spec/INSTRUCTION-REF.md`'s
  floating-point section:
  - `mtc1`/`mfc1` (`rt fs`): raw GPR↔FPR bit-pattern move, no numeric
    conversion.
  - `lwc1`/`swc1` (`rs ft imm`): identical addressing to `lw`/`sw`, but the
    loaded/stored register is FP register `ft`.
  - `addS subS mulS divS` (`fd fs ft`): single-precision IEEE-754 arithmetic,
    field order matching the `add.s $fd, $fs, $ft` assembly operand order.
  - `movS` (`fd fs`): FP register raw-bit copy.
  - `cvtSW`/`cvtWS` (`fd fs`): int-bit-pattern↔float numeric conversion.
  - `cEqS cLtS cLeS` (`fs ft`): single-precision IEEE-754 comparison, sets
    `State.fpCondFlag`; only FP condition-code register 0 is modeled (see
    `Types.lean`'s `fpCondFlag` docstring).
  - `bc1t`/`bc1f` (`imm`): branch on `fpCondFlag`. Simplification flagged for
    integration: this v1.x addition does **not** model a branch delay slot
    (jumps immediately), matching this codebase's existing no-delay-slot
    convention for `beq`/`bne`/`j`/etc. (SPEC-NOTES §9.1), not real MIPS32
    hardware.
  Double-precision (`.d`) and the rest of the COP1 format (`sqrt.s`, `neg.s`,
  `abs.s`, `cvt.d.*`, `cvt.*.d`, multi-cc compares, `bc1tl`/`bc1fl`) are out
  of scope for this pass; see `docs/spec/INSTRUCTION-REF.md` for the
  documented follow-up.
-/

/-- The full v1 machine-instruction set (24 original real instructions plus
`syscall`, plus the 7 coprocessor-0 trap/exception instructions added on top
— `teq tne tlt tge tltu tgeu break` — for 31 real instructions plus
`syscall` in total). Each constructor's fields are the **raw** bit-field
values extracted from the 32-bit encoding — see the module docstring for
which fields each variant carries and INSTRUCTION-REF for the exact bit
layout and semantics. -/
inductive Instruction where
  -- R-type reg/reg/reg
  /-- `$rd = $rs + $rt`, signed; traps on overflow (opcode 0, funct 0x20). -/
  | add  (rs rt rd : W32)
  /-- `$rd = $rs + $rt`, wraps (opcode 0, funct 0x21). -/
  | addu (rs rt rd : W32)
  /-- `$rd = $rs - $rt`, signed; traps on overflow (opcode 0, funct 0x22). -/
  | sub  (rs rt rd : W32)
  /-- `$rd = $rs - $rt`, wraps (opcode 0, funct 0x23). -/
  | subu (rs rt rd : W32)
  /-- `$rd = $rs & $rt` (opcode 0, funct 0x24). -/
  | and  (rs rt rd : W32)
  /-- `$rd = $rs | $rt` (opcode 0, funct 0x25). -/
  | or   (rs rt rd : W32)
  /-- `$rd = $rs ^ $rt` (opcode 0, funct 0x26). -/
  | xor  (rs rt rd : W32)
  /-- `$rd = ~($rs | $rt)` (opcode 0, funct 0x27). -/
  | nor  (rs rt rd : W32)
  /-- `$rd = ($rs < $rt) ? 1 : 0`, signed (opcode 0, funct 0x2a). -/
  | slt  (rs rt rd : W32)
  /-- `$rd = ($rs <u $rt) ? 1 : 0`, unsigned (opcode 0, funct 0x2b). -/
  | sltu (rs rt rd : W32)
  /-- `$rd = $rs` if `$rt != 0`; `$rd` unchanged otherwise (a real conditional
  no-op, not "write 0") (opcode 0, funct 0x0b). MIPS32r2. -/
  | movn (rs rt rd : W32)
  /-- `$rd = $rs` if `$rt == 0`; `$rd` unchanged otherwise (opcode 0,
  funct 0x0a). MIPS32r2. -/
  | movz (rs rt rd : W32)
  -- R-type shift (rs unused)
  /-- `$rd = $rt << shamt`, logical (opcode 0, funct 0x00). -/
  | sll  (rd rt shamt : W32)
  /-- `$rd = $rt >> shamt`, logical/zero-fill (opcode 0, funct 0x02). -/
  | srl  (rd rt shamt : W32)
  /-- `$rd = $rt >> shamt`, arithmetic/sign-fill (opcode 0, funct 0x03). -/
  | sra  (rd rt shamt : W32)
  -- R-type variable shift (opcode 0; shamt field unused/fixed 0). MIPS32
  -- v1.x addition: compilers emit these (not `sll`/`srl`/`sra`) whenever
  -- the shift amount is a runtime value rather than a compile-time
  -- constant (`docs/spec/MIPS-COVERAGE-GAPS.md` §3.4).
  /-- `$rd = $rt << ($rs & 0x1f)`, logical, shift amount from a register's
  low 5 bits (opcode 0, funct 0x04). MIPS32. -/
  | sllv (rd rt rs : W32)
  /-- `$rd = $rt >> ($rs & 0x1f)`, logical/zero-fill, shift amount from a
  register's low 5 bits (opcode 0, funct 0x06). MIPS32. -/
  | srlv (rd rt rs : W32)
  /-- `$rd = $rt >> ($rs & 0x1f)`, arithmetic/sign-fill, shift amount from a
  register's low 5 bits (opcode 0, funct 0x07). MIPS32. -/
  | srav (rd rt rs : W32)
  -- R-type mult/div (rd, shamt unused)
  /-- `{hi,lo} = $rs * $rt`, signed 64-bit (opcode 0, funct 0x18). -/
  | mult   (rs rt : W32)
  /-- `{hi,lo} = $rs * $rt`, unsigned 64-bit (opcode 0, funct 0x19). -/
  | multu  (rs rt : W32)
  /-- `lo = $rs / $rt; hi = $rs % $rt`, signed (opcode 0, funct 0x1a). -/
  | div    (rs rt : W32)
  /-- `lo = $rs / $rt; hi = $rs % $rt`, unsigned (opcode 0, funct 0x1b). -/
  | divu   (rs rt : W32)
  -- R-type move (rs, rt, shamt unused)
  /-- `$rd = lo` (opcode 0, funct 0x12). -/
  | mflo (rd : W32)
  /-- `$rd = hi` (opcode 0, funct 0x10). -/
  | mfhi (rd : W32)
  -- R-type jump register (rt, rd/shamt unused as noted per-constructor). Real
  -- MIPS32 register-indirect jump/call family — shares opcode 0 (SPECIAL)
  -- with the R-type arithmetic instructions above, distinguished by funct.
  /-- `PC = $rs`, after the usual one-instruction delay slot (opcode 0,
  funct 0x08). Real MIPS32 register-indirect jump (MD00086 §3.2); `rt`/`rd`/
  `shamt` are 0 in the real encoding and carry no information. The canonical
  function-return idiom is `jr $ra`. -/
  | jr (rs : W32)
  /-- `$rd = PC_next + 4` (the address of the instruction *after* the delay
  slot — same `pc + 8` link-value convention as `jal`); `PC = $rs`, after
  the usual one-instruction delay slot (opcode 0, funct 0x09). Real MIPS32
  register-indirect call (MD00086 §3.2), used for indirect procedure calls
  and function pointers (e.g. `jalr $t9`); `rt`/`shamt` are 0 in the real
  encoding and carry no information. -/
  | jalr (rs rd : W32)
  -- R-type SPECIAL2 bit-count (MIPS32). The real 32-bit encoding's `rt` field
  -- (bits 20..16) duplicates `rd` (bits 15..11) "because both fields hold the
  -- same register number" per the ISA; hardware does not read `rt` for these
  -- two instructions, so it carries no independent information and is not
  -- modeled as a separate field here (`encode` reconstructs the duplicate).
  /-- `$rd = ` the number of leading one bits in `$rs`, counted from the MSB
  (32 if `$rs` is all-ones) (SPECIAL2 opcode 0x1c, funct 0x21). MIPS32. -/
  | clo (rs rd : W32)
  /-- `$rd = ` the number of leading zero bits in `$rs`, counted from the MSB
  (32 if `$rs` is all-zero) (SPECIAL2 opcode 0x1c, funct 0x20). MIPS32. -/
  | clz (rs rd : W32)
  -- R-type GPR multiply, SPECIAL2 (MIPS32). Unlike `clo`/`clz`, this is a
  -- plain `rs rt rd` shape with no duplicated-field quirk.
  /-- `$rd = ` low 32 bits of `$rs * $rt`, signed (SPECIAL2 opcode 0x1c,
  funct 0x02). `hi`/`lo` are left **unchanged** by this dialect (real
  MIPS32 hardware leaves them architecturally unpredictable after `mul`;
  see `docs/spec/INSTRUCTION-REF.md` for the documented dialect choice).
  MIPS32. -/
  | mul (rs rt rd : W32)
  -- R-type SPECIAL3 BSHFL sign-extend (MIPS32r2). `rs` is unused/fixed 0;
  -- `funct` is 0x20 for the whole BSHFL sub-op family, and the shamt-position
  -- 5-bit sub-field (not a real shift amount here) selects which one.
  /-- `$rd = sign-extend($rt[7:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x10). MIPS32r2. -/
  | seb (rd rt : W32)
  /-- `$rd = sign-extend($rt[15:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x18). MIPS32r2. -/
  | seh (rd rt : W32)
  -- I-type arith/logic
  /-- `$rt = $rs + sext16(imm)`, traps on overflow (opcode 0x08). -/
  | addi  (rs rt imm : W32)
  /-- `$rt = $rs + sext16(imm)`, wraps (opcode 0x09). -/
  | addiu (rs rt imm : W32)
  /-- `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed (opcode 0x0a). -/
  | slti  (rs rt imm : W32)
  /-- `$rt = ($rs <u sext16(imm)) ? 1 : 0` (opcode 0x0b). -/
  | sltiu (rs rt imm : W32)
  /-- `$rt = $rs & zext16(imm)` (opcode 0x0c). -/
  | andi  (rs rt imm : W32)
  /-- `$rt = $rs | zext16(imm)` (opcode 0x0d). -/
  | ori   (rs rt imm : W32)
  /-- `$rt = $rs ^ zext16(imm)` (opcode 0x0e). -/
  | xori  (rs rt imm : W32)
  -- I-type lui (rs unused/fixed 0)
  /-- `$rt = imm << 16` (opcode 0x0f). -/
  | lui   (rt imm : W32)
  -- I-type load/store: rs = base, rt = dest/src, imm = raw offset field
  /-- `$rt = MEM32[$rs + offset]`, word-aligned (opcode 0x23). -/
  | lw  (rs rt imm : W32)
  /-- `MEM32[$rs + offset] = $rt`, word-aligned (opcode 0x2b). -/
  | sw  (rs rt imm : W32)
  /-- `$rt = sext8(MEM8[$rs + offset])` (opcode 0x20). -/
  | lb  (rs rt imm : W32)
  /-- `$rt = zext8(MEM8[$rs + offset])` (opcode 0x24). -/
  | lbu (rs rt imm : W32)
  /-- `$rt = sext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x21). -/
  | lh  (rs rt imm : W32)
  /-- `$rt = zext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x25). -/
  | lhu (rs rt imm : W32)
  /-- `MEM16[$rs + offset] = $rt[15:0]`, halfword-aligned (opcode 0x29). -/
  | sh  (rs rt imm : W32)
  /-- `$rt = MEM32[$rs + offset]`, word-aligned, and sets `State.llBit`
  (real MIPS32 "Load Linked Word", opcode 0x30; MD00086 Rev 2.50 §3.2,
  Table 3-4). Identical addressing/alignment to `lw`; see
  `docs/spec/INSTRUCTION-REF.md` for the paired `sc` semantics and this
  model's single-hart `llBit` simplification. -/
  | ll  (rs rt imm : W32)
  /-- Conditionally `MEM32[$rs + offset] = $rt`, word-aligned, based on
  `State.llBit`: if set, performs the store and writes `1` to `$rt`;
  otherwise the store does not happen and `0` is written to `$rt`. Either
  way, clears `llBit` (real MIPS32 "Store Conditional Word", opcode 0x38;
  MD00086 Rev 2.50 §3.2, Table 3-4). Identical addressing/alignment to
  `sw`. -/
  | sc  (rs rt imm : W32)
  -- I-type branch reg/reg
  /-- `if $rs == $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x04). -/
  | beq (rs rt imm : W32)
  /-- `if $rs != $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x05). -/
  | bne (rs rt imm : W32)
  -- I-type branch reg-only (rt unused/fixed 0)
  /-- `if $rs <= 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x06). -/
  | blez (rs imm : W32)
  /-- `if $rs > 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x07). -/
  | bgtz (rs imm : W32)
  -- I-type REGIMM zero-comparison branches (MIPS32 ISA; opcode 0x01). All
  -- four share this one opcode; the `rt` field (not a separate opcode)
  -- selects which instruction it is (ground truth: MD00086 Rev 2.50 §3.2,
  -- Table 3-2, p. 25; see docs/spec/INSTRUCTION-REF.md for the full
  -- citation). Same `rs, offset` field shape as `blez`/`bgtz`.
  /-- `if $rs < 0 then PC = PC_next + (sext16(imm) << 2)`, signed
  (opcode 0x01, `rt` field = 0x00 `BLTZ`). -/
  | bltz (rs imm : W32)
  /-- `if $rs >= 0 then PC = PC_next + (sext16(imm) << 2)`, signed
  (opcode 0x01, `rt` field = 0x01 `BGEZ`). -/
  | bgez (rs imm : W32)
  /-- `$ra = PC_next + 4` unconditionally, **then** `if $rs < 0 then
  PC = PC_next + (sext16(imm) << 2)`, signed (opcode 0x01, `rt` field = 0x10
  `BLTZAL`). Real MIPS32: the link into `$ra` always happens (it is not
  conditional on the branch being taken), same convention as `jal`'s link —
  see docs/spec/INSTRUCTION-REF.md for the citation. The real ISA
  pseudocode links `$ra` one cycle before testing `$rs`, so `rs = $ra` (31)
  is architecturally UNPREDICTABLE (the test could observe either the old
  or the freshly-linked value); `Step.lean` resolves this by testing the
  pre-link value of `$rs`, a documented, defensible choice for an
  explicitly-unspecified case rather than an oversight. -/
  | bltzal (rs imm : W32)
  /-- `$ra = PC_next + 4` unconditionally, **then** `if $rs >= 0 then
  PC = PC_next + (sext16(imm) << 2)`, signed (opcode 0x01, `rt` field = 0x11
  `BGEZAL`). Same unconditional-link convention and `rs = $ra`
  UNPREDICTABLE-case resolution as `bltzal`. -/
  | bgezal (rs imm : W32)
  -- J-type
  /-- `PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x02). -/
  | j   (target : W32)
  /-- `$ra = PC_next; PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x03). -/
  | jal (target : W32)
  -- syscall (no fields; the syscall number lives in $v0 at execution time)
  /-- Dispatch on `$v0` (opcode 0, funct 0x0c); MARS syscalls 1/4/10/11 in v1 scope. -/
  | syscall
  -- R-type trap-on-condition (rd, shamt unused) — real MIPS32 SPECIAL-opcode
  -- trap family. Not modeled realistically by MARS (see
  -- docs/spec/INSTRUCTION-REF.md); funct values below are the standard
  -- MIPS32 ISA encoding, cited from the real architecture, not MARS.
  /-- `if $rs == $rt then trap` (opcode 0, funct 0x34). -/
  | teq (rs rt : W32)
  /-- `if $rs != $rt then trap` (opcode 0, funct 0x36). -/
  | tne (rs rt : W32)
  /-- `if $rs < $rt then trap`, signed (opcode 0, funct 0x32). -/
  | tlt (rs rt : W32)
  /-- `if $rs >= $rt then trap`, signed (opcode 0, funct 0x30). -/
  | tge (rs rt : W32)
  /-- `if $rs <u $rt then trap`, unsigned (opcode 0, funct 0x33). -/
  | tltu (rs rt : W32)
  /-- `if $rs >=u $rt then trap`, unsigned (opcode 0, funct 0x31). -/
  | tgeu (rs rt : W32)
  -- break (no fields; see module docstring — the real "code" field is
  -- out of scope)
  /-- Unconditional trap (opcode 0, funct 0x0d — the funct value immediately
  after `syscall`'s 0x0c). -/
  | break
  -- Coprocessor 1 (FPU), single-precision subset. Ground truth: the MIPS32
  -- ISA (not MARS) "COP1" encodings; see docs/spec/INSTRUCTION-REF.md's
  -- floating-point section for the full citation and scope notes.
  /-- `$rt = rawbits($fs)`, no numeric conversion (opcode 0x11 COP1, `fmt`
  field = `MF` = 0x00). -/
  | mfc1 (rt fs : W32)
  /-- `$fs = rawbits($rt)`, no numeric conversion (opcode 0x11 COP1, `fmt`
  field = `MT` = 0x04). -/
  | mtc1 (rt fs : W32)
  /-- `$ft = MEM32[$rs + offset]`, word-aligned, raw bits (opcode 0x31). -/
  | lwc1 (rs ft imm : W32)
  /-- `MEM32[$rs + offset] = rawbits($ft)`, word-aligned (opcode 0x39). -/
  | swc1 (rs ft imm : W32)
  /-- `$fd = $fs + $ft`, single-precision IEEE-754 (opcode 0x11 COP1,
  `fmt` = `S` = 0x10, `funct` = 0x00 `ADD.S`). -/
  | addS (fd fs ft : W32)
  /-- `$fd = $fs - $ft`, single-precision IEEE-754 (opcode 0x11 COP1,
  `fmt` = `S`, `funct` = 0x01 `SUB.S`). -/
  | subS (fd fs ft : W32)
  /-- `$fd = $fs * $ft`, single-precision IEEE-754 (opcode 0x11 COP1,
  `fmt` = `S`, `funct` = 0x02 `MUL.S`). -/
  | mulS (fd fs ft : W32)
  /-- `$fd = $fs / $ft`, single-precision IEEE-754 (opcode 0x11 COP1,
  `fmt` = `S`, `funct` = 0x03 `DIV.S`); division by zero produces ±Infinity
  or NaN per IEEE-754, no trap (SPEC-NOTES §9 item 2 precedent). -/
  | divS (fd fs ft : W32)
  /-- `$fd = $fs`, raw bit copy (opcode 0x11 COP1, `fmt` = `S`, `funct` = 0x06
  `MOV.S`; `ft`-position field unused/fixed 0). -/
  | movS (fd fs : W32)
  /-- `$fd = float32(int32bits($fs))`, numeric conversion of `$fs`'s bit
  pattern read as a 32-bit two's-complement int (opcode 0x11 COP1,
  `fmt` = `W` = 0x14, `funct` = 0x20 `CVT.S.W`; `ft`-position field unused). -/
  | cvtSW (fd fs : W32)
  /-- `$fd = int32bits(truncate($fs))`, numeric conversion truncating toward
  zero (opcode 0x11 COP1, `fmt` = `S`, `funct` = 0x24 `CVT.W.S`;
  `ft`-position field unused). Real MIPS32 rounds per the current FCSR
  rounding mode (default round-to-nearest-even); this v1.x addition always
  truncates toward zero, a documented simplification pinned by this track's
  brief (no `FCSR` in scope). -/
  | cvtWS (fd fs : W32)
  /-- `fpCondFlag := ($fs == $ft)`, IEEE-754 single-precision compare (opcode
  0x11 COP1, `fmt` = `S`, `funct` = 0x32 `C.EQ.S`; FP condition-code field
  fixed to `cc = 0`). -/
  | cEqS (fs ft : W32)
  /-- `fpCondFlag := ($fs < $ft)`, IEEE-754 single-precision compare (opcode
  0x11 COP1, `fmt` = `S`, `funct` = 0x3c `C.LT.S`; `cc` fixed 0). -/
  | cLtS (fs ft : W32)
  /-- `fpCondFlag := ($fs <= $ft)`, IEEE-754 single-precision compare (opcode
  0x11 COP1, `fmt` = `S`, `funct` = 0x3e `C.LE.S`; `cc` fixed 0). -/
  | cLeS (fs ft : W32)
  /-- `if fpCondFlag then PC = PC_next + (sext16(imm) << 2)` (opcode 0x11
  COP1, `fmt` = `BC1` = 0x08, `tf` bit = 1). No delay slot modeled — see
  the module docstring's COP1 bullet. -/
  | bc1t (imm : W32)
  /-- `if !fpCondFlag then PC = PC_next + (sext16(imm) << 2)` (opcode 0x11
  COP1, `fmt` = `BC1` = 0x08, `tf` bit = 0). No delay slot modeled — see
  the module docstring's COP1 bullet. -/
  | bc1f (imm : W32)
  deriving Repr, DecidableEq

/-- Extract the 6-bit opcode field (bits 31..26), zero-extended to a `W32`. -/
private def opcodeOf (w : W32) : W32 := (w.extractLsb 31 26).zeroExtend 32

/-- Extract the 5-bit `rs` field (bits 25..21), zero-extended to a `W32`. -/
private def rsOf (w : W32) : W32 := (w.extractLsb 25 21).zeroExtend 32

/-- Extract the 5-bit `rt` field (bits 20..16), zero-extended to a `W32`. -/
private def rtOf (w : W32) : W32 := (w.extractLsb 20 16).zeroExtend 32

/-- Extract the 5-bit `rd` field (bits 15..11), zero-extended to a `W32`. -/
private def rdOf (w : W32) : W32 := (w.extractLsb 15 11).zeroExtend 32

/-- Extract the 5-bit `shamt` field (bits 10..6), zero-extended to a `W32`. -/
private def shamtOf (w : W32) : W32 := (w.extractLsb 10 6).zeroExtend 32

/-- Extract the 6-bit `funct` field (bits 5..0), zero-extended to a `W32`. -/
private def functOf (w : W32) : W32 := (w.extractLsb 5 0).zeroExtend 32

/-- Extract the raw 16-bit immediate/offset field (bits 15..0), zero-extended
to a `W32` with no sign interpretation applied. -/
private def immOf (w : W32) : W32 := (w.extractLsb 15 0).zeroExtend 32

/-- Extract the raw 26-bit jump-target field (bits 25..0), zero-extended to a `W32`. -/
private def targetOf (w : W32) : W32 := (w.extractLsb 25 0).zeroExtend 32

/-- Decode a raw 32-bit instruction word into an `Instruction`, or `none` if
the opcode/funct combination is not in the v1 instruction set. Ground truth:
`docs/spec/INSTRUCTION-REF.md`. -/
def decode (w : W32) : Option Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let imm := immOf w
  let target := targetOf w
  match (opcodeOf w).toNat with
  | 0x00 =>
    match (functOf w).toNat with
    | 0x20 => some (.add rs rt rd)
    | 0x21 => some (.addu rs rt rd)
    | 0x22 => some (.sub rs rt rd)
    | 0x23 => some (.subu rs rt rd)
    | 0x24 => some (.and rs rt rd)
    | 0x25 => some (.or rs rt rd)
    | 0x26 => some (.xor rs rt rd)
    | 0x27 => some (.nor rs rt rd)
    | 0x2a => some (.slt rs rt rd)
    | 0x2b => some (.sltu rs rt rd)
    | 0x0b => some (.movn rs rt rd)
    | 0x0a => some (.movz rs rt rd)
    | 0x00 => some (.sll rd rt shamt)
    | 0x02 => some (.srl rd rt shamt)
    | 0x03 => some (.sra rd rt shamt)
    | 0x04 => some (.sllv rd rt rs)
    | 0x06 => some (.srlv rd rt rs)
    | 0x07 => some (.srav rd rt rs)
    | 0x18 => some (.mult rs rt)
    | 0x19 => some (.multu rs rt)
    | 0x1a => some (.div rs rt)
    | 0x1b => some (.divu rs rt)
    | 0x12 => some (.mflo rd)
    | 0x10 => some (.mfhi rd)
    | 0x08 => some (.jr rs)
    | 0x09 => some (.jalr rs rd)
    | 0x0c => some .syscall
    | 0x0d => some .break
    | 0x34 => some (.teq rs rt)
    | 0x36 => some (.tne rs rt)
    | 0x32 => some (.tlt rs rt)
    | 0x30 => some (.tge rs rt)
    | 0x33 => some (.tltu rs rt)
    | 0x31 => some (.tgeu rs rt)
    | _ => none
  | 0x1c =>  -- SPECIAL2: bit-count (rt field is the rd/rt-duplication quirk; ignored)
    match (functOf w).toNat with
    | 0x21 => some (.clo rs rd)
    | 0x20 => some (.clz rs rd)
    | 0x02 => some (.mul rs rt rd)
    | _ => none
  | 0x1f =>  -- SPECIAL3: BSHFL sign-extend family, selected by the shamt sub-field
    match (functOf w).toNat with
    | 0x20 =>
      match shamt.toNat with
      | 0x10 => some (.seb rd rt)
      | 0x18 => some (.seh rd rt)
      | _ => none
    | _ => none
  | 0x08 => some (.addi rs rt imm)
  | 0x09 => some (.addiu rs rt imm)
  | 0x0a => some (.slti rs rt imm)
  | 0x0b => some (.sltiu rs rt imm)
  | 0x0c => some (.andi rs rt imm)
  | 0x0d => some (.ori rs rt imm)
  | 0x0e => some (.xori rs rt imm)
  | 0x0f => some (.lui rt imm)
  | 0x23 => some (.lw rs rt imm)
  | 0x2b => some (.sw rs rt imm)
  | 0x20 => some (.lb rs rt imm)
  | 0x24 => some (.lbu rs rt imm)
  | 0x21 => some (.lh rs rt imm)
  | 0x25 => some (.lhu rs rt imm)
  | 0x29 => some (.sh rs rt imm)
  | 0x30 => some (.ll rs rt imm)
  | 0x38 => some (.sc rs rt imm)
  | 0x04 => some (.beq rs rt imm)
  | 0x05 => some (.bne rs rt imm)
  | 0x06 => some (.blez rs imm)
  | 0x07 => some (.bgtz rs imm)
  | 0x01 =>  -- REGIMM: rt field (not the opcode) selects bltz/bgez/bltzal/bgezal
    match rt.toNat with
    | 0x00 => some (.bltz rs imm)
    | 0x01 => some (.bgez rs imm)
    | 0x10 => some (.bltzal rs imm)
    | 0x11 => some (.bgezal rs imm)
    | _ => none
  | 0x02 => some (.j target)
  | 0x03 => some (.jal target)
  | 0x31 => some (.lwc1 rs rt imm)
  | 0x39 => some (.swc1 rs rt imm)
  -- Coprocessor 1 (FPU): `rs`-position field is `fmt`/sub-opcode, `rt` is
  -- `ft` (or the GPR for mtc1/mfc1), `rd` is `fs` (or `ft` for arithmetic
  -- format, see each case), `shamt` is `fd` for arithmetic format.
  | 0x11 =>
    match rs.toNat with
    | 0x00 => some (.mfc1 rt rd)  -- fmt = MF: rt = GPR, rd-position = fs
    | 0x04 => some (.mtc1 rt rd)  -- fmt = MT
    | 0x08 =>
      -- BC1: `rt`-position field is `cc`(3)/`nd`(1)/`tf`(1); only cc=0,
      -- nd=0 (i.e. the field's raw value is exactly 0 or 1) is modeled.
      match rt.toNat with
      | 1 => some (.bc1t imm)
      | 0 => some (.bc1f imm)
      | _ => none
    | 0x10 =>  -- fmt = S: arithmetic/compare format, ft=rt, fs=rd, fd=shamt
      match (functOf w).toNat with
      | 0x00 => some (.addS shamt rd rt)
      | 0x01 => some (.subS shamt rd rt)
      | 0x02 => some (.mulS shamt rd rt)
      | 0x03 => some (.divS shamt rd rt)
      | 0x06 => some (.movS shamt rd)
      | 0x24 => some (.cvtWS shamt rd)
      -- `fd`-position field holds `cc`(3)/0/0 for compares; only cc=0 modeled.
      | 0x32 => if shamt.toNat == 0 then some (.cEqS rd rt) else none
      | 0x3c => if shamt.toNat == 0 then some (.cLtS rd rt) else none
      | 0x3e => if shamt.toNat == 0 then some (.cLeS rd rt) else none
      | _ => none
    | 0x14 =>  -- fmt = W
      match (functOf w).toNat with
      | 0x20 => some (.cvtSW shamt rd)
      | _ => none
    | _ => none
  | _ => none

/-- Encode an `Instruction` back into its raw 32-bit word. Inverse of `decode`
on the v1 instruction set. -/
def encode (i : Instruction) : W32 :=
  match i with
  | .add  rs rt rd => mkRT rs rt rd 0#32 0x20#32
  | .addu rs rt rd => mkRT rs rt rd 0#32 0x21#32
  | .sub  rs rt rd => mkRT rs rt rd 0#32 0x22#32
  | .subu rs rt rd => mkRT rs rt rd 0#32 0x23#32
  | .and  rs rt rd => mkRT rs rt rd 0#32 0x24#32
  | .or   rs rt rd => mkRT rs rt rd 0#32 0x25#32
  | .xor  rs rt rd => mkRT rs rt rd 0#32 0x26#32
  | .nor  rs rt rd => mkRT rs rt rd 0#32 0x27#32
  | .slt  rs rt rd => mkRT rs rt rd 0#32 0x2a#32
  | .sltu rs rt rd => mkRT rs rt rd 0#32 0x2b#32
  | .movn rs rt rd => mkRT rs rt rd 0#32 0x0b#32
  | .movz rs rt rd => mkRT rs rt rd 0#32 0x0a#32
  | .sll  rd rt shamt => mkRT 0#32 rt rd shamt 0x00#32
  | .srl  rd rt shamt => mkRT 0#32 rt rd shamt 0x02#32
  | .sra  rd rt shamt => mkRT 0#32 rt rd shamt 0x03#32
  | .sllv rd rt rs => mkRT rs rt rd 0#32 0x04#32
  | .srlv rd rt rs => mkRT rs rt rd 0#32 0x06#32
  | .srav rd rt rs => mkRT rs rt rd 0#32 0x07#32
  | .mult  rs rt => mkRT rs rt 0#32 0#32 0x18#32
  | .multu rs rt => mkRT rs rt 0#32 0#32 0x19#32
  | .div   rs rt => mkRT rs rt 0#32 0#32 0x1a#32
  | .divu  rs rt => mkRT rs rt 0#32 0#32 0x1b#32
  | .mflo rd => mkRT 0#32 0#32 rd 0#32 0x12#32
  | .mfhi rd => mkRT 0#32 0#32 rd 0#32 0x10#32
  | .jr   rs => mkRT rs 0#32 0#32 0#32 0x08#32
  | .jalr rs rd => mkRT rs 0#32 rd 0#32 0x09#32
  -- SPECIAL2: duplicate rd into the rt-position field per the real encoding.
  | .clo rs rd => (0x1c#32 <<< 26) ||| mkRT rs rd rd 0#32 0x21#32
  | .clz rs rd => (0x1c#32 <<< 26) ||| mkRT rs rd rd 0#32 0x20#32
  | .mul rs rt rd => (0x1c#32 <<< 26) ||| mkRT rs rt rd 0#32 0x02#32
  -- SPECIAL3 BSHFL: rs fixed 0, shamt-position field selects seb/seh.
  | .seb rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x10#32 0x20#32
  | .seh rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x18#32 0x20#32
  | .addi  rs rt imm => mkIT 0x08#32 rs rt imm
  | .addiu rs rt imm => mkIT 0x09#32 rs rt imm
  | .slti  rs rt imm => mkIT 0x0a#32 rs rt imm
  | .sltiu rs rt imm => mkIT 0x0b#32 rs rt imm
  | .andi  rs rt imm => mkIT 0x0c#32 rs rt imm
  | .ori   rs rt imm => mkIT 0x0d#32 rs rt imm
  | .xori  rs rt imm => mkIT 0x0e#32 rs rt imm
  | .lui   rt imm    => mkIT 0x0f#32 0#32 rt imm
  | .lw rs rt imm => mkIT 0x23#32 rs rt imm
  | .sw rs rt imm => mkIT 0x2b#32 rs rt imm
  | .lb rs rt imm => mkIT 0x20#32 rs rt imm
  | .lbu rs rt imm => mkIT 0x24#32 rs rt imm
  | .lh rs rt imm => mkIT 0x21#32 rs rt imm
  | .lhu rs rt imm => mkIT 0x25#32 rs rt imm
  | .sh rs rt imm => mkIT 0x29#32 rs rt imm
  | .ll rs rt imm => mkIT 0x30#32 rs rt imm
  | .sc rs rt imm => mkIT 0x38#32 rs rt imm
  | .beq rs rt imm => mkIT 0x04#32 rs rt imm
  | .bne rs rt imm => mkIT 0x05#32 rs rt imm
  | .blez rs imm => mkIT 0x06#32 rs 0#32 imm
  | .bgtz rs imm => mkIT 0x07#32 rs 0#32 imm
  | .bltz   rs imm => mkIT 0x01#32 rs 0x00#32 imm
  | .bgez   rs imm => mkIT 0x01#32 rs 0x01#32 imm
  | .bltzal rs imm => mkIT 0x01#32 rs 0x10#32 imm
  | .bgezal rs imm => mkIT 0x01#32 rs 0x11#32 imm
  | .j   target => (0x02#32 <<< 26) ||| mkJT target
  | .jal target => (0x03#32 <<< 26) ||| mkJT target
  | .syscall => mkRT 0#32 0#32 0#32 0#32 0x0c#32
  | .teq  rs rt => mkRT rs rt 0#32 0#32 0x34#32
  | .tne  rs rt => mkRT rs rt 0#32 0#32 0x36#32
  | .tlt  rs rt => mkRT rs rt 0#32 0#32 0x32#32
  | .tge  rs rt => mkRT rs rt 0#32 0#32 0x30#32
  | .tltu rs rt => mkRT rs rt 0#32 0#32 0x33#32
  | .tgeu rs rt => mkRT rs rt 0#32 0#32 0x31#32
  | .break => mkRT 0#32 0#32 0#32 0#32 0x0d#32
  -- Coprocessor 1 (FPU). `mkRT` leaves the opcode field 0 (correct for
  -- plain R-type), so the COP1 cases OR in opcode 0x11 explicitly, the same
  -- way `.j`/`.jal` OR in their opcode over `mkJT`'s target-only field.
  | .mfc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x00#32 rt fs 0#32 0#32
  | .mtc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x04#32 rt fs 0#32 0#32
  | .lwc1 rs ft imm => mkIT 0x31#32 rs ft imm
  | .swc1 rs ft imm => mkIT 0x39#32 rs ft imm
  | .addS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x00#32
  | .subS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x01#32
  | .mulS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x02#32
  | .divS fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs fd 0x03#32
  | .movS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x06#32
  | .cvtSW fd fs => (0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 fs fd 0x20#32
  | .cvtWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x24#32
  | .cEqS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x32#32
  | .cLtS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x3c#32
  | .cLeS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x3e#32
  | .bc1t imm => mkIT 0x11#32 0x08#32 1#32 imm
  | .bc1f imm => mkIT 0x11#32 0x08#32 0#32 imm

-- ## Tests

-- Each v1 instruction: hand-computed word (from INSTRUCTION-REF encodings,
-- distinct nontrivial field values) decodes to the expected variant.

-- R-type reg/reg/reg: rs=29, rt=8, rd=3
example : decode (mkRT 29#32 8#32 3#32 0#32 0x20#32) = some (.add 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x21#32) = some (.addu 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x22#32) = some (.sub 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x23#32) = some (.subu 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x24#32) = some (.and 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x25#32) = some (.or 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x26#32) = some (.xor 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x27#32) = some (.nor 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x2a#32) = some (.slt 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x2b#32) = some (.sltu 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x0b#32) = some (.movn 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x0a#32) = some (.movz 29#32 8#32 3#32) := by decide

-- R-type shift: rd=3, rt=8, shamt=5 (rs unused/0)
example : decode (mkRT 0#32 8#32 3#32 5#32 0x00#32) = some (.sll 3#32 8#32 5#32) := by decide
example : decode (mkRT 0#32 8#32 3#32 5#32 0x02#32) = some (.srl 3#32 8#32 5#32) := by decide
example : decode (mkRT 0#32 8#32 3#32 5#32 0x03#32) = some (.sra 3#32 8#32 5#32) := by decide

-- R-type variable shift: rd=3, rt=8, rs=29 (shamt field unused/0)
example : decode (mkRT 29#32 8#32 3#32 0#32 0x04#32) = some (.sllv 3#32 8#32 29#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x06#32) = some (.srlv 3#32 8#32 29#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x07#32) = some (.srav 3#32 8#32 29#32) := by decide

-- R-type mult/div: rs=29, rt=8
example : decode (mkRT 29#32 8#32 0#32 0#32 0x18#32) = some (.mult 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x19#32) = some (.multu 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x1a#32) = some (.div 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x1b#32) = some (.divu 29#32 8#32) := by decide

-- R-type move: rd=3
example : decode (mkRT 0#32 0#32 3#32 0#32 0x12#32) = some (.mflo 3#32) := by decide
example : decode (mkRT 0#32 0#32 3#32 0#32 0x10#32) = some (.mfhi 3#32) := by decide

-- syscall: opcode 0, funct 0x0c, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0c#32) = some .syscall := by decide

-- SPECIAL2 bit-count: rs=29, rd=3 (rt field duplicates rd=3, per the real encoding)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x21#32) = some (.clo 29#32 3#32) := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x20#32) = some (.clz 29#32 3#32) := by decide
-- decode also accepts the (nonconforming but documented-as-ignored) case
-- where the raw rt field does *not* match rd, since hardware doesn't read it.
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 17#32 3#32 0#32 0x21#32) = some (.clo 29#32 3#32) := by decide

-- SPECIAL2 GPR multiply: rs=29, rt=8, rd=3 (plain rs/rt/rd shape, no duplication quirk)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32) = some (.mul 29#32 8#32 3#32) := by decide

-- SPECIAL3 BSHFL sign-extend: rd=3, rt=8, sub-field selects seb vs seh
example : decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x10#32 0x20#32) = some (.seb 3#32 8#32) := by decide
example : decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x18#32 0x20#32) = some (.seh 3#32 8#32) := by decide
-- an unrecognized BSHFL sub-field (e.g. 0x02 = WSBH) is out of v1+ scope → none
#guard decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x02#32 0x20#32) = none
-- break: opcode 0, funct 0x0d, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0d#32) = some .break := by decide

-- R-type trap-on-condition: rs=29, rt=8 (same shape as mult/div)
example : decode (mkRT 29#32 8#32 0#32 0#32 0x34#32) = some (.teq 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x36#32) = some (.tne 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x32#32) = some (.tlt 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x30#32) = some (.tge 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x33#32) = some (.tltu 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x31#32) = some (.tgeu 29#32 8#32) := by decide

-- I-type arith/logic: rs=29, rt=8, imm=0x1234
example : decode (mkIT 0x08#32 29#32 8#32 0x1234#32) = some (.addi 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x09#32 29#32 8#32 0x1234#32) = some (.addiu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0a#32 29#32 8#32 0x1234#32) = some (.slti 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0b#32 29#32 8#32 0x1234#32) = some (.sltiu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0c#32 29#32 8#32 0x1234#32) = some (.andi 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0d#32 29#32 8#32 0x1234#32) = some (.ori 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0e#32 29#32 8#32 0x1234#32) = some (.xori 29#32 8#32 0x1234#32) := by decide

-- lui: rt=8, imm=0x1234 (rs fixed 0)
example : decode (mkIT 0x0f#32 0#32 8#32 0x1234#32) = some (.lui 8#32 0x1234#32) := by decide

-- load/store: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset)
example : decode (mkIT 0x23#32 29#32 8#32 0x1234#32) = some (.lw 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x2b#32 29#32 8#32 0x1234#32) = some (.sw 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x20#32 29#32 8#32 0x1234#32) = some (.lb 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x24#32 29#32 8#32 0x1234#32) = some (.lbu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x21#32 29#32 8#32 0x1234#32) = some (.lh 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x25#32 29#32 8#32 0x1234#32) = some (.lhu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x29#32 29#32 8#32 0x1234#32) = some (.sh 29#32 8#32 0x1234#32) := by decide

-- ll/sc: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset) -- identical
-- field layout to lw/sw
example : decode (mkIT 0x30#32 29#32 8#32 0x1234#32) = some (.ll 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x38#32 29#32 8#32 0x1234#32) = some (.sc 29#32 8#32 0x1234#32) := by decide

-- branch reg/reg: rs=29, rt=8, imm=0x1234
example : decode (mkIT 0x04#32 29#32 8#32 0x1234#32) = some (.beq 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x05#32 29#32 8#32 0x1234#32) = some (.bne 29#32 8#32 0x1234#32) := by decide

-- branch reg-only: rs=29, imm=0x1234 (rt fixed 0)
example : decode (mkIT 0x06#32 29#32 0#32 0x1234#32) = some (.blez 29#32 0x1234#32) := by decide
example : decode (mkIT 0x07#32 29#32 0#32 0x1234#32) = some (.bgtz 29#32 0x1234#32) := by decide

-- REGIMM zero-comparison branches: opcode 0x01, rs=29, imm=0x1234, rt field
-- selects bltz/bgez/bltzal/bgezal
example : decode (mkIT 0x01#32 29#32 0x00#32 0x1234#32) = some (.bltz 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x01#32 0x1234#32) = some (.bgez 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x10#32 0x1234#32) = some (.bltzal 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x11#32 0x1234#32) = some (.bgezal 29#32 0x1234#32) := by decide
-- a REGIMM word with an unrecognized rt field (not 0x00/0x01/0x10/0x11,
-- e.g. the real MIPS32 `tgei`/`tlti`/etc. trap-immediate family, out of
-- v1+ scope) decodes to none
#guard decode (mkIT 0x01#32 29#32 0x08#32 0x1234#32) = none

-- J-type: target = 0x3ffffff (all 26 bits)
example : decode ((0x02#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.j 0x3ffffff#32) := by decide
example : decode ((0x03#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.jal 0x3ffffff#32) := by decide

-- Coprocessor 1 (FPU): mtc1/mfc1 (fmt=MT/MF, rt=8, fs=3). Unlike plain
-- R-type, COP1 words need opcode 0x11 OR'd in explicitly over `mkRT`'s
-- (always-0) opcode field.
example : decode ((0x11#32 <<< 26) ||| mkRT 0x00#32 8#32 3#32 0#32 0#32) = some (.mfc1 8#32 3#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x04#32 8#32 3#32 0#32 0#32) = some (.mtc1 8#32 3#32) := by decide
-- lwc1/swc1: rs=29 (base), ft=5, imm=0x1234 (identical layout to lw/sw)
example : decode (mkIT 0x31#32 29#32 5#32 0x1234#32) = some (.lwc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (mkIT 0x39#32 29#32 5#32 0x1234#32) = some (.swc1 29#32 5#32 0x1234#32) := by
  decide
-- add.s/sub.s/mul.s/div.s: fmt=S, ft=6, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x00#32) = some (.addS 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x01#32) = some (.subS 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x02#32) = some (.mulS 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 8#32 0x03#32) = some (.divS 8#32 7#32 6#32) := by
  decide
-- mov.s/cvt.w.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x06#32) = some (.movS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x24#32) = some (.cvtWS 8#32 7#32) := by
  decide
-- cvt.s.w: fmt=W, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 7#32 8#32 0x20#32) = some (.cvtSW 8#32 7#32) := by
  decide
-- c.eq.s/c.lt.s/c.le.s: fmt=S, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x32#32) = some (.cEqS 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x3c#32) = some (.cLtS 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x3e#32) = some (.cLeS 7#32 6#32) := by decide
-- c.eq.s with a nonzero cc field (unsupported, only cc=0 modeled) → none
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 1#32 0x32#32) = none := by decide
-- bc1t/bc1f: fmt=BC1, tf=1/0, offset=0x1234
example : decode (mkIT 0x11#32 0x08#32 1#32 0x1234#32) = some (.bc1t 0x1234#32) := by decide
example : decode (mkIT 0x11#32 0x08#32 0#32 0x1234#32) = some (.bc1f 0x1234#32) := by decide
-- a BC1 word with a nonzero cc/nd (rt-field > 1, unsupported) → none
example : decode (mkIT 0x11#32 0x08#32 2#32 0x1234#32) = none := by decide

-- `encode ∘ decode` round-trips, spanning R / I / J / branch / syscall
example : encode (.add 29#32 8#32 3#32) = mkRT 29#32 8#32 3#32 0#32 0x20#32 := by decide
example : encode (.lw 29#32 8#32 0x1234#32) = mkIT 0x23#32 29#32 8#32 0x1234#32 := by decide
example : encode (.beq 29#32 8#32 0x1234#32) = mkIT 0x04#32 29#32 8#32 0x1234#32 := by decide
example : encode (.j 0x3ffffff#32) = (0x02#32 <<< 26) ||| mkJT 0x3ffffff#32 := by decide
example : encode .syscall = mkRT 0#32 0#32 0#32 0#32 0x0c#32 := by decide
example : encode (.sll 3#32 8#32 5#32) = mkRT 0#32 8#32 3#32 5#32 0x00#32 := by decide
example : encode (.movn 29#32 8#32 3#32) = mkRT 29#32 8#32 3#32 0#32 0x0b#32 := by decide
example : encode (.clo 29#32 3#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 3#32 3#32 0#32 0x21#32 := by decide
example : encode (.seb 3#32 8#32) = (0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x10#32 0x20#32 := by decide
example : encode (.sllv 3#32 8#32 29#32) = mkRT 29#32 8#32 3#32 0#32 0x04#32 := by decide
example : encode (.mul 29#32 8#32 3#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32 := by decide
example : encode (.jr 29#32) = mkRT 29#32 0#32 0#32 0#32 0x08#32 := by decide
example : encode (.jalr 29#32 3#32) = mkRT 29#32 0#32 3#32 0#32 0x09#32 := by decide
-- full round trip for every new instruction (decode ∘ encode = id on the field values we store)
example : decode (encode (.movn 29#32 8#32 3#32)) = some (.movn 29#32 8#32 3#32) := by decide
example : decode (encode (.movz 29#32 8#32 3#32)) = some (.movz 29#32 8#32 3#32) := by decide
example : decode (encode (.clo 29#32 3#32)) = some (.clo 29#32 3#32) := by decide
example : decode (encode (.clz 29#32 3#32)) = some (.clz 29#32 3#32) := by decide
example : decode (encode (.seb 3#32 8#32)) = some (.seb 3#32 8#32) := by decide
example : decode (encode (.seh 3#32 8#32)) = some (.seh 3#32 8#32) := by decide
example : decode (encode (.sllv 3#32 8#32 29#32)) = some (.sllv 3#32 8#32 29#32) := by decide
example : decode (encode (.srlv 3#32 8#32 29#32)) = some (.srlv 3#32 8#32 29#32) := by decide
example : decode (encode (.srav 3#32 8#32 29#32)) = some (.srav 3#32 8#32 29#32) := by decide
example : decode (encode (.mul 29#32 8#32 3#32)) = some (.mul 29#32 8#32 3#32) := by decide
example : decode (encode (.jr 29#32)) = some (.jr 29#32) := by decide
example : decode (encode (.jalr 29#32 3#32)) = some (.jalr 29#32 3#32) := by decide
example : encode .break = mkRT 0#32 0#32 0#32 0#32 0x0d#32 := by decide
example : encode (.teq 29#32 8#32) = mkRT 29#32 8#32 0#32 0#32 0x34#32 := by decide

-- `decode (encode ...)` round-trips for every new trap/break instruction
example : decode (encode (.teq 29#32 8#32)) = some (.teq 29#32 8#32) := by decide
example : decode (encode (.tne 29#32 8#32)) = some (.tne 29#32 8#32) := by decide
example : decode (encode (.tlt 29#32 8#32)) = some (.tlt 29#32 8#32) := by decide
example : decode (encode (.tge 29#32 8#32)) = some (.tge 29#32 8#32) := by decide
example : decode (encode (.tltu 29#32 8#32)) = some (.tltu 29#32 8#32) := by decide
example : decode (encode (.tgeu 29#32 8#32)) = some (.tgeu 29#32 8#32) := by decide
example : decode (encode .break) = some .break := by decide

-- Coprocessor 1 (FPU): full `decode (encode i) = some i` round-trips
example : decode (encode (.mfc1 8#32 3#32)) = some (.mfc1 8#32 3#32) := by decide
example : decode (encode (.mtc1 8#32 3#32)) = some (.mtc1 8#32 3#32) := by decide
example : decode (encode (.lwc1 29#32 5#32 0x1234#32)) = some (.lwc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (encode (.swc1 29#32 5#32 0x1234#32)) = some (.swc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (encode (.addS 8#32 7#32 6#32)) = some (.addS 8#32 7#32 6#32) := by decide
example : decode (encode (.subS 8#32 7#32 6#32)) = some (.subS 8#32 7#32 6#32) := by decide
example : decode (encode (.mulS 8#32 7#32 6#32)) = some (.mulS 8#32 7#32 6#32) := by decide
example : decode (encode (.divS 8#32 7#32 6#32)) = some (.divS 8#32 7#32 6#32) := by decide
example : decode (encode (.movS 8#32 7#32)) = some (.movS 8#32 7#32) := by decide
example : decode (encode (.cvtSW 8#32 7#32)) = some (.cvtSW 8#32 7#32) := by decide
example : decode (encode (.cvtWS 8#32 7#32)) = some (.cvtWS 8#32 7#32) := by decide
example : decode (encode (.cEqS 7#32 6#32)) = some (.cEqS 7#32 6#32) := by decide
example : decode (encode (.cLtS 7#32 6#32)) = some (.cLtS 7#32 6#32) := by decide
example : decode (encode (.cLeS 7#32 6#32)) = some (.cLeS 7#32 6#32) := by decide
example : decode (encode (.bc1t 0x1234#32)) = some (.bc1t 0x1234#32) := by decide
example : decode (encode (.bc1f 0x1234#32)) = some (.bc1f 0x1234#32) := by decide

-- REGIMM zero-comparison branches: full decode(encode i) = some i round-trips
example : decode (encode (.bltz 29#32 0x1234#32)) = some (.bltz 29#32 0x1234#32) := by decide
example : decode (encode (.bgez 29#32 0x1234#32)) = some (.bgez 29#32 0x1234#32) := by decide
example : decode (encode (.bltzal 29#32 0x1234#32)) = some (.bltzal 29#32 0x1234#32) := by decide
example : decode (encode (.bgezal 29#32 0x1234#32)) = some (.bgezal 29#32 0x1234#32) := by decide
-- ll/sc: encode matches the hand-computed opcode, and decode (encode i) = some i
example : encode (.ll 29#32 8#32 0x1234#32) = mkIT 0x30#32 29#32 8#32 0x1234#32 := by decide
example : encode (.sc 29#32 8#32 0x1234#32) = mkIT 0x38#32 29#32 8#32 0x1234#32 := by decide
example : decode (encode (.ll 29#32 8#32 0x1234#32)) = some (.ll 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.sc 29#32 8#32 0x1234#32)) = some (.sc 29#32 8#32 0x1234#32) := by decide

-- unknown opcodes → none
#guard decode (mkIT 0x3a#32 0#32 0#32 0#32) = none  -- opcode 0x3a, unassigned/not in v1+ scope
-- opcode 0x11 (COP1) is implemented for the fmt/funct combinations below;
-- an unrecognized fmt (not MF/MT/BC1/S/W) still decodes to `none`.
#guard decode (mkIT 0x11#32 0x1f#32 0#32 0#32) = none
#guard decode (mkIT 0x16#32 0#32 0#32 0#32) = none
#guard decode (mkIT 0x17#32 0#32 0#32 0#32) = none
#guard decode (mkIT 0x1c#32 0#32 0#32 0#32) = none
#guard decode (mkIT 0x1d#32 0#32 0#32 0#32) = none

-- unknown functs under opcode 0 → none
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x01#32) = none
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x3f#32) = none

-- a few key decodes
#guard decode (mkRT 29#32 8#32 3#32 0#32 0x20#32) = some (.add 29#32 8#32 3#32)
#guard decode (mkIT 0x23#32 29#32 8#32 0x1234#32) = some (.lw 29#32 8#32 0x1234#32)
#guard decode ((0x02#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.j 0x3ffffff#32)
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x0c#32) = some .syscall
#guard decode (mkRT 29#32 8#32 0#32 0#32 0x34#32) = some (.teq 29#32 8#32)
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x0d#32) = some .break

-- funct 0x35 sits between teq (0x34) and tne (0x36) and is reserved/unused
-- in the real MIPS32 trap family; no mnemonic maps to it.
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x35#32) = none
#guard decode (encode (.addS 8#32 7#32 6#32)) = some (.addS 8#32 7#32 6#32)
