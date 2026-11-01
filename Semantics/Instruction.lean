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
- R-type move, write direction (`rs`): `mthi mtlo` — `rt`/`rd`/`shamt`
  unused; the write-direction counterparts to `mfhi`/`mflo` above (MIPS32
  addition; see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5), needed for OS
  context switching and setjmp/longjmp to save/restore `hi`/`lo`.
- R-type multiply-accumulate (`rs rt`), SPECIAL2 (opcode 0x1c): `madd
  maddu msub msubu` — same `rs rt` shape as `mult`/`multu` (`rd`/`shamt`
  unused), accumulating into (or subtracting from) the *existing* `hi`/`lo`
  pair rather than overwriting it (MIPS32 addition; see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5).
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
- No fields: `sync` — real MIPS32 memory-ordering barrier (opcode 0, funct
  0x0f; `docs/spec/MIPS-COVERAGE-GAPS.md` §3.7), completing the atomics
  story alongside `ll`/`sc` above. The real encoding also carries an
  optional 5-bit `stype` hint field (bits 10..6) selecting which kind of
  ordering to enforce, but since this single-hart, non-reordering simulator
  has no concurrency or out-of-order execution for `stype` to distinguish
  between, it is omitted from this constructor entirely (decode ignores
  whatever value that field holds; encode always emits 0) — a documented
  simplification, not an oversight (see `docs/spec/INSTRUCTION-REF.md`).
- I-type synchronize-caches hint (`rs imm`), same field shape as `blez`:
  `synci` — real MIPS32 instruction-cache-flush hint for self-modifying
  code / JIT compilers (REGIMM opcode 0x01, `rt` field fixed `0x1f`;
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.7, MIPS32r2). Computes the same
  `$rs + sext16(offset)` address as `lw`/`sw`, but since this simulator has
  no instruction-cache model at all, the address is never used for
  anything (see `Step.lean`/`docs/spec/INSTRUCTION-REF.md`).
- I-type unaligned load/store (`rs rt imm`), same field shape as `lw`/`sw`:
  `lwl lwr swl swr` — real MIPS32 classic (pre-r6) unaligned memory-access
  pair (opcodes 0x22/0x26/0x2a/0x2e); not part of the original v1
  instruction set (see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.6 and
  `docs/spec/INSTRUCTION-REF.md`'s dedicated section). `rs` is the base
  register, `rt` is the dest/src register (also read, since these partially
  preserve `$rt`'s prior value), `imm` is the raw offset field, exactly like
  `lw`/`sw`; unlike `lw`/`sw`, the effective address has no alignment
  requirement at all.
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
- I-type trap-immediate (`rs imm`), REGIMM (opcode 0x01; `rt` field unused by
  the ALU, since it instead selects which trap this is, same multiplexing
  convention as `bltz`/`bgez`/`bltzal`/`bgezal` above): `teqi tnei tgei
  tgeiu tlti tltiu` — real MIPS32 immediate-operand trap family (see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.8), the sign-extended-16-bit-immediate
  counterpart of the `teq tne tlt tge tltu tgeu` register-register family
  above; same coprocessor-0 trap/exception model (`takeException` in
  `Semantics/Step.lean`). `tgeiu`/`tltiu` follow the same "sign-extend the
  16-bit immediate to 32 bits, then compare the result as unsigned"
  convention already used by `sltiu`.
- Coprocessor-0 (CP0) register move and execution-control instructions —
  opcode `0x10` (COP0); real MIPS32 encoding, scoped to exactly the three
  CP0 registers this project already models (`cp0Status`/`cp0Cause`/
  `cp0Epc`, register numbers 12/13/14) — no TLB/interrupt-mask registers are
  added (`docs/spec/MIPS-COVERAGE-GAPS.md` §3.10A):
  - `mfc0`/`mtc0` (`rt rd`): CP0-register ↔ GPR move, `rs`-position field
    selects `MF`(`0x00`)/`MT`(`0x04`); `rd` is the CP0 register number
    (only 12/13/14 are meaningful in this model — `Step.lean` documents the
    out-of-scope-`rd` behavior).
  - `eret`/`wait` (no fields): `rs`-position field `0x10` (`CO`
    sub-format), distinguished by `funct` (`0x18`/`0x20`); see
    `Step.lean`'s execution semantics for `eret`'s no-delay-slot
    architectural exception and `wait`'s no-op simplification.
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
  - `sqrtS absS negS` (`fd fs`): single-precision square root / absolute
    value / negation (v1.x addition, MIPS-COVERAGE-GAPS.md §3.9B). `absS`/
    `negS` are raw sign-bit operations in `Step.lean` (no `Float32`
    arithmetic involved), not IEEE-754-rounded computations.
  - `roundWS truncWS ceilWS floorWS` (`fd fs`): directed-rounding float→int32
    conversions (v1.x addition, MIPS-COVERAGE-GAPS.md §3.9B). `truncWS` is
    numerically identical to the pre-existing `cvtWS` under this model (both
    truncate toward zero); see `cvtWS`'s and `truncWS`'s docstrings.
  - `cFS cUnS cUeqS cOltS cUltS cOleS cUleS` (`fs ft`): the 7 additional
    `C.cond.S` predicates from this v1.x addition (MIPS-COVERAGE-GAPS.md
    §3.9B), completing the quiet (non-signaling) half of the 16-predicate
    family alongside the pre-existing `cEqS`/`cLtS`/`cLeS`. `cOltS`/`cOleS`
    are numerically identical to `cLtS`/`cLeS` under this model (both only
    differ from them in real-hardware NaN-exception behavior, which isn't
    modeled); see their docstrings.
  - `cfc1`/`ctc1` (`rt fs`): GPR↔FPU-control-register move (v1.x addition,
    MIPS-COVERAGE-GAPS.md §3.9C). No FCSR/FIR semantics are modeled; see
    `cfc1`'s docstring for the chosen scratch-storage model.
  Double-precision (`.d`) — opcode `0x11` COP1, `fmt` = `D` = `0x11` (not to
  be confused with the single-precision `fmt` = `S` = `0x10`) — v2 addition,
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.9A. A double value in `$fN` occupies
  a **pair** of adjacent 32-bit FPRs under the classic MIPS32 FR=0
  convention this project's `fpRegs : Array W32` already follows: `$fN`
  holds the low 32 bits, `$f(N+1)` holds the high 32 bits (real MIPS32
  requires `N` even for double operands; this model does not check/enforce
  that, it just follows the convention when composing/decomposing — see
  `Step.lean`'s `doubleOfRegPair`/`regPairOfDouble`). `fd`/`fs`/`ft` below
  name the *low* register of each pair; the high register is implicitly
  `+1`.
  - `ldc1`/`sdc1` (`rs ft imm`): load/store a full 64-bit doubleword between
    memory and an FPR pair, identical addressing to `lwc1`/`swc1` (opcodes
    `0x35`/`0x3d`). Implemented as two `readMemWord`/`writeMemWord` calls (at
    `addr` and `addr + 4`), reusing `lw`/`sw`'s already-correct alignment and
    big-endian byte-order logic rather than adding dedicated 64-bit memory
    helpers — see `Step.lean`'s cases for the resulting (documented)
    4-byte-alignment-per-half simplification vs. real MIPS32's 8-byte
    doubleword alignment.
  - `addD subD mulD divD` (`fd fs ft`): double-precision IEEE-754
    arithmetic, same shape/semantics as `addS subS mulS divS` but on
    register-pair-composed 64-bit `Float` values (`fmt` = `D`, `funct` =
    `0x00`/`0x01`/`0x02`/`0x03`).
  - `movD` (`fd fs`): FP register-pair raw-bit copy (both 32-bit halves),
    no `Float` arithmetic (`fmt` = `D`, `funct` = `0x06`).
  - `cvtDS`/`cvtSD` (`fd fs`): single↔double numeric promotion/demotion
    (`cvtDS`: `fmt` = `S` = `0x10` since the *source* is single, `funct` =
    `0x21`; `cvtSD`: `fmt` = `D`, `funct` = `0x20`).
  - `cvtDW`/`cvtWD` (`fd fs`): int↔double numeric conversion, the
    double-precision counterpart of `cvtSW`/`cvtWS` (`cvtDW`: `fmt` = `W` =
    `0x14`, `funct` = `0x21`; `cvtWD`: `fmt` = `D`, `funct` = `0x24`).
  - `cEqD cLtD cLeD cFD cUnD cUeqD cOltD cUltD cOleD cUleD` (`fs ft`): the
    double-precision counterparts of the same 10 quiet `C.cond.S`
    predicates this project already implements for single precision (`fmt`
    = `D`, same `funct = 0x30 | cond` numbering as the `.S` family —
    `cEqD`=`0x32`, `cLtD`=`0x3c`, `cLeD`=`0x3e`, `cFD`=`0x30`, `cUnD`=`0x31`,
    `cUeqD`=`0x33`, `cOltD`=`0x34`, `cUltD`=`0x35`, `cOleD`=`0x36`,
    `cUleD`=`0x37`); the remaining 6 "signaling" predicates are out of scope
    here for the same reason they are for `.S` (see below).
  - `absD negD` (`fd fs`): raw sign-bit operations on the **high** 32-bit
    half only (`fmt` = `D`, `funct` = `0x05`/`0x07`) — a double's sign bit is
    bit 63 of the 64-bit value, which lives in the high register's bit 31
    under the register-pair convention; the low register is copied
    unchanged. No `Float` arithmetic involved, same rationale as `absS`/
    `negS`.
  - `sqrtD` (`fd fs`): double-precision IEEE-754 square root (`fmt` = `D`,
    `funct` = `0x04`), via Lean core's `Float.sqrt`.
  The remaining 6 "signaling" `C.cond.S`/`C.cond.D` predicates
  (`c.sf`/`c.ngle`/`c.seq`/`c.ngl`/`c.nge`/`c.ngt`, cond numbers
  8/9/10/11/13/15 — the signaling counterparts of `c.un`/`c.eq`/`c.ueq`/
  `c.ult`/`c.ule`; this model has no FP-exception mechanism, so a signaling
  predicate would compute an identical `fpCondFlag` result to its quiet
  counterpart, the same relationship already documented between `cLtS`/
  `cOltS` and `cLeS`/`cOleS` above) remain out of scope, along with
  multi-cc compares and `bc1tl`/`bc1fl`; see `docs/spec/INSTRUCTION-REF.md`
  for the documented follow-up.
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
  -- R-type rotate (MIPS32r2; docs/spec/MIPS-COVERAGE-GAPS.md §3.4). Real
  -- MIPS32r2 overloads `srl`'s opcode-0/funct-0x02 encoding: the `rs` field
  -- (normally unused/fixed 0 for the plain shift-by-constant format) is set
  -- to 0x01 to select rotate instead of shift. Likewise `srlv`'s
  -- opcode-0/funct-0x06 encoding is overloaded via the (normally
  -- unused/fixed 0) `shamt` field set to 0x01. These are new decode/encode
  -- branches alongside the existing `srl`/`srlv` ones, not replacements.
  /-- `$rd = $rt` rotated right by the constant `sa` (0-31) bits -- bits
  shifted off the bottom wrap around to the top, unlike `srl`'s zero-fill
  (opcode 0, funct 0x02, `rs` field = 0x01). MIPS32r2. -/
  | rotr (rd rt sa : W32)
  /-- `$rd = $rt` rotated right by `$rs & 0x1f` bits, rotate amount from a
  register's low 5 bits (opcode 0, funct 0x06, `shamt` field = 0x01).
  MIPS32r2. -/
  | rotrv (rd rt rs : W32)
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
  -- R-type move, write direction (rt, rd/shamt unused): the write-direction
  -- counterparts to `mfhi`/`mflo` above (opcode 0, funct 0x11/0x13 — the
  -- next funct values immediately after `mfhi`'s 0x10/`mflo`'s 0x12, the
  -- same adjacency pattern as `syscall` 0x0c/`break` 0x0d). Real MIPS32
  -- (MD00086 Rev 2.50 §3.2, Table 3-7); needed for OS context switching and
  -- setjmp/longjmp to save/restore `hi`/`lo` (see
  -- `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5).
  /-- `hi = $rs` (opcode 0, funct 0x11). MIPS32. -/
  | mthi (rs : W32)
  /-- `lo = $rs` (opcode 0, funct 0x13). MIPS32. -/
  | mtlo (rs : W32)
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
  -- R-type multiply-accumulate, SPECIAL2 (MIPS32). Same `rs rt` field shape
  -- as `mult`/`multu` (`rd`/`shamt` unused) -- these accumulate into the
  -- *existing* `hi`/`lo` 64-bit pair instead of overwriting it, the core
  -- loop instruction in DSP filters, vector dot-products, and numerical
  -- libraries (see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5). Ground truth:
  -- MD00086 Rev 2.50 §3.2, Table 3-1.
  /-- `{hi,lo} += $rs * $rt`, signed 64-bit, wrapping on overflow like
  `mult` (SPECIAL2 opcode 0x1c, funct 0x00). MIPS32. -/
  | madd  (rs rt : W32)
  /-- `{hi,lo} += $rs * $rt`, unsigned 64-bit, wrapping on overflow (SPECIAL2
  opcode 0x1c, funct 0x01). MIPS32. -/
  | maddu (rs rt : W32)
  /-- `{hi,lo} -= $rs * $rt`, signed 64-bit, wrapping on overflow (SPECIAL2
  opcode 0x1c, funct 0x04). MIPS32. -/
  | msub  (rs rt : W32)
  /-- `{hi,lo} -= $rs * $rt`, unsigned 64-bit, wrapping on overflow (SPECIAL2
  opcode 0x1c, funct 0x05). MIPS32. -/
  | msubu (rs rt : W32)
  -- R-type SPECIAL3 BSHFL sign-extend (MIPS32r2). `rs` is unused/fixed 0;
  -- `funct` is 0x20 for the whole BSHFL sub-op family, and the shamt-position
  -- 5-bit sub-field (not a real shift amount here) selects which one.
  /-- `$rd = sign-extend($rt[7:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x10). MIPS32r2. -/
  | seb (rd rt : W32)
  /-- `$rd = sign-extend($rt[15:0])` to 32 bits (SPECIAL3 opcode 0x1f,
  funct 0x20, sub-field 0x18). MIPS32r2. -/
  | seh (rd rt : W32)
  /-- "Word Swap Bytes Within Halfwords": swaps the byte order *within* each
  16-bit half of `$rt` independently (byte 0 <-> 1, byte 2 <-> 3), leaving
  the two halfwords in their original word positions -- **not** a full
  32-bit byte-reverse (that needs `wsbh` followed by `rotr` by 16)
  (SPECIAL3 opcode 0x1f, funct 0x20, sub-field 0x02 -- same BSHFL funct
  family as `seb`/`seh`, distinguished by the sub-field like they are).
  MIPS32r2. -/
  | wsbh (rd rt : W32)
  -- R-type SPECIAL3 bitfield extract/insert (MIPS32r2;
  -- docs/spec/MIPS-COVERAGE-GAPS.md section 3.4). Both `pos` and `size` are
  -- small compile-time constants (0-31) encoded directly in the
  -- instruction word, not register values. Real constraint `pos + size <=
  -- 32` is architecturally UNPREDICTABLE if violated; this model makes no
  -- special case for it (SPEC-NOTES precedent: just compute what the
  -- bit masking implies). The raw encoding packs `pos` into the `shamt`
  -- field (bits 10..6) for both instructions, but the `rd`-position field
  -- (bits 15..11) differs: for `ext` it holds `size - 1` ("msbd"); for
  -- `ins` it holds `pos + size - 1` ("msb") -- these are genuinely
  -- different fields in the real MIPS32 ISA (MD00086 section 3.2), not a
  -- typo. `decode`/`encode` below do the +-1 arithmetic so `Step.lean`
  -- only ever sees the semantic `pos`/`size` pair.
  /-- `$rt = zero-extend($rs[pos+size-1 .. pos])`, extracting a `size`-bit
  field starting at bit `pos` (SPECIAL3 opcode 0x1f, funct 0x00). MIPS32r2. -/
  | ext (rt rs pos size : W32)
  /-- Inserts the low `size` bits of `$rs` into `$rt` starting at bit `pos`;
  bits of `$rt` outside `[pos+size-1 .. pos]` are left unchanged (SPECIAL3
  opcode 0x1f, funct 0x04). MIPS32r2. -/
  | ins (rt rs pos size : W32)
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
  -- I-type unaligned load/store (classic MIPS32; removed in MIPS32r6). Same
  -- `rs rt imm` field shape as `lw`/`sw`; see `docs/spec/INSTRUCTION-REF.md`'s
  -- dedicated section for the exact big-endian byte-merge semantics.
  /-- Load Word Left (opcode 0x22; MD00086 Rev 2.50 §3.2, Table 3-4, p. 25,
  entry 174). `addr = $rs + sext16(offset)` (no alignment check). Loads the
  bytes from `addr` up to the next word boundary (inclusive of `addr`) into
  the most-significant bytes of `$rt`; `$rt`'s remaining (less-significant)
  bytes are left unchanged. -/
  | lwl (rs rt imm : W32)
  /-- Load Word Right (opcode 0x26; MD00086 Rev 2.50 §3.2, Table 3-4, p. 25,
  entry 177). Same `addr` as `lwl`. Loads the bytes from the start of the
  word containing `addr` up to and including `addr` into the
  least-significant bytes of `$rt`; `$rt`'s remaining (more-significant)
  bytes are left unchanged. Paired with `lwl` (opposite offsets) to load an
  arbitrary unaligned word. -/
  | lwr (rs rt imm : W32)
  /-- Store Word Left (opcode 0x2a; MD00086 Rev 2.50 §3.2, Table 3-4, p. 26,
  entry 282). Same `addr` as `lwl`. Stores `$rt`'s most-significant bytes
  into memory from `addr` up to the next word boundary (inclusive of
  `addr`). -/
  | swl (rs rt imm : W32)
  /-- Store Word Right (opcode 0x2e; MD00086 Rev 2.50 §3.2, Table 3-4, p. 26,
  entry 285). Same `addr` as `lwl`. Stores `$rt`'s least-significant bytes
  into memory from the start of the word containing `addr` up to and
  including `addr`. Paired with `swl` to store an arbitrary unaligned
  word. -/
  | swr (rs rt imm : W32)
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
  -- I-type REGIMM trap-immediate family (real MIPS32 ISA; opcode 0x01,
  -- same opcode as the zero-comparison branches above, selected by the
  -- same `rt`-field multiplexing). Not part of the original v1 instruction
  -- set, added on top as the sign-extended-16-bit-immediate counterpart of
  -- the `teq tne tlt tge tltu tgeu` register-register trap family below
  -- (see `docs/spec/MIPS-COVERAGE-GAPS.md` §3.8); funct/rt values are cited
  -- from the real MIPS32 ISA (MD00086 Rev 2.50 §3.2, Table 3-2), not MARS.
  /-- `if $rs == sext16(imm) then trap`, signed (opcode 0x01, `rt` field =
  0x0c `TEQI`). -/
  | teqi (rs imm : W32)
  /-- `if $rs != sext16(imm) then trap`, signed (opcode 0x01, `rt` field =
  0x0e `TNEI`). -/
  | tnei (rs imm : W32)
  /-- `if $rs >= sext16(imm) then trap`, signed (opcode 0x01, `rt` field =
  0x08 `TGEI`). -/
  | tgei (rs imm : W32)
  /-- `if $rs >=u sext16(imm) then trap`: the immediate is sign-extended to
  32 bits first, then the comparison is unsigned on the resulting bit
  patterns — same "sign-extend, then compare unsigned" convention as
  `sltiu` (opcode 0x01, `rt` field = 0x09 `TGEIU`). -/
  | tgeiu (rs imm : W32)
  /-- `if $rs < sext16(imm) then trap`, signed (opcode 0x01, `rt` field =
  0x0a `TLTI`). -/
  | tlti (rs imm : W32)
  /-- `if $rs <u sext16(imm) then trap`: same sign-extend-then-unsigned-compare
  convention as `tgeiu`/`sltiu` (opcode 0x01, `rt` field = 0x0b `TLTIU`). -/
  | tltiu (rs imm : W32)
  -- Instruction-cache synchronize hint (real MIPS32 ISA, MIPS32r2; see
  -- `docs/spec/MIPS-COVERAGE-GAPS.md` section 3.7). Shares REGIMM's opcode 0x01
  -- with the branch/trap-immediate families above, selected the same way
  -- (by the `rt` field, here fixed to `0x1f`), but its remaining operands
  -- (`rs`, `imm`) are an address computation like `lw`/`sw`/`blez`, not a
  -- branch target or trap comparand.
  /-- Hint to flush the instruction cache at `$rs + sext16(offset)`, for
  self-modifying code / JIT compilers (opcode 0x01 REGIMM, `rt` field =
  `0x1f` `SYNCI`). This simulator has no instruction-cache model, so
  `Step.lean` computes the address (exactly like `lw`/`sw`) but never uses
  it for anything -- a documented no-op, not a silently-dropped cache
  effect. -/
  | synci (rs imm : W32)
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
  -- sync (no fields; see module docstring -- the real `stype` hint field is
  -- out of scope, same "documented simplification, not an oversight"
  -- rationale as `break`'s omitted "code" field above).
  /-- Memory-ordering barrier (opcode 0, funct 0x0f -- the next funct value
  after `break`'s 0x0d, skipping the unassigned 0x0e). Real MIPS32: ensures
  all loads/stores issued before `sync` complete, as observed by other
  processors/coherent I/O, before any issued after it -- see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.7. -/
  | sync
  -- Coprocessor 0 (CP0) register move and execution-control instructions
  -- (v1.x addition; `docs/spec/MIPS-COVERAGE-GAPS.md` §3.10A). Real MIPS32
  -- encoding (opcode 0x10, COP0), scoped to exactly the three CP0
  -- registers this project already models (`cp0Status`/`cp0Cause`/
  -- `cp0Epc`, real MIPS32 register numbers 12/13/14); no TLB/interrupt-mask
  -- registers are added.
  /-- `$rt = ` the CP0 register named by `rd` (opcode 0x10 COP0, `rs`-field =
  `MF` = 0x00). Only `rd = 12/13/14` (`Status`/`Cause`/`EPC`) are meaningful
  in this model — see `Step.lean` for the documented out-of-scope-`rd`
  behavior. -/
  | mfc0 (rt rd : W32)
  /-- the CP0 register named by `rd := $rt` (opcode 0x10 COP0, `rs`-field =
  `MT` = 0x04). Same `rd` scoping (12/13/14 only) as `mfc0`. -/
  | mtc0 (rt rd : W32)
  /-- Exception return: `PC := cp0Epc`, `Status.EXL := 0` (opcode 0x10 COP0,
  `rs`-field = `CO` = 0x10, `funct` = 0x18). No operands. Real MIPS32:
  **not** a delay-slotted instruction — it takes effect immediately, an
  architectural exception to the general branch/jump delay-slot rule (see
  `Step.lean`'s execution semantics and `docs/spec/INSTRUCTION-REF.md`). -/
  | eret
  /-- Enter standby mode (opcode 0x10 COP0, `rs`-field = `CO` = 0x10,
  `funct` = 0x20). No operands. This simulator has no interrupt/timer model,
  so `Step.lean` treats this as a documented no-op that falls through to
  `pc + 4`, not a realistic idle/halt-until-interrupt. -/
  | wait
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
  /-- `{$ft,$ft+1} = MEM64[$rs + offset]`, raw bits, into an FPR pair per the
  module docstring's register-pair convention (opcode 0x35 `LDC1`). This
  model only checks each 32-bit half's own 4-byte alignment (via two
  `readMemWord` calls at `addr`/`addr+4`), not real MIPS32's 8-byte
  doubleword alignment requirement -- a documented simplification (see
  `Step.lean`). -/
  | ldc1 (rs ft imm : W32)
  /-- `MEM64[$rs + offset] = rawbits({$ft,$ft+1})`, inverse of `ldc1`
  (opcode 0x3d `SDC1`); same alignment simplification. -/
  | sdc1 (rs ft imm : W32)
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
  /-- `$fd = sqrt($fs)`, single-precision IEEE-754 square root (opcode 0x11
  COP1, `fmt` = `S`, `funct` = 0x04 `SQRT.S`; `ft`-position field unused).
  Computed via Lean core's `Float32.sqrt` (`@[extern "sqrtf"]`, backed by the
  C library's `sqrtf`, which is correctly-rounded IEEE-754 single-precision
  square root on every supported platform) — see `Step.lean`. -/
  | sqrtS (fd fs : W32)
  /-- `$fd = |$fs|`, i.e. `$fs` with its sign bit (bit 31) cleared (opcode
  0x11 COP1, `fmt` = `S`, `funct` = 0x05 `ABS.S`; `ft`-position field
  unused). Implemented in `Step.lean` as the raw bit operation
  `$fs &&& 0x7fffffff`, **not** `Float32` arithmetic — clearing the sign bit
  is exact for every bit pattern including `NaN`/`Inf`/`0`, so there is no
  rounding or NaN-propagation question to resolve here. -/
  | absS (fd fs : W32)
  /-- `$fd = -$fs`, i.e. `$fs` with its sign bit (bit 31) flipped (opcode
  0x11 COP1, `fmt` = `S`, `funct` = 0x07 `NEG.S`; `ft`-position field
  unused). Implemented in `Step.lean` as the raw bit operation
  `$fs ^^^ 0x80000000`, same rationale as `absS`. -/
  | negS (fd fs : W32)
  /-- `$fd = int32bits(round($fs))`, numeric conversion rounding to the
  nearest integer (opcode 0x11 COP1, `fmt` = `S`, `funct` = 0x0c `ROUND.W.S`;
  `ft`-position field unused). Real MIPS32 always rounds to nearest with
  ties-to-even for this instruction, regardless of the FCSR rounding mode;
  this v1.x addition instead uses Lean core's `Float32.round` (`roundf`),
  which rounds ties **away from zero**, not to even — a documented
  simplification (Lean core exposes no ties-to-even float-to-float rounding
  primitive), matching this track's existing `cvtWS`-rounding-mode
  simplification in spirit. Overflow/NaN clamp to `Int32`'s extremes/`0`,
  same as `cvtWS` (`Float32.toInt32`). -/
  | roundWS (fd fs : W32)
  /-- `$fd = int32bits(trunc($fs))`, numeric conversion truncating toward
  zero (opcode 0x11 COP1, `fmt` = `S`, `funct` = 0x0d `TRUNC.W.S`;
  `ft`-position field unused). Numerically **identical** to the pre-existing
  `cvtWS` under this model (both truncate toward zero via `Float32.toInt32`)
  — `trunc.w.s` and `cvt.w.s` are distinct real-MIPS32 encodings/mnemonics
  that happen to collapse to the same modeled behavior here, since `cvt.w.s`
  always truncates in this model too (no FCSR rounding-mode state exists to
  make them diverge); this overlap is intentional and documented, not an
  oversight. -/
  | truncWS (fd fs : W32)
  /-- `$fd = int32bits(ceil($fs))`, numeric conversion rounding toward
  +Infinity (opcode 0x11 COP1, `fmt` = `S`, `funct` = 0x0e `CEIL.W.S`;
  `ft`-position field unused). Uses Lean core's `Float32.ceil` (`ceilf`). -/
  | ceilWS (fd fs : W32)
  /-- `$fd = int32bits(floor($fs))`, numeric conversion rounding toward
  -Infinity (opcode 0x11 COP1, `fmt` = `S`, `funct` = 0x0f `FLOOR.W.S`;
  `ft`-position field unused). Uses Lean core's `Float32.floor` (`floorf`). -/
  | floorWS (fd fs : W32)
  /-- `fpCondFlag := false`, unconditionally (opcode 0x11 COP1, `fmt` = `S`,
  `funct` = 0x30 = `0x30 | cond`, `cond(F) = 0`; `cc` fixed 0). Real MIPS32's
  "always false" predicate, used by compilers as a placeholder/no-op
  compare. -/
  | cFS (fs ft : W32)
  /-- `fpCondFlag := isNaN($fs) ∨ isNaN($ft)` ("unordered") (opcode 0x11
  COP1, `fmt` = `S`, `funct` = 0x31, `cond(UN) = 1`; `cc` fixed 0). Built
  from `Float32.isNaN` explicitly in `Step.lean`, **not** derived from `<`/
  `<=` — Lean core's `Float32` `<`/`<=` already return `false` for any NaN
  operand (the IEEE-754-correct behavior), which would silently make a
  naive `!(a < b) && !(b < a)`-style "unordered" formula wrong, so this
  predicate reads `isNaN` directly instead. -/
  | cUnS (fs ft : W32)
  /-- `fpCondFlag := ($fs == $ft) ∨ unordered` (opcode 0x11 COP1, `fmt` = `S`,
  `funct` = 0x33, `cond(UEQ) = 3`; `cc` fixed 0). -/
  | cUeqS (fs ft : W32)
  /-- `fpCondFlag := ordered ∧ ($fs < $ft)` (opcode 0x11 COP1, `fmt` = `S`,
  `funct` = 0x34, `cond(OLT) = 4`; `cc` fixed 0). Numerically **identical**
  to `cLtS`'s modeled result: `Float32.lt` already returns `false` for any
  NaN operand, so it already computes exactly the ordered-less-than
  predicate. `cLtS` (`C.LT.S`, cond 12, the *signaling* variant) and `cOltS`
  (`C.OLT.S`, cond 4, the *quiet* variant) differ on real hardware only in
  whether a quiet-NaN operand raises an Invalid Operation exception —
  since this model has no FP-exception mechanism for either, both
  constructors compute the same `fpCondFlag` value. Two constructors are
  kept because they are genuinely distinct real-MIPS32 encodings/mnemonics,
  not because the model needs two implementations. -/
  | cOltS (fs ft : W32)
  /-- `fpCondFlag := ($fs < $ft) ∨ unordered` (opcode 0x11 COP1, `fmt` = `S`,
  `funct` = 0x35, `cond(ULT) = 5`; `cc` fixed 0). Built from `Float32.isNaN`
  explicitly, same rationale as `cUnS`. -/
  | cUltS (fs ft : W32)
  /-- `fpCondFlag := ordered ∧ ($fs <= $ft)` (opcode 0x11 COP1, `fmt` = `S`,
  `funct` = 0x36, `cond(OLE) = 6`; `cc` fixed 0). Same `cLeS`/`cOleS`
  signaling-vs-quiet relationship as `cLtS`/`cOltS` above (`cLeS` = cond 14
  `C.LE.S`, `cOleS` = cond 6 `C.OLE.S`). -/
  | cOleS (fs ft : W32)
  /-- `fpCondFlag := ($fs <= $ft) ∨ unordered` (opcode 0x11 COP1, `fmt` = `S`,
  `funct` = 0x37, `cond(ULE) = 7`; `cc` fixed 0). Built from `Float32.isNaN`
  explicitly, same rationale as `cUnS`. -/
  | cUleS (fs ft : W32)
  -- Double-precision (`.d`) arithmetic/move/convert/compare -- opcode 0x11
  -- COP1, `fmt` = `D` = 0x11 (see the module docstring's double-precision
  -- bullet for the register-pair convention). `fd`/`fs`/`ft` name the *low*
  -- register of each operand's pair; `Step.lean`'s `doubleOfRegPair`/
  -- `regPairOfDouble` do the pair composition/decomposition.
  /-- `{$fd,$fd+1} = {$fs,$fs+1} + {$ft,$ft+1}`, double-precision IEEE-754
  (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x00 `ADD.D`). -/
  | addD (fd fs ft : W32)
  /-- `{$fd,$fd+1} = {$fs,$fs+1} - {$ft,$ft+1}`, double-precision IEEE-754
  (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x01 `SUB.D`). -/
  | subD (fd fs ft : W32)
  /-- `{$fd,$fd+1} = {$fs,$fs+1} * {$ft,$ft+1}`, double-precision IEEE-754
  (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x02 `MUL.D`). -/
  | mulD (fd fs ft : W32)
  /-- `{$fd,$fd+1} = {$fs,$fs+1} / {$ft,$ft+1}`, double-precision IEEE-754
  (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x03 `DIV.D`); division by zero
  produces ±Infinity/NaN per IEEE-754, no trap, same as `divS`. -/
  | divD (fd fs ft : W32)
  /-- `{$fd,$fd+1} = {$fs,$fs+1}`, raw pair-to-pair bit copy, both 32-bit
  halves (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x06 `MOV.D`;
  `ft`-position field unused/fixed 0). -/
  | movD (fd fs : W32)
  /-- `{$fd,$fd+1} = float64(float32bits($fs))`, single-to-double promotion
  (opcode 0x11 COP1, `fmt` = `S` = 0x10 since the *source* is single,
  `funct` = 0x21 `CVT.D.S`; `ft`-position field unused). Exact: every
  `Float32` value is exactly representable as a `Float` (binary64 strictly
  extends binary32's range/precision). -/
  | cvtDS (fd fs : W32)
  /-- `$fd = float32(float64bits({$fs,$fs+1}))`, double-to-single demotion,
  rounding to the nearest `Float32` (opcode 0x11 COP1, `fmt` = `D`, `funct`
  = 0x20 `CVT.S.D`; `ft`-position field unused). May lose precision/
  overflow to ±Infinity, per IEEE-754 double-to-single conversion. -/
  | cvtSD (fd fs : W32)
  /-- `{$fd,$fd+1} = float64(int32bits($fs))`, numeric conversion of `$fs`'s
  bit pattern read as a 32-bit two's-complement int (opcode 0x11 COP1,
  `fmt` = `W` = 0x14, `funct` = 0x21 `CVT.D.W`; `ft`-position field unused).
  Exact for every `Int32` value (binary64 has 52 mantissa bits). -/
  | cvtDW (fd fs : W32)
  /-- `$fd = int32bits(truncate({$fs,$fs+1}))`, numeric conversion
  truncating toward zero (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x24
  `CVT.W.D`; `ft`-position field unused). Same truncating-vs-FCSR-rounding-
  mode simplification as `cvtWS`. -/
  | cvtWD (fd fs : W32)
  /-- `fpCondFlag := ({$fs,$fs+1} == {$ft,$ft+1})`, IEEE-754 double-precision
  compare (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x32 `C.EQ.D`; `cc`
  fixed 0). -/
  | cEqD (fs ft : W32)
  /-- `fpCondFlag := ({$fs,$fs+1} < {$ft,$ft+1})`, IEEE-754 double-precision
  compare (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x3c `C.LT.D`; `cc`
  fixed 0). -/
  | cLtD (fs ft : W32)
  /-- `fpCondFlag := ({$fs,$fs+1} <= {$ft,$ft+1})`, IEEE-754 double-precision
  compare (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x3e `C.LE.D`; `cc`
  fixed 0). -/
  | cLeD (fs ft : W32)
  /-- `fpCondFlag := false`, unconditionally (opcode 0x11 COP1, `fmt` = `D`,
  `funct` = 0x30, `cond(F) = 0`; `cc` fixed 0). Double-precision counterpart
  of `cFS`. -/
  | cFD (fs ft : W32)
  /-- `fpCondFlag := isNaN({$fs,$fs+1}) ∨ isNaN({$ft,$ft+1})` ("unordered")
  (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x31, `cond(UN) = 1`; `cc` fixed
  0). Double-precision counterpart of `cUnS`, same `Float.isNaN`-based
  rationale. -/
  | cUnD (fs ft : W32)
  /-- `fpCondFlag := ({$fs,$fs+1} == {$ft,$ft+1}) ∨ unordered` (opcode 0x11
  COP1, `fmt` = `D`, `funct` = 0x33, `cond(UEQ) = 3`; `cc` fixed 0). -/
  | cUeqD (fs ft : W32)
  /-- `fpCondFlag := ordered ∧ ({$fs,$fs+1} < {$ft,$ft+1})` (opcode 0x11
  COP1, `fmt` = `D`, `funct` = 0x34, `cond(OLT) = 4`; `cc` fixed 0).
  Numerically identical to `cLtD`'s modeled result, same `cLtS`/`cOltS`
  relationship. -/
  | cOltD (fs ft : W32)
  /-- `fpCondFlag := ({$fs,$fs+1} < {$ft,$ft+1}) ∨ unordered` (opcode 0x11
  COP1, `fmt` = `D`, `funct` = 0x35, `cond(ULT) = 5`; `cc` fixed 0). -/
  | cUltD (fs ft : W32)
  /-- `fpCondFlag := ordered ∧ ({$fs,$fs+1} <= {$ft,$ft+1})` (opcode 0x11
  COP1, `fmt` = `D`, `funct` = 0x36, `cond(OLE) = 6`; `cc` fixed 0). -/
  | cOleD (fs ft : W32)
  /-- `fpCondFlag := ({$fs,$fs+1} <= {$ft,$ft+1}) ∨ unordered` (opcode 0x11
  COP1, `fmt` = `D`, `funct` = 0x37, `cond(ULE) = 7`; `cc` fixed 0). -/
  | cUleD (fs ft : W32)
  /-- `$fd = sqrt({$fs,$fs+1})`, double-precision IEEE-754 square root
  (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x04 `SQRT.D`; `ft`-position
  field unused). Via Lean core's `Float.sqrt` (`@[extern "sqrt"]`, backed by
  the C library's `sqrt`). -/
  | sqrtD (fd fs : W32)
  /-- `{$fd,$fd+1} = |{$fs,$fs+1}|`, i.e. the pair with the sign bit (bit 31
  of the **high** register, `$fs+1`) cleared and the low register copied
  unchanged (opcode 0x11 COP1, `fmt` = `D`, `funct` = 0x05 `ABS.D`;
  `ft`-position field unused). A double's sign bit is bit 63 of the 64-bit
  value, which lives in the high register's bit 31 under the register-pair
  convention -- implemented in `Step.lean` as the raw bit operation
  `($fs+1) &&& 0x7fffffff` on the high half only, same rationale as
  `absS`. -/
  | absD (fd fs : W32)
  /-- `{$fd,$fd+1} = -{$fs,$fs+1}`, i.e. the pair with the high register's
  sign bit flipped and the low register copied unchanged (opcode 0x11 COP1,
  `fmt` = `D`, `funct` = 0x07 `NEG.D`; `ft`-position field unused).
  Implemented in `Step.lean` as `($fs+1) ^^^ 0x80000000` on the high half
  only, same rationale as `negS`. -/
  | negD (fd fs : W32)
  /-- `$rt = FpuControl[$fs]`, move from a coprocessor-1 control register to
  a GPR (opcode 0x11 COP1, `rs`-position field = `CF` = 0x02). Real MIPS32
  exposes named control registers (`FIR` = reg 0, `FCSR` = reg 31, ...) with
  rounding-mode/exception-flag semantics behind them; this project models no
  `FCSR`/`FIR` state at all, so — per this track's brief — `cfc1`/`ctc1`
  are given the simplest available semantics: they read/write the *same*
  `State.fpRegs` array the data instructions use (register 31 conventionally
  standing in for `FCSR`), as an ordinary addressable 32-bit scratch slot
  with no control-register behavior (rounding mode, exception sticky bits)
  actually modeled behind it. This is a deliberate simplification, not an
  oversight; see `Step.lean`. -/
  | cfc1 (rt fs : W32)
  /-- `FpuControl[$fs] = $rt`, move from a GPR to a coprocessor-1 control
  register (opcode 0x11 COP1, `rs`-position field = `CT` = 0x06). See
  `cfc1`'s docstring for the shared-`fpRegs`-scratch-slot model this uses. -/
  | ctc1 (rt fs : W32)
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
    -- `srl`/`rotr` share funct 0x02; the `rs` field (normally unused/fixed 0
    -- for `srl`) is overloaded to 0x01 to select `rotr` (MIPS32r2; see the
    -- `.rotr` docstring).
    | 0x02 => if rs.toNat == 0x01 then some (.rotr rd rt shamt) else some (.srl rd rt shamt)
    | 0x03 => some (.sra rd rt shamt)
    | 0x04 => some (.sllv rd rt rs)
    -- `srlv`/`rotrv` share funct 0x06; the `shamt` field (normally
    -- unused/fixed 0 for `srlv`) is overloaded to 0x01 to select `rotrv`.
    | 0x06 => if shamt.toNat == 0x01 then some (.rotrv rd rt rs) else some (.srlv rd rt rs)
    | 0x07 => some (.srav rd rt rs)
    | 0x18 => some (.mult rs rt)
    | 0x19 => some (.multu rs rt)
    | 0x1a => some (.div rs rt)
    | 0x1b => some (.divu rs rt)
    | 0x12 => some (.mflo rd)
    | 0x10 => some (.mfhi rd)
    | 0x11 => some (.mthi rs)
    | 0x13 => some (.mtlo rs)
    | 0x08 => some (.jr rs)
    | 0x09 => some (.jalr rs rd)
    | 0x0c => some .syscall
    | 0x0d => some .break
    -- sync: funct 0x0f. The real `stype` hint lives in the `shamt` field
    -- (bits 10..6); not modeled, so decode matches regardless of its value,
    -- the same "ignore an unmodeled sub-field" convention as the SPECIAL2
    -- bit-count family's rt/rd duplication above.
    | 0x0f => some .sync
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
    | 0x00 => some (.madd rs rt)
    | 0x01 => some (.maddu rs rt)
    | 0x04 => some (.msub rs rt)
    | 0x05 => some (.msubu rs rt)
    | _ => none
  | 0x1f =>  -- SPECIAL3: BSHFL sign-extend family, selected by the shamt sub-field
    match (functOf w).toNat with
    | 0x20 =>
      match shamt.toNat with
      | 0x10 => some (.seb rd rt)
      | 0x18 => some (.seh rd rt)
      | 0x02 => some (.wsbh rd rt)
      | _ => none
    -- `ext`/`ins` (MIPS32r2 bitfield extract/insert): `pos` is the raw
    -- `shamt` field for both; the raw `rd`-position field means something
    -- different for each (see the `.ext`/`.ins` docstrings), so the +-1
    -- arithmetic to recover the semantic `size` happens right here.
    | 0x00 => some (.ext rt rs shamt (rd + 1#32))
    | 0x04 => some (.ins rt rs shamt (rd - shamt + 1#32))
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
  | 0x22 => some (.lwl rs rt imm)
  | 0x26 => some (.lwr rs rt imm)
  | 0x2a => some (.swl rs rt imm)
  | 0x2e => some (.swr rs rt imm)
  | 0x29 => some (.sh rs rt imm)
  | 0x30 => some (.ll rs rt imm)
  | 0x38 => some (.sc rs rt imm)
  | 0x04 => some (.beq rs rt imm)
  | 0x05 => some (.bne rs rt imm)
  | 0x06 => some (.blez rs imm)
  | 0x07 => some (.bgtz rs imm)
  | 0x01 =>  -- REGIMM: rt field (not the opcode) selects
             -- bltz/bgez/bltzal/bgezal/tgei/tgeiu/tlti/tltiu/teqi/tnei/synci
    match rt.toNat with
    | 0x00 => some (.bltz rs imm)
    | 0x01 => some (.bgez rs imm)
    | 0x10 => some (.bltzal rs imm)
    | 0x11 => some (.bgezal rs imm)
    | 0x08 => some (.tgei rs imm)
    | 0x09 => some (.tgeiu rs imm)
    | 0x0a => some (.tlti rs imm)
    | 0x0b => some (.tltiu rs imm)
    | 0x0c => some (.teqi rs imm)
    | 0x0e => some (.tnei rs imm)
    | 0x1f => some (.synci rs imm)
    | _ => none
  | 0x02 => some (.j target)
  | 0x03 => some (.jal target)
  -- Coprocessor 0 (CP0): `rs`-position field is the format selector
  -- (MF/MT/CO), `rt` is the GPR, `rd` is the CP0 register number for
  -- mfc0/mtc0; eret/wait are the CO sub-format, selected by `funct`.
  | 0x10 =>
    match rs.toNat with
    | 0x00 => some (.mfc0 rt rd)  -- fmt = MF
    | 0x04 => some (.mtc0 rt rd)  -- fmt = MT
    | 0x10 =>  -- fmt = CO (coprocessor operation sub-format)
      match (functOf w).toNat with
      | 0x18 => some .eret
      | 0x20 => some .wait
      | _ => none
    | _ => none
  | 0x31 => some (.lwc1 rs rt imm)
  | 0x39 => some (.swc1 rs rt imm)
  | 0x35 => some (.ldc1 rs rt imm)
  | 0x3d => some (.sdc1 rs rt imm)
  -- Coprocessor 1 (FPU): `rs`-position field is `fmt`/sub-opcode, `rt` is
  -- `ft` (or the GPR for mtc1/mfc1), `rd` is `fs` (or `ft` for arithmetic
  -- format, see each case), `shamt` is `fd` for arithmetic format.
  | 0x11 =>
    match rs.toNat with
    | 0x00 => some (.mfc1 rt rd)  -- fmt = MF: rt = GPR, rd-position = fs
    | 0x04 => some (.mtc1 rt rd)  -- fmt = MT
    | 0x02 => some (.cfc1 rt rd)  -- fmt = CF: control-register read
    | 0x06 => some (.ctc1 rt rd)  -- fmt = CT: control-register write
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
      | 0x04 => some (.sqrtS shamt rd)
      | 0x05 => some (.absS shamt rd)
      | 0x07 => some (.negS shamt rd)
      | 0x0c => some (.roundWS shamt rd)
      | 0x0d => some (.truncWS shamt rd)
      | 0x0e => some (.ceilWS shamt rd)
      | 0x0f => some (.floorWS shamt rd)
      -- `fd`-position field holds `cc`(3)/0/0 for compares; only cc=0 modeled.
      | 0x32 => if shamt.toNat == 0 then some (.cEqS rd rt) else none
      | 0x3c => if shamt.toNat == 0 then some (.cLtS rd rt) else none
      | 0x3e => if shamt.toNat == 0 then some (.cLeS rd rt) else none
      | 0x30 => if shamt.toNat == 0 then some (.cFS rd rt) else none
      | 0x31 => if shamt.toNat == 0 then some (.cUnS rd rt) else none
      | 0x33 => if shamt.toNat == 0 then some (.cUeqS rd rt) else none
      | 0x34 => if shamt.toNat == 0 then some (.cOltS rd rt) else none
      | 0x35 => if shamt.toNat == 0 then some (.cUltS rd rt) else none
      | 0x36 => if shamt.toNat == 0 then some (.cOleS rd rt) else none
      | 0x37 => if shamt.toNat == 0 then some (.cUleS rd rt) else none
      -- `cvt.d.s`: source is single, so it's funct 0x21 in the *S* fmt block
      -- (not the D block below), same "fmt names the source format"
      -- convention as `cvtSW`/`cvtWS`.
      | 0x21 => some (.cvtDS shamt rd)
      | _ => none
    | 0x14 =>  -- fmt = W
      match (functOf w).toNat with
      | 0x20 => some (.cvtSW shamt rd)
      -- `cvt.d.w`: source is a word (int), funct 0x21, same field shape.
      | 0x21 => some (.cvtDW shamt rd)
      | _ => none
    -- fmt = D (0x11): double-precision arithmetic/compare/move/convert
    -- format, exact same field shape as fmt = S above (ft=rt, fs=rd,
    -- fd=shamt) -- see the module docstring's double-precision bullet.
    | 0x11 =>
      match (functOf w).toNat with
      | 0x00 => some (.addD shamt rd rt)
      | 0x01 => some (.subD shamt rd rt)
      | 0x02 => some (.mulD shamt rd rt)
      | 0x03 => some (.divD shamt rd rt)
      | 0x06 => some (.movD shamt rd)
      | 0x20 => some (.cvtSD shamt rd)
      | 0x24 => some (.cvtWD shamt rd)
      | 0x04 => some (.sqrtD shamt rd)
      | 0x05 => some (.absD shamt rd)
      | 0x07 => some (.negD shamt rd)
      | 0x32 => if shamt.toNat == 0 then some (.cEqD rd rt) else none
      | 0x3c => if shamt.toNat == 0 then some (.cLtD rd rt) else none
      | 0x3e => if shamt.toNat == 0 then some (.cLeD rd rt) else none
      | 0x30 => if shamt.toNat == 0 then some (.cFD rd rt) else none
      | 0x31 => if shamt.toNat == 0 then some (.cUnD rd rt) else none
      | 0x33 => if shamt.toNat == 0 then some (.cUeqD rd rt) else none
      | 0x34 => if shamt.toNat == 0 then some (.cOltD rd rt) else none
      | 0x35 => if shamt.toNat == 0 then some (.cUltD rd rt) else none
      | 0x36 => if shamt.toNat == 0 then some (.cOleD rd rt) else none
      | 0x37 => if shamt.toNat == 0 then some (.cUleD rd rt) else none
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
  -- Rotate (MIPS32r2): `rs`/`shamt` field overloading, per the `.rotr`/
  -- `.rotrv` docstrings.
  | .rotr  rd rt sa => mkRT 0x01#32 rt rd sa 0x02#32
  | .rotrv rd rt rs => mkRT rs rt rd 0x01#32 0x06#32
  | .mult  rs rt => mkRT rs rt 0#32 0#32 0x18#32
  | .multu rs rt => mkRT rs rt 0#32 0#32 0x19#32
  | .div   rs rt => mkRT rs rt 0#32 0#32 0x1a#32
  | .divu  rs rt => mkRT rs rt 0#32 0#32 0x1b#32
  | .mflo rd => mkRT 0#32 0#32 rd 0#32 0x12#32
  | .mfhi rd => mkRT 0#32 0#32 rd 0#32 0x10#32
  | .mthi rs => mkRT rs 0#32 0#32 0#32 0x11#32
  | .mtlo rs => mkRT rs 0#32 0#32 0#32 0x13#32
  | .jr   rs => mkRT rs 0#32 0#32 0#32 0x08#32
  | .jalr rs rd => mkRT rs 0#32 rd 0#32 0x09#32
  -- SPECIAL2: duplicate rd into the rt-position field per the real encoding.
  | .clo rs rd => (0x1c#32 <<< 26) ||| mkRT rs rd rd 0#32 0x21#32
  | .clz rs rd => (0x1c#32 <<< 26) ||| mkRT rs rd rd 0#32 0x20#32
  | .mul rs rt rd => (0x1c#32 <<< 26) ||| mkRT rs rt rd 0#32 0x02#32
  | .madd  rs rt => (0x1c#32 <<< 26) ||| mkRT rs rt 0#32 0#32 0x00#32
  | .maddu rs rt => (0x1c#32 <<< 26) ||| mkRT rs rt 0#32 0#32 0x01#32
  | .msub  rs rt => (0x1c#32 <<< 26) ||| mkRT rs rt 0#32 0#32 0x04#32
  | .msubu rs rt => (0x1c#32 <<< 26) ||| mkRT rs rt 0#32 0#32 0x05#32
  -- SPECIAL3 BSHFL: rs fixed 0, shamt-position field selects seb/seh/wsbh.
  | .seb rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x10#32 0x20#32
  | .seh rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x18#32 0x20#32
  | .wsbh rd rt => (0x1f#32 <<< 26) ||| mkRT 0#32 rt rd 0x02#32 0x20#32
  -- SPECIAL3 bitfield extract/insert: `pos` is the raw `shamt` field for
  -- both; the raw `rd`-position field is `size - 1` for `ext` ("msbd") but
  -- `pos + size - 1` for `ins` ("msb") -- see the `.ext`/`.ins` docstrings.
  | .ext rt rs pos size => (0x1f#32 <<< 26) ||| mkRT rs rt (size - 1#32) pos 0x00#32
  | .ins rt rs pos size => (0x1f#32 <<< 26) ||| mkRT rs rt (pos + size - 1#32) pos 0x04#32
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
  | .lwl rs rt imm => mkIT 0x22#32 rs rt imm
  | .lwr rs rt imm => mkIT 0x26#32 rs rt imm
  | .swl rs rt imm => mkIT 0x2a#32 rs rt imm
  | .swr rs rt imm => mkIT 0x2e#32 rs rt imm
  | .beq rs rt imm => mkIT 0x04#32 rs rt imm
  | .bne rs rt imm => mkIT 0x05#32 rs rt imm
  | .blez rs imm => mkIT 0x06#32 rs 0#32 imm
  | .bgtz rs imm => mkIT 0x07#32 rs 0#32 imm
  | .bltz   rs imm => mkIT 0x01#32 rs 0x00#32 imm
  | .bgez   rs imm => mkIT 0x01#32 rs 0x01#32 imm
  | .bltzal rs imm => mkIT 0x01#32 rs 0x10#32 imm
  | .bgezal rs imm => mkIT 0x01#32 rs 0x11#32 imm
  | .teqi   rs imm => mkIT 0x01#32 rs 0x0c#32 imm
  | .tnei   rs imm => mkIT 0x01#32 rs 0x0e#32 imm
  | .tgei   rs imm => mkIT 0x01#32 rs 0x08#32 imm
  | .tgeiu  rs imm => mkIT 0x01#32 rs 0x09#32 imm
  | .tlti   rs imm => mkIT 0x01#32 rs 0x0a#32 imm
  | .tltiu  rs imm => mkIT 0x01#32 rs 0x0b#32 imm
  | .synci  rs imm => mkIT 0x01#32 rs 0x1f#32 imm
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
  -- sync: no stored `stype` field, so this always encodes `stype = 0`
  -- (the default "complete barrier"), same simplification as `break`'s
  -- unmodeled "code" field.
  | .sync => mkRT 0#32 0#32 0#32 0#32 0x0f#32
  -- Coprocessor 0 (CP0). Same opcode-OR convention as the COP1 cases below.
  | .mfc0 rt rd => (0x10#32 <<< 26) ||| mkRT 0x00#32 rt rd 0#32 0#32
  | .mtc0 rt rd => (0x10#32 <<< 26) ||| mkRT 0x04#32 rt rd 0#32 0#32
  | .eret => (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32
  | .wait => (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x20#32
  -- Coprocessor 1 (FPU). `mkRT` leaves the opcode field 0 (correct for
  -- plain R-type), so the COP1 cases OR in opcode 0x11 explicitly, the same
  -- way `.j`/`.jal` OR in their opcode over `mkJT`'s target-only field.
  | .mfc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x00#32 rt fs 0#32 0#32
  | .mtc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x04#32 rt fs 0#32 0#32
  | .lwc1 rs ft imm => mkIT 0x31#32 rs ft imm
  | .swc1 rs ft imm => mkIT 0x39#32 rs ft imm
  | .ldc1 rs ft imm => mkIT 0x35#32 rs ft imm
  | .sdc1 rs ft imm => mkIT 0x3d#32 rs ft imm
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
  | .sqrtS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x04#32
  | .absS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x05#32
  | .negS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x07#32
  | .roundWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0c#32
  | .truncWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0d#32
  | .ceilWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0e#32
  | .floorWS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x0f#32
  | .cFS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x30#32
  | .cUnS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x31#32
  | .cUeqS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x33#32
  | .cOltS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x34#32
  | .cUltS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x35#32
  | .cOleS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x36#32
  | .cUleS fs ft => (0x11#32 <<< 26) ||| mkRT 0x10#32 ft fs 0#32 0x37#32
  -- Double-precision (`.d`): `fmt` = `D` = 0x11, same field shape as the
  -- single-precision cases above; `cvtDS`/`cvtDW` use the *source*'s `fmt`
  -- (`S`/`W`), same convention as `cvtSW`/`cvtWS`.
  | .addD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x00#32
  | .subD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x01#32
  | .mulD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x02#32
  | .divD fd fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs fd 0x03#32
  | .movD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x06#32
  | .cvtDS fd fs => (0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 fs fd 0x21#32
  | .cvtSD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x20#32
  | .cvtDW fd fs => (0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 fs fd 0x21#32
  | .cvtWD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x24#32
  | .sqrtD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x04#32
  | .absD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x05#32
  | .negD fd fs => (0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 fs fd 0x07#32
  | .cEqD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x32#32
  | .cLtD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x3c#32
  | .cLeD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x3e#32
  | .cFD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x30#32
  | .cUnD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x31#32
  | .cUeqD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x33#32
  | .cOltD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x34#32
  | .cUltD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x35#32
  | .cOleD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x36#32
  | .cUleD fs ft => (0x11#32 <<< 26) ||| mkRT 0x11#32 ft fs 0#32 0x37#32
  | .cfc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x02#32 rt fs 0#32 0#32
  | .ctc1 rt fs => (0x11#32 <<< 26) ||| mkRT 0x06#32 rt fs 0#32 0#32
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

-- R-type move, write direction: rs=29 (same field shape as jr)
example : decode (mkRT 29#32 0#32 0#32 0#32 0x11#32) = some (.mthi 29#32) := by decide
example : decode (mkRT 29#32 0#32 0#32 0#32 0x13#32) = some (.mtlo 29#32) := by decide

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

-- SPECIAL2 multiply-accumulate: rs=29, rt=8 (same rs/rt shape as mult/multu)
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x00#32) = some (.madd 29#32 8#32) := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x01#32) = some (.maddu 29#32 8#32) := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x04#32) = some (.msub 29#32 8#32) := by decide
example : decode ((0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x05#32) = some (.msubu 29#32 8#32) := by decide

-- SPECIAL3 BSHFL sign-extend/byte-swap: rd=3, rt=8, sub-field selects seb/seh/wsbh
example : decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x10#32 0x20#32) = some (.seb 3#32 8#32) := by decide
example : decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x18#32 0x20#32) = some (.seh 3#32 8#32) := by decide
example : decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x02#32 0x20#32) = some (.wsbh 3#32 8#32) := by decide
-- an unrecognized BSHFL sub-field (neither seb/seh/wsbh's) is out of v1+ scope → none
#guard decode ((0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x03#32 0x20#32) = none

-- rotr/rotrv (MIPS32r2): rd=3, rt=8, sa=5 / rs=29 -- share srl/srlv's
-- opcode/funct but overload the rs/shamt field to select rotate.
example : decode (mkRT 0x01#32 8#32 3#32 5#32 0x02#32) = some (.rotr 3#32 8#32 5#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0x01#32 0x06#32) = some (.rotrv 3#32 8#32 29#32) := by decide
-- rs=0 under funct 0x02 still decodes to plain srl (existing behavior unchanged)
example : decode (mkRT 0#32 8#32 3#32 5#32 0x02#32) = some (.srl 3#32 8#32 5#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x06#32) = some (.srlv 3#32 8#32 29#32) := by decide

-- ext/ins (MIPS32r2 bitfield extract/insert): rt=8, rs=29, pos=6, size=10
-- (so the raw `shamt` field is 6, and the raw `rd`-position field is
-- `size-1=9` for ext but `pos+size-1=15` for ins)
example : decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 9#32 6#32 0x00#32) = some (.ext 8#32 29#32 6#32 10#32) := by decide
example : decode ((0x1f#32 <<< 26) ||| mkRT 29#32 8#32 15#32 6#32 0x04#32) = some (.ins 8#32 29#32 6#32 10#32) := by decide
-- break: opcode 0, funct 0x0d, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0d#32) = some .break := by decide

-- sync: opcode 0, funct 0x0f, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0f#32) = some .sync := by decide
-- sync decodes the same way regardless of the (unmodeled) `stype` field,
-- here carried in the raw `shamt`-position bits (e.g. `stype = 0x10`,
-- a real MIPS32 "load ordering" hint value)
example : decode (mkRT 0#32 0#32 0#32 0x10#32 0x0f#32) = some .sync := by decide

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

-- lwl/lwr/swl/swr: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset) --
-- identical field layout to lw/sw
example : decode (mkIT 0x22#32 29#32 8#32 0x1234#32) = some (.lwl 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x26#32 29#32 8#32 0x1234#32) = some (.lwr 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x2a#32 29#32 8#32 0x1234#32) = some (.swl 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x2e#32 29#32 8#32 0x1234#32) = some (.swr 29#32 8#32 0x1234#32) := by decide

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
-- REGIMM trap-immediate family: same opcode 0x01, `rt` field selects
-- teqi/tnei/tgei/tgeiu/tlti/tltiu (real MIPS32 ISA, MD00086 Rev 2.50 §3.2,
-- Table 3-2 -- see docs/spec/MIPS-COVERAGE-GAPS.md §3.8).
example : decode (mkIT 0x01#32 29#32 0x0c#32 0x1234#32) = some (.teqi 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x0e#32 0x1234#32) = some (.tnei 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x08#32 0x1234#32) = some (.tgei 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x09#32 0x1234#32) = some (.tgeiu 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x0a#32 0x1234#32) = some (.tlti 29#32 0x1234#32) := by decide
example : decode (mkIT 0x01#32 29#32 0x0b#32 0x1234#32) = some (.tltiu 29#32 0x1234#32) := by decide
-- synci: same opcode 0x01, `rt` field fixed 0x1f (real MIPS32 MIPS32r2
-- addition, docs/spec/MIPS-COVERAGE-GAPS.md §3.7), `rs, imm` shape
-- identical to `blez`/`bgtz`.
example : decode (mkIT 0x01#32 29#32 0x1f#32 0x1234#32) = some (.synci 29#32 0x1234#32) := by decide
-- a REGIMM word with an unrecognized rt field (0x1d is reserved in the
-- real MIPS32 REGIMM table -- not one of bltz/bgez/bltzal/bgezal/the trap
-- family/synci above) decodes to none
#guard decode (mkIT 0x01#32 29#32 0x1d#32 0x1234#32) = none

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
-- sqrt.s/abs.s/neg.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x04#32) = some (.sqrtS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x05#32) = some (.absS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x07#32) = some (.negS 8#32 7#32) := by decide
-- round.w.s/trunc.w.s/ceil.w.s/floor.w.s: fmt=S, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0c#32) = some (.roundWS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0d#32) = some (.truncWS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0e#32) = some (.ceilWS 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x0f#32) = some (.floorWS 8#32 7#32) := by decide
-- c.f.s/c.un.s/c.ueq.s/c.olt.s/c.ult.s/c.ole.s/c.ule.s: fmt=S, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x30#32) = some (.cFS 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x31#32) = some (.cUnS 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x33#32) = some (.cUeqS 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x34#32) = some (.cOltS 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x35#32) = some (.cUltS 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x36#32) = some (.cOleS 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 0#32 0x37#32) = some (.cUleS 7#32 6#32) := by decide
-- c.un.s with a nonzero cc field (unsupported, only cc=0 modeled) → none
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 6#32 7#32 1#32 0x31#32) = none := by decide

-- ldc1/sdc1: rs=29 (base), ft=5, imm=0x1234 (identical layout to lwc1/swc1)
example : decode (mkIT 0x35#32 29#32 5#32 0x1234#32) = some (.ldc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (mkIT 0x3d#32 29#32 5#32 0x1234#32) = some (.sdc1 29#32 5#32 0x1234#32) := by
  decide
-- add.d/sub.d/mul.d/div.d: fmt=D, ft=6, fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x00#32) = some (.addD 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x01#32) = some (.subD 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x02#32) = some (.mulD 8#32 7#32 6#32) := by
  decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 8#32 0x03#32) = some (.divD 8#32 7#32 6#32) := by
  decide
-- mov.d/sqrt.d/abs.d/neg.d/cvt.w.d: fmt=D, fs=7, fd=8 (ft-position fixed 0)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x06#32) = some (.movD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x04#32) = some (.sqrtD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x05#32) = some (.absD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x07#32) = some (.negD 8#32 7#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x24#32) = some (.cvtWD 8#32 7#32) := by
  decide
-- cvt.d.s: fmt=S (source is single), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x10#32 0#32 7#32 8#32 0x21#32) = some (.cvtDS 8#32 7#32) := by
  decide
-- cvt.s.d: fmt=D (source is double), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 0#32 7#32 8#32 0x20#32) = some (.cvtSD 8#32 7#32) := by
  decide
-- cvt.d.w: fmt=W (source is a word), fs=7, fd=8
example : decode ((0x11#32 <<< 26) ||| mkRT 0x14#32 0#32 7#32 8#32 0x21#32) = some (.cvtDW 8#32 7#32) := by
  decide
-- c.eq.d/c.lt.d/c.le.d/c.f.d/c.un.d/c.ueq.d/c.olt.d/c.ult.d/c.ole.d/c.ule.d:
-- fmt=D, fs=7, ft=6, fd-position (cc) fixed 0
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x32#32) = some (.cEqD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x3c#32) = some (.cLtD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x3e#32) = some (.cLeD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x30#32) = some (.cFD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x31#32) = some (.cUnD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x33#32) = some (.cUeqD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x34#32) = some (.cOltD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x35#32) = some (.cUltD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x36#32) = some (.cOleD 7#32 6#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 0#32 0x37#32) = some (.cUleD 7#32 6#32) := by decide
-- c.eq.d with a nonzero cc field (unsupported, only cc=0 modeled) → none
example : decode ((0x11#32 <<< 26) ||| mkRT 0x11#32 6#32 7#32 1#32 0x32#32) = none := by decide

-- cfc1/mfc1 share the same (rt, fs) field shape, distinguished by the
-- rs-position sub-opcode (CF=0x02 vs MF=0x00); ctc1/mtc1 likewise (CT=0x06 vs MT=0x04)
example : decode ((0x11#32 <<< 26) ||| mkRT 0x02#32 8#32 3#32 0#32 0#32) = some (.cfc1 8#32 3#32) := by decide
example : decode ((0x11#32 <<< 26) ||| mkRT 0x06#32 8#32 3#32 0#32 0#32) = some (.ctc1 8#32 3#32) := by decide
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
example : encode (.wsbh 3#32 8#32) = (0x1f#32 <<< 26) ||| mkRT 0#32 8#32 3#32 0x02#32 0x20#32 := by decide
example : encode (.rotr 3#32 8#32 5#32) = mkRT 0x01#32 8#32 3#32 5#32 0x02#32 := by decide
example : encode (.rotrv 3#32 8#32 29#32) = mkRT 29#32 8#32 3#32 0x01#32 0x06#32 := by decide
example : encode (.ext 8#32 29#32 6#32 10#32) = (0x1f#32 <<< 26) ||| mkRT 29#32 8#32 9#32 6#32 0x00#32 := by decide
example : encode (.ins 8#32 29#32 6#32 10#32) = (0x1f#32 <<< 26) ||| mkRT 29#32 8#32 15#32 6#32 0x04#32 := by decide
example : encode (.sllv 3#32 8#32 29#32) = mkRT 29#32 8#32 3#32 0#32 0x04#32 := by decide
example : encode (.mul 29#32 8#32 3#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 3#32 0#32 0x02#32 := by decide
example : encode (.madd 29#32 8#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x00#32 := by decide
example : encode (.maddu 29#32 8#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x01#32 := by decide
example : encode (.msub 29#32 8#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x04#32 := by decide
example : encode (.msubu 29#32 8#32) = (0x1c#32 <<< 26) ||| mkRT 29#32 8#32 0#32 0#32 0x05#32 := by decide
example : encode (.mthi 29#32) = mkRT 29#32 0#32 0#32 0#32 0x11#32 := by decide
example : encode (.mtlo 29#32) = mkRT 29#32 0#32 0#32 0#32 0x13#32 := by decide
example : encode (.jr 29#32) = mkRT 29#32 0#32 0#32 0#32 0x08#32 := by decide
example : encode (.jalr 29#32 3#32) = mkRT 29#32 0#32 3#32 0#32 0x09#32 := by decide
-- full round trip for every new instruction (decode ∘ encode = id on the field values we store)
example : decode (encode (.movn 29#32 8#32 3#32)) = some (.movn 29#32 8#32 3#32) := by decide
example : decode (encode (.movz 29#32 8#32 3#32)) = some (.movz 29#32 8#32 3#32) := by decide
example : decode (encode (.clo 29#32 3#32)) = some (.clo 29#32 3#32) := by decide
example : decode (encode (.clz 29#32 3#32)) = some (.clz 29#32 3#32) := by decide
example : decode (encode (.seb 3#32 8#32)) = some (.seb 3#32 8#32) := by decide
example : decode (encode (.seh 3#32 8#32)) = some (.seh 3#32 8#32) := by decide
example : decode (encode (.wsbh 3#32 8#32)) = some (.wsbh 3#32 8#32) := by decide
example : decode (encode (.rotr 3#32 8#32 5#32)) = some (.rotr 3#32 8#32 5#32) := by decide
example : decode (encode (.rotrv 3#32 8#32 29#32)) = some (.rotrv 3#32 8#32 29#32) := by decide
example : decode (encode (.ext 8#32 29#32 6#32 10#32)) = some (.ext 8#32 29#32 6#32 10#32) := by decide
example : decode (encode (.ins 8#32 29#32 6#32 10#32)) = some (.ins 8#32 29#32 6#32 10#32) := by decide
-- ext/ins round-trip edge cases: pos=0 (size=32, the full word) and
-- pos+size=32 (touches the top bit) -- both satisfy the real `pos+size<=32`
-- constraint so the `rd`-position field packs/unpacks without truncation.
example : decode (encode (.ext 8#32 29#32 0#32 32#32)) = some (.ext 8#32 29#32 0#32 32#32) := by decide
example : decode (encode (.ins 8#32 29#32 20#32 12#32)) = some (.ins 8#32 29#32 20#32 12#32) := by decide
example : decode (encode (.sllv 3#32 8#32 29#32)) = some (.sllv 3#32 8#32 29#32) := by decide
example : decode (encode (.srlv 3#32 8#32 29#32)) = some (.srlv 3#32 8#32 29#32) := by decide
example : decode (encode (.srav 3#32 8#32 29#32)) = some (.srav 3#32 8#32 29#32) := by decide
example : decode (encode (.mul 29#32 8#32 3#32)) = some (.mul 29#32 8#32 3#32) := by decide
example : decode (encode (.madd 29#32 8#32)) = some (.madd 29#32 8#32) := by decide
example : decode (encode (.maddu 29#32 8#32)) = some (.maddu 29#32 8#32) := by decide
example : decode (encode (.msub 29#32 8#32)) = some (.msub 29#32 8#32) := by decide
example : decode (encode (.msubu 29#32 8#32)) = some (.msubu 29#32 8#32) := by decide
example : decode (encode (.mthi 29#32)) = some (.mthi 29#32) := by decide
example : decode (encode (.mtlo 29#32)) = some (.mtlo 29#32) := by decide
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

-- sync/synci: encode matches the hand-computed word, and decode (encode i) = some i
example : encode .sync = mkRT 0#32 0#32 0#32 0#32 0x0f#32 := by decide
example : encode (.synci 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x1f#32 0x1234#32 := by decide
example : decode (encode .sync) = some .sync := by decide
example : decode (encode (.synci 29#32 0x1234#32)) = some (.synci 29#32 0x1234#32) := by decide

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
example : decode (encode (.sqrtS 8#32 7#32)) = some (.sqrtS 8#32 7#32) := by decide
example : decode (encode (.absS 8#32 7#32)) = some (.absS 8#32 7#32) := by decide
example : decode (encode (.negS 8#32 7#32)) = some (.negS 8#32 7#32) := by decide
example : decode (encode (.roundWS 8#32 7#32)) = some (.roundWS 8#32 7#32) := by decide
example : decode (encode (.truncWS 8#32 7#32)) = some (.truncWS 8#32 7#32) := by decide
example : decode (encode (.ceilWS 8#32 7#32)) = some (.ceilWS 8#32 7#32) := by decide
example : decode (encode (.floorWS 8#32 7#32)) = some (.floorWS 8#32 7#32) := by decide
example : decode (encode (.cFS 7#32 6#32)) = some (.cFS 7#32 6#32) := by decide
example : decode (encode (.cUnS 7#32 6#32)) = some (.cUnS 7#32 6#32) := by decide
example : decode (encode (.cUeqS 7#32 6#32)) = some (.cUeqS 7#32 6#32) := by decide
example : decode (encode (.cOltS 7#32 6#32)) = some (.cOltS 7#32 6#32) := by decide
example : decode (encode (.cUltS 7#32 6#32)) = some (.cUltS 7#32 6#32) := by decide
example : decode (encode (.cOleS 7#32 6#32)) = some (.cOleS 7#32 6#32) := by decide
example : decode (encode (.cUleS 7#32 6#32)) = some (.cUleS 7#32 6#32) := by decide
example : decode (encode (.cfc1 8#32 3#32)) = some (.cfc1 8#32 3#32) := by decide
example : decode (encode (.ctc1 8#32 3#32)) = some (.ctc1 8#32 3#32) := by decide
example : decode (encode (.bc1t 0x1234#32)) = some (.bc1t 0x1234#32) := by decide
example : decode (encode (.bc1f 0x1234#32)) = some (.bc1f 0x1234#32) := by decide

-- Coprocessor 1 (FPU), double-precision: full `decode (encode i) = some i` round-trips
example : decode (encode (.ldc1 29#32 5#32 0x1234#32)) = some (.ldc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (encode (.sdc1 29#32 5#32 0x1234#32)) = some (.sdc1 29#32 5#32 0x1234#32) := by
  decide
example : decode (encode (.addD 8#32 7#32 6#32)) = some (.addD 8#32 7#32 6#32) := by decide
example : decode (encode (.subD 8#32 7#32 6#32)) = some (.subD 8#32 7#32 6#32) := by decide
example : decode (encode (.mulD 8#32 7#32 6#32)) = some (.mulD 8#32 7#32 6#32) := by decide
example : decode (encode (.divD 8#32 7#32 6#32)) = some (.divD 8#32 7#32 6#32) := by decide
example : decode (encode (.movD 8#32 7#32)) = some (.movD 8#32 7#32) := by decide
example : decode (encode (.cvtDS 8#32 7#32)) = some (.cvtDS 8#32 7#32) := by decide
example : decode (encode (.cvtSD 8#32 7#32)) = some (.cvtSD 8#32 7#32) := by decide
example : decode (encode (.cvtDW 8#32 7#32)) = some (.cvtDW 8#32 7#32) := by decide
example : decode (encode (.cvtWD 8#32 7#32)) = some (.cvtWD 8#32 7#32) := by decide
example : decode (encode (.sqrtD 8#32 7#32)) = some (.sqrtD 8#32 7#32) := by decide
example : decode (encode (.absD 8#32 7#32)) = some (.absD 8#32 7#32) := by decide
example : decode (encode (.negD 8#32 7#32)) = some (.negD 8#32 7#32) := by decide
example : decode (encode (.cEqD 7#32 6#32)) = some (.cEqD 7#32 6#32) := by decide
example : decode (encode (.cLtD 7#32 6#32)) = some (.cLtD 7#32 6#32) := by decide
example : decode (encode (.cLeD 7#32 6#32)) = some (.cLeD 7#32 6#32) := by decide
example : decode (encode (.cFD 7#32 6#32)) = some (.cFD 7#32 6#32) := by decide
example : decode (encode (.cUnD 7#32 6#32)) = some (.cUnD 7#32 6#32) := by decide
example : decode (encode (.cUeqD 7#32 6#32)) = some (.cUeqD 7#32 6#32) := by decide
example : decode (encode (.cOltD 7#32 6#32)) = some (.cOltD 7#32 6#32) := by decide
example : decode (encode (.cUltD 7#32 6#32)) = some (.cUltD 7#32 6#32) := by decide
example : decode (encode (.cOleD 7#32 6#32)) = some (.cOleD 7#32 6#32) := by decide
example : decode (encode (.cUleD 7#32 6#32)) = some (.cUleD 7#32 6#32) := by decide

-- REGIMM zero-comparison branches: full decode(encode i) = some i round-trips
example : decode (encode (.bltz 29#32 0x1234#32)) = some (.bltz 29#32 0x1234#32) := by decide
example : decode (encode (.bgez 29#32 0x1234#32)) = some (.bgez 29#32 0x1234#32) := by decide
example : decode (encode (.bltzal 29#32 0x1234#32)) = some (.bltzal 29#32 0x1234#32) := by decide
example : decode (encode (.bgezal 29#32 0x1234#32)) = some (.bgezal 29#32 0x1234#32) := by decide
-- REGIMM trap-immediate family: encode matches the hand-computed opcode,
-- and full decode(encode i) = some i round-trips.
example : encode (.teqi 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x0c#32 0x1234#32 := by decide
example : encode (.tnei 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x0e#32 0x1234#32 := by decide
example : encode (.tgei 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x08#32 0x1234#32 := by decide
example : encode (.tgeiu 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x09#32 0x1234#32 := by decide
example : encode (.tlti 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x0a#32 0x1234#32 := by decide
example : encode (.tltiu 29#32 0x1234#32) = mkIT 0x01#32 29#32 0x0b#32 0x1234#32 := by decide
example : decode (encode (.teqi 29#32 0x1234#32)) = some (.teqi 29#32 0x1234#32) := by decide
example : decode (encode (.tnei 29#32 0x1234#32)) = some (.tnei 29#32 0x1234#32) := by decide
example : decode (encode (.tgei 29#32 0x1234#32)) = some (.tgei 29#32 0x1234#32) := by decide
example : decode (encode (.tgeiu 29#32 0x1234#32)) = some (.tgeiu 29#32 0x1234#32) := by decide
example : decode (encode (.tlti 29#32 0x1234#32)) = some (.tlti 29#32 0x1234#32) := by decide
example : decode (encode (.tltiu 29#32 0x1234#32)) = some (.tltiu 29#32 0x1234#32) := by decide
-- ll/sc: encode matches the hand-computed opcode, and decode (encode i) = some i
example : encode (.ll 29#32 8#32 0x1234#32) = mkIT 0x30#32 29#32 8#32 0x1234#32 := by decide
example : encode (.sc 29#32 8#32 0x1234#32) = mkIT 0x38#32 29#32 8#32 0x1234#32 := by decide
example : decode (encode (.ll 29#32 8#32 0x1234#32)) = some (.ll 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.sc 29#32 8#32 0x1234#32)) = some (.sc 29#32 8#32 0x1234#32) := by decide
-- lwl/lwr/swl/swr: encode matches the hand-computed opcode, and
-- decode (encode i) = some i
example : encode (.lwl 29#32 8#32 0x1234#32) = mkIT 0x22#32 29#32 8#32 0x1234#32 := by decide
example : encode (.lwr 29#32 8#32 0x1234#32) = mkIT 0x26#32 29#32 8#32 0x1234#32 := by decide
example : encode (.swl 29#32 8#32 0x1234#32) = mkIT 0x2a#32 29#32 8#32 0x1234#32 := by decide
example : encode (.swr 29#32 8#32 0x1234#32) = mkIT 0x2e#32 29#32 8#32 0x1234#32 := by decide
example : decode (encode (.lwl 29#32 8#32 0x1234#32)) = some (.lwl 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.lwr 29#32 8#32 0x1234#32)) = some (.lwr 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.swl 29#32 8#32 0x1234#32)) = some (.swl 29#32 8#32 0x1234#32) := by decide
example : decode (encode (.swr 29#32 8#32 0x1234#32)) = some (.swr 29#32 8#32 0x1234#32) := by decide

-- unknown opcodes → none
#guard decode (mkIT 0x3a#32 0#32 0#32 0#32) = none  -- opcode 0x3a, unassigned/not in v1+ scope
-- opcode 0x11 (COP1) is implemented for the fmt/funct combinations below;
-- an unrecognized fmt (not MF/MT/BC1/S/W) still decodes to `none`.
#guard decode (mkIT 0x11#32 0x1f#32 0#32 0#32) = none
#guard decode (mkIT 0x16#32 0#32 0#32 0#32) = none
#guard decode (mkIT 0x17#32 0#32 0#32 0#32) = none
-- opcode 0x1c (SPECIAL2) funct 0x00/0x01/0x02/0x04/0x05/0x20/0x21 are now
-- assigned (madd/maddu/mul/msub/msubu/clz/clo); funct 0x3f remains unassigned.
#guard decode (mkIT 0x1c#32 0#32 0#32 0x3f#32) = none
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
#guard decode (encode (.addD 8#32 7#32 6#32)) = some (.addD 8#32 7#32 6#32)
#guard decode (encode (.ldc1 29#32 5#32 0x1234#32)) = some (.ldc1 29#32 5#32 0x1234#32)

-- Coprocessor 0 (CP0) register move / execution control: mfc0/mtc0/eret/wait
-- (docs/spec/MIPS-COVERAGE-GAPS.md §3.10A). rt=8 (GPR), rd=13 (Cause).
example : decode ((0x10#32 <<< 26) ||| mkRT 0x00#32 8#32 13#32 0#32 0#32)
  = some (.mfc0 8#32 13#32) := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x04#32 8#32 13#32 0#32 0#32)
  = some (.mtc0 8#32 13#32) := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32)
  = some .eret := by decide
example : decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x20#32)
  = some .wait := by decide

-- encode produces the exact hand-computed words above.
example : encode (.mfc0 8#32 13#32) = (0x10#32 <<< 26) ||| mkRT 0x00#32 8#32 13#32 0#32 0#32 := by
  decide
example : encode (.mtc0 8#32 13#32) = (0x10#32 <<< 26) ||| mkRT 0x04#32 8#32 13#32 0#32 0#32 := by
  decide
example : encode .eret = (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x18#32 := by decide
example : encode .wait = (0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x20#32 := by decide

-- full decode ∘ encode round trips, across all three real CP0 register numbers.
example : decode (encode (.mfc0 8#32 12#32)) = some (.mfc0 8#32 12#32) := by decide
example : decode (encode (.mfc0 8#32 13#32)) = some (.mfc0 8#32 13#32) := by decide
example : decode (encode (.mfc0 8#32 14#32)) = some (.mfc0 8#32 14#32) := by decide
example : decode (encode (.mtc0 8#32 12#32)) = some (.mtc0 8#32 12#32) := by decide
example : decode (encode (.mtc0 8#32 13#32)) = some (.mtc0 8#32 13#32) := by decide
example : decode (encode (.mtc0 8#32 14#32)) = some (.mtc0 8#32 14#32) := by decide
example : decode (encode .eret) = some .eret := by decide
example : decode (encode .wait) = some .wait := by decide

-- an unrecognized COP0 `rs`-field (not MF/MT/CO) decodes to `none`.
#guard decode (mkIT 0x10#32 0x08#32 0#32 0#32) = none
-- a CO-sub-format word with an unrecognized `funct` (not eret's 0x18 or
-- wait's 0x20) decodes to `none`.
#guard decode ((0x10#32 <<< 26) ||| mkRT 0x10#32 0#32 0#32 0#32 0x01#32) = none
