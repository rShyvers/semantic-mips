# MARS MIPS v1 Instruction Reference

This document is a precise, source-grounded reference for the ~24 machine
instructions plus 4 syscalls in Lean spec v1 scope, intended to ground the
`step` function for MARS MIPS small-step semantics. Every semantic claim is
cited against the vendored MARS 4.5 source (`vendor/mars-src/`). Where MARS
deviates from "textbook" MIPS, or where the source is ambiguous/inconsistent,
this is flagged explicitly rather than normalized away.

A later, purely-additive extension ("MIPS32 / MIPS32r2 additions" section,
near the end of this document) adds six more real MIPS32/MIPS32r2 integer
instructions (`movn`, `movz`, `clo`, `clz`, `seb`, `seh`) beyond the original
v1 subset. Those six are grounded directly in the standard MIPS32 ISA rather
than the MARS source (see that section's header note for why).
On top of that MARS-grounded v1 set, a minimal coprocessor-0 trap/exception
model has since been added (`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu`/`break`,
plus `cp0Status`/`cp0Cause`/`cp0Epc`). That addition is grounded in the real
MIPS32 ISA, not MARS — see the dedicated
["Coprocessor 0 / traps and exceptions"](#coprocessor-0--traps-and-exceptions-real-mips32-isa)
section below, which is explicit about this difference in sourcing.
A further v1.x addition ("MIPS32 GPR multiply and variable shifts" section,
at the end of this document) adds `mul`, `sllv`, `srlv`, and `srav` — also
grounded directly in the standard MIPS32 ISA, not MARS — per
`docs/spec/MIPS-COVERAGE-GAPS.md` §§3.4-3.5's finding that real compilers
essentially never emit this project's existing `mult`+`mflo`/constant-`sll`
sequences for plain 32-bit multiplication/variable shifts.
Separately, the real MIPS32 register-indirect jump/call pair `jr`/`jalr`
(the single highest-priority gap identified in
[`MIPS-COVERAGE-GAPS.md`](MIPS-COVERAGE-GAPS.md) §3.1 — without them no
compiled function can return or call through a function pointer) has also
been added, likewise grounded in the real MIPS32 ISA rather than MARS — see
the dedicated
["Register-indirect jump/call"](#register-indirect-jumpcall-real-mips32-isa)
section below.

Conventions pinned elsewhere and assumed here (see
[`SPEC-NOTES.md`](SPEC-NOTES.md)): one real-MIPS32 branch delay slot per
branch/jump (not MARS's default `DelayedBranching=false` no-delay-slot
config — see Global rule 3); execution starts at `0x00400000`; big-endian
memory; 32 GPRs plus separate 64-bit `hi`/`lo` pair (internally registers
33/34); `$zero` write-ignored.

All line numbers below refer to
`vendor/mars-src/mars/mips/instructions/InstructionSet.java` unless otherwise
noted. The `simulate()` method body for each instruction is the authoritative
execution logic (method `populate()`, lines 77–3236).

---

## Summary table

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `add` | R | `$rd = $rs + $rt`, signed; traps on signed overflow |
| `addu` | R | `$rd = $rs + $rt`, wraps, never traps |
| `sub` | R | `$rd = $rs - $rt`, signed; traps on signed overflow |
| `subu` | R | `$rd = $rs - $rt`, wraps, never traps |
| `and` | R | `$rd = $rs & $rt` |
| `or` | R | `$rd = $rs \| $rt` |
| `xor` | R | `$rd = $rs ^ $rt` |
| `nor` | R | `$rd = ~($rs \| $rt)` |
| `sll` | R | `$rd = $rt << shamt` (logical, zero-fill) |
| `srl` | R | `$rd = $rt >> shamt` (logical, zero-fill) |
| `sra` | R | `$rd = $rt >> shamt` (arithmetic, sign-fill) |
| `slt` | R | `$rd = ($rs < $rt) ? 1 : 0`, signed compare |
| `sltu` | R | `$rd = ($rs < $rt) ? 1 : 0`, unsigned compare |
| `mult` | R | `{hi,lo} = $rs * $rt`, signed 64-bit product |
| `multu` | R | `{hi,lo} = $rs * $rt`, unsigned 64-bit product |
| `div` | R | `lo = $rs / $rt`, `hi = $rs % $rt`, signed; no-op on `$rt == 0` |
| `divu` | R | `lo = $rs / $rt`, `hi = $rs % $rt`, unsigned; no-op on `$rt == 0` |
| `mflo` | R | `$rd = lo` |
| `mfhi` | R | `$rd = hi` |
| `addi` | I | `$rt = $rs + sext16(imm)`, traps on signed overflow |
| `addiu` | I | `$rt = $rs + sext16(imm)`, wraps, never traps |
| `slti` | I | `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed compare |
| `sltiu` | I | `$rt = ($rs < sext16(imm)) ? 1 : 0`, unsigned compare on sign-extended imm |
| `andi` | I | `$rt = $rs & zext16(imm)` |
| `ori` | I | `$rt = $rs \| zext16(imm)` |
| `xori` | I | `$rt = $rs ^ zext16(imm)` |
| `lui` | I | `$rt = imm << 16` (low 16 bits zero) |
| `lw` | I | `$rt = MEM32[$rs + offset]`, word-aligned |
| `sw` | I | `MEM32[$rs + offset] = $rt`, word-aligned |
| `lb` | I | `$rt = sext8(MEM8[$rs + offset])` |
| `lbu` | I | `$rt = zext8(MEM8[$rs + offset])` |
| `lh` | I | `$rt = sext16(MEM16[$rs + offset])`, halfword-aligned |
| `lhu` | I | `$rt = zext16(MEM16[$rs + offset])`, halfword-aligned |
| `sh` | I | `MEM16[$rs + offset] = $rt[15:0]`, halfword-aligned |
| `j` | J | `PC = (PC_next & 0xF0000000) \| (target << 2)` |
| `jal` | J | `$ra = PC_next; PC = (PC_next & 0xF0000000) \| (target << 2)` |
| `beq` | I-branch | `if ($rs == $rt) PC = PC_next + (offset << 2)` |
| `bne` | I-branch | `if ($rs != $rt) PC = PC_next + (offset << 2)` |
| `blez` | I-branch | `if ($rs <= 0) PC = PC_next + (offset << 2)` |
| `bgtz` | I-branch | `if ($rs > 0) PC = PC_next + (offset << 2)` |
| syscall 1 | — | print signed decimal integer in `$a0` |
| syscall 4 | — | print null-terminated byte string starting at address `$a0` |
| syscall 10 | — | terminate program normally |
| syscall 11 | — | print low byte of `$a0` as a character |
| `teq` | R | `if ($rs == $rt) trap` |
| `tne` | R | `if ($rs != $rt) trap` |
| `tlt` | R | `if ($rs < $rt) trap`, signed |
| `tge` | R | `if ($rs >= $rt) trap`, signed |
| `tltu` | R | `if ($rs < $rt) trap`, unsigned |
| `tgeu` | R | `if ($rs >= $rt) trap`, unsigned |
| `break` | R | unconditional trap |

`PC_next` denotes the program counter value *after* the fetched instruction
has been accounted for, i.e. `PC_at_fetch + 4` — see Global rule 1.

Pseudo-instructions (`li`, `la`, `move`, `nop` as written by the user, `ble`,
`bge`, etc.) are assembler sugar expanded per
`vendor/mars-src/PseudoOps.txt`; they are **not** documented here as machine
instructions.

---

## Global rules

### 1. PC update timing and per-class behavior

Source: `vendor/mars-src/mars/simulator/Simulator.java`, lines 325–327
(fetch/increment loop) and `InstructionSet.java` lines 3265–3303
(`processBranch`, `processJump`, `processReturnAddress`).

- The simulator fetches the instruction at the current PC, **then
  increments PC by 4** (`RegisterFile.incrementPC()`, line 327), **then**
  calls `simulate()`. So by the time any instruction's semantics run, `PC`
  already holds the address of the sequentially-next instruction
  (`PC_next` in this document).
- **Non-control-flow instructions** (arith/logic/mem): PC is left at
  `PC_next`; execution continues there.
- **Branches** (`beq`,`bne`,`blez`,`bgtz`): the *target address formula* is
  `PC = PC_next + (displacement << 2)` (`InstructionSet.java` line ~3272,
  `processBranch`; `displacement` is the instruction's signed 16-bit offset
  field) — standard MIPS branch-target arithmetic, PC-relative to the
  instruction *after* the branch, scaled by 4. **Our semantics overrides
  MARS's *timing* of when this target is applied**: real MIPS32 always
  executes one delay-slot instruction first (see rule 3), so a taken branch
  *schedules* this target rather than jumping to it immediately (MARS's
  default `DelayedBranching=false` path jumps immediately instead; we do
  not follow that part of MARS).
- **Jumps** (`j`,`jal`): the *target address formula* is
  `targetAddress = (PC_next & 0xF0000000) | (target_field << 2)`
  (`InstructionSet.java` lines ~1207–1211, 1238–1240) — the top 4 bits come
  from `PC_next`, not from the jump instruction's own address. As with
  branches, our semantics *schedules* this target via the delay slot (rule
  3) rather than applying it immediately.
- **Link instructions** (`jal`): the address-*formula* source
  (`processReturnAddress(31)`, `InstructionSet.java` lines 3309–3315) sets
  `$ra = PC_next` only when delayed branching is disabled (MARS's default).
  **Our semantics does not follow that**: since we always execute one
  delay-slot instruction, `$ra` must be `PC_next + 4` (`pc + 8` relative to
  `jal`'s own address) — the address *after* the delay slot — matching real
  MIPS32, not MARS's no-delay-slot default (see rule 3).

### 2. `$zero` is write-ignored

Source: `vendor/mars-src/mars/mips/hardware/RegisterFile.java`,
`updateRegister(int num, int val)`, lines 95–119: when `num == 0` the method
takes the empty branch and returns `old = 0` without touching the register
array. Reads of register 0 always return `0` (it is initialized to 0 and
never written). Every instruction below that writes `$rd`/`$rt` is silently
a no-op if that operand is `$zero`.

### 3. Branch/jump delay slots (real MIPS32 semantics)

Ground truth: the real MIPS32 architecture (not MARS). Every branch
(`beq`,`bne`,`blez`,`bgtz`) and jump (`j`,`jal`) has exactly **one**
architecturally-mandated delay slot: the single instruction immediately
following it in program order always executes — whether or not the branch
is taken — *before* control transfers to the target.

- **Taken branch/jump**: the delay-slot instruction (at `pc + 4`) executes
  normally; *after* it retires, `pc` becomes the branch/jump target (not
  `pc + 4 + 4`). Modeled in `Semantics/Step.lean` as: the branch/jump
  itself falls through to `pc + 4` and records the real target in
  `State.pendingBranch : Option W32`; the delay-slot instruction's own step
  (any ordinary, non-branch-like instruction) commits the scheduled target
  to `pc` via `advance`/`mkNext`.
- **Not-taken branch**: behaves exactly like an ordinary instruction (falls
  through to `pc + 4`, `pendingBranch` stays `none`) — no observable
  difference from a world without delay slots.
- **`jal`'s `$ra`** is `pc + 8` (past the delay slot), not `pc + 4` — see
  rule 1.
- **A branch/jump occurring itself in another's delay slot** (i.e.
  immediately after a *taken* branch/jump) is architecturally
  discouraged/implementation-defined on real MIPS32. Rather than guess,
  `step` halts with `HaltReason.branchInDelaySlot` whenever the instruction
  about to execute is itself one of the six branch/jump instructions and
  `State.pendingBranch` is still `some _` from the previous step — this
  keeps `step` total and the condition diagnosable instead of silently
  picking an arbitrary (and likely wrong) behavior.

This **overrides MARS's own default configuration**
(`vendor/mars-src/mars/mips/instructions/InstructionSet.java`,
`processBranch`/`processJump`, lines 3265–3306, gated on
`Globals.getSettings().getDelayedBranchingEnabled()`;
`vendor/mars-src/mars/Settings.java`'s `DelayedBranching` defaults to
`false`), under which a taken branch/jump updates `PC` to the target
*immediately*, with no delay-slot instruction executed at all. MARS is only
ever used by this project as a differential-testing oracle, not as the spec
source (`SPEC-NOTES.md` §9 item 1); on this point we deliberately diverge
from MARS's default to match the real architecture instead. (MARS *can*
model delay slots if `DelayedBranching` is enabled, which would then agree
with this rule — but that MARS setting is not why we implement it this
way.)

### 4. Big-endian load/store byte order

Source: `vendor/mars-src/mars/mips/hardware/Memory.java`, header comment
line 44 ("This implementation is purely big-endian"), and
`storeOrFetchBytesInTable` (lines ~1272–1313), especially line 1301. The
class also has an internal `byteOrder` flag defaulting to the oddly-named
constant `LITTLE_ENDIAN = true` (lines 85–90); when that default internal
flag is set, `bytePositionInMemory` is flipped (`3 - bytePositionInMemory`),
which makes the **lowest byte address hold the most-significant byte** of a
stored word — i.e. the user-observable default behavior is big-endian,
matching `SPEC-NOTES.md` §7, despite the confusing internal constant name.
This internal naming is a documentation hazard in the MARS source itself,
not a behavioral deviation — `lw`/`sw`/`lh`/`sh`/`lb`/`sb` all agree on
address `A` holding byte `[31:24]` of the word at `A`, address `A+1` holding
`[23:16]`, etc.

### 5. Alignment requirements per access size

Source: `vendor/mars-src/mars/mips/hardware/Memory.java`:
- Word access (`lw`, `sw`, instruction fetch): address must be a multiple of
  4, else `AddressErrorException` ("...not aligned on word boundary",
  `getWord` line ~824, `setWord` line ~498).
- Halfword access (`lh`, `lhu`, `sh`): address must be a multiple of 2, else
  `AddressErrorException` ("...not aligned on halfword boundary", `setHalf`
  line ~520).
- Byte access (`lb`, `lbu`): no alignment requirement (`getByte`/`setByte`
  perform no modulus check).
- `AddressErrorException` carries a type, `Exceptions.ADDRESS_EXCEPTION_LOAD`
  (4) or `Exceptions.ADDRESS_EXCEPTION_STORE` (5)
  (`vendor/mars-src/mars/mips/hardware/AddressErrorException.java`,
  `vendor/mars-src/mars/simulator/Exceptions.java` lines 55–56), and is
  converted to a `ProcessingException` with a non-null error list at the
  instruction's catch site in `Simulator.java` (lines 352–380). With no
  exception handler installed at `0x80000180` (the v1-scope assumption),
  this halts the program with return reason `EXCEPTION`.
- Instruction fetch misalignment/out-of-range is handled separately at the
  top of the fetch loop (`Simulator.java` lines 273–288) and also halts with
  `EXCEPTION`.

---

## R-type arithmetic / logic

### add (R)
- **Encoding**: `opcode=000000`, `funct=100000` (0x20). Fields:
  `000000 sssss ttttt fffff 00000 100000` → `rs=sssss`($t2/src1),
  `rt=ttttt`($t3/src2), `rd=fffff`($t1/dest), `shamt=00000`.
- **Semantics**: `sum = $rs + $rt` computed as 32-bit signed Java `int`
  addition. If `$rd != $zero`, write `sum` to `$rd`. No memory access, no
  hi/lo update. PC already advanced to `PC_next` (rule 1); unaffected
  otherwise.
- **Errors/halts**: overflow check: `(rs>=0 && rt>=0 && sum<0) ||
  (rs<0 && rt<0 && sum>=0)` → throws `ProcessingException` with message
  `"arithmetic overflow"` and code `Exceptions.ARITHMETIC_OVERFLOW_EXCEPTION`
  (12). With no exception handler, this halts the program (`EXCEPTION`).
- **MARS note**: none — matches textbook MIPS (`add` traps on signed
  overflow; this is a deliberate design point of real MIPS too, not a MARS
  deviation).
- **Source**: `InstructionSet.java`, `add` instruction object, lines 94–116.

### addu (R)
- **Encoding**: `opcode=000000`, `funct=100001` (0x21). Same field layout as
  `add`.
- **Semantics**: `$rd = $rs + $rt` with plain Java `int` addition
  (two's-complement wraparound on overflow, no check). If `$rd == $zero`,
  write is discarded.
- **Errors/halts**: none from this instruction.
- **MARS note**: none — matches textbook MIPS (`addu` never traps).
- **Source**: `InstructionSet.java`, lines 163–177.

### sub (R)
- **Encoding**: `opcode=000000`, `funct=100010` (0x22). Fields:
  `rs=sssss`($t2/minuend), `rt=ttttt`($t3/subtrahend), `rd=fffff`($t1/dest).
- **Semantics**: `dif = $rs - $rt` (32-bit signed). If `$rd != $zero`, write
  `dif`.
- **Errors/halts**: overflow check: `(rs>=0 && rt<0 && dif<0) ||
  (rs<0 && rt>=0 && dif>=0)` → `ProcessingException("arithmetic overflow",
  ARITHMETIC_OVERFLOW_EXCEPTION)`; halts with no handler installed.
- **MARS note**: none — matches textbook MIPS (traps on signed overflow).
- **Source**: `InstructionSet.java`, lines 117–139.

### subu (R)
- **Encoding**: `opcode=000000`, `funct=100011` (0x23).
- **Semantics**: `$rd = $rs - $rt`, plain wraparound subtraction, no check.
- **Errors/halts**: none.
- **MARS note**: none — matches textbook MIPS.
- **Source**: `InstructionSet.java`, lines 178–192.

### and (R)
- **Encoding**: `opcode=000000`, `funct=100100` (0x24). `rs=sssss`($t2),
  `rt=ttttt`($t3), `rd=fffff`($t1).
- **Semantics**: `$rd = $rs & $rt`, bitwise, no overflow concept.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 448–462.

### or (R)
- **Encoding**: `opcode=000000`, `funct=100101` (0x25).
- **Semantics**: `$rd = $rs | $rt`.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 463–477.

### xor (R)
- **Encoding**: `opcode=000000`, `funct=100110` (0x26).
- **Semantics**: `$rd = $rs ^ $rt`.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 525–539.

### nor (R)
- **Encoding**: `opcode=000000`, `funct=100111` (0x27).
- **Semantics**: `$rd = ~($rs | $rt)` (bitwise NOR, full 32-bit complement).
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 510–524.

### sll (R)
- **Encoding**: `opcode=000000`, `funct=000000`. Fields:
  `000000 00000 sssss fffff ttttt 000000` → `rs=00000`(unused),
  `rt=sssss`($t2/src), `rd=fffff`($t1/dest), `shamt=ttttt`(5-bit immediate
  shift amount, 0–31).
- **Semantics**: `$rd = $rt << shamt` using Java `<<` on `int` (logical
  left shift, zero-fills low bits). No masking of `shamt` is performed in
  code, but the 5-bit field is architecturally limited to 0–31 so no
  >32 shift can be encoded.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 556–569.

### srl (R)
- **Encoding**: `opcode=000000`, `funct=000010` (0x02). Same layout as
  `sll`.
- **Semantics**: `$rd = $rt >>> shamt` — Java `>>>` is used explicitly
  (comment: "must zero-fill"), i.e. logical shift right, zero-fill.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 586–600.

### sra (R)
- **Encoding**: `opcode=000000`, `funct=000011` (0x03). Same layout as
  `sll`.
- **Semantics**: `$rd = $rt >> shamt` — Java `>>` is used explicitly
  (comment: "must sign-fill"), i.e. arithmetic shift right, sign-extend.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 601–614.

### slt (R)
- **Encoding**: `opcode=000000`, `funct=101010` (0x2a). `rs=sssss`($t2),
  `rt=ttttt`($t3), `rd=fffff`($t1).
- **Semantics**: `$rd = ($rs < $rt) ? 1 : 0`, using signed Java `int`
  comparison (`<`).
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 991–1007.

### sltu (R)
- **Encoding**: `opcode=000000`, `funct=101011` (0x2b). Same layout.
- **Semantics**: `$rd = ($rs <u $rt) ? 1 : 0`. Implemented via explicit
  sign-based case split rather than Java unsigned compare intrinsics: if
  both operands are non-negative or both negative, compare directly with
  `<`; otherwise the non-negative one is unsigned-smaller
  (`first >= 0 ? 1 : 0`). This is a correct hand-rolled unsigned-less-than
  on 32-bit two's-complement values.
- **Errors/halts**: none.
- **MARS note**: none — result is equivalent to a true unsigned compare.
- **Source**: `InstructionSet.java`, lines 1008–1030.

---

## Multiply / divide

### mult (R)
- **Encoding**: `opcode=000000`, `funct=011000` (0x18). Fields:
  `000000 fffff sssss 00000 00000 011000` → `rs=fffff`($t1/operand0),
  `rt=sssss`($t2/operand1); `rd`/`shamt` unused (always 0).
- **Semantics**: `product = (int64)$rs * (int64)$rt` computed as a signed
  64-bit Java `long` product of the two sign-extended 32-bit operands.
  `hi` (register 33) = high-order 32 bits of `product`; `lo` (register 34) =
  low-order 32 bits. No GPR is written.
- **Errors/halts**: none; MARS never traps on multiply overflow (there is no
  overflow concept — the full 64-bit result is always captured in hi:lo).
- **MARS note**: none — matches textbook MIPS (`mult` does not trap).
- **Source**: `InstructionSet.java`, lines 208–224.

### multu (R)
- **Encoding**: `opcode=000000`, `funct=011001` (0x19). Same layout.
- **Semantics**: both operands are zero-extended to 64 bits (`<<32>>>32` on
  the `long` cast) before multiplying; `hi:lo` = unsigned 64-bit product,
  split the same way as `mult`.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 225–240.

### div (R)
- **Encoding**: `opcode=000000`, `funct=011010` (0x1a). Fields:
  `000000 fffff sssss 00000 00000 011010` → `rs=fffff`($t1/dividend),
  `rt=sssss`($t2/divisor).
- **Semantics**: if `$rt != 0`: `hi (reg 33) = $rs % $rt` (signed Java `%`,
  remainder takes the sign of the dividend); `lo (reg 34) = $rs / $rt`
  (signed Java `/`, truncating toward zero). Both are ordinary 32-bit
  signed operations; no overflow check even for the `INT_MIN / -1` edge
  case (Java `int` division wraps `Integer.MIN_VALUE / -1` back to
  `Integer.MIN_VALUE`, matching two's-complement wraparound, and this is
  passed through silently).
- **Errors/halts**: **if `$rt == 0`, the method returns immediately without
  writing `hi` or `lo` at all** — they retain whatever value they held
  before the instruction executed. No exception is thrown.
- **MARS note**: **DEVIATION / explicit source comment.** The source
  contains an explicit comment at this exact spot: *"Note: no exceptions
  and undefined results for zero div. COD3 Appendix A says 'with overflow'
  but MIPS 32 instruction set specification says 'no arithmetic exception
  under any circumstances'."* MARS follows the MIPS32 spec reading here,
  not the Patterson & Hennessy (COD3) "divide with overflow" framing many
  textbooks use. A `Exceptions.DIVIDE_BY_ZERO_EXCEPTION` constant (value 15)
  exists in `vendor/mars-src/mars/simulator/Exceptions.java` (line 63) but
  is **never thrown** by `div`/`divu` — it is dead/vestigial code. Decision
  for the Lean spec: model `div`/`divu` by zero as **hi/lo unchanged, no
  halt**, matching this source exactly.
- **Source**: `InstructionSet.java`, lines 341–367 (zero-check and comment
  at lines ~352–358).

### divu (R)
- **Encoding**: `opcode=000000`, `funct=011011` (0x1b). Same layout as
  `div`.
- **Semantics**: operands are zero-extended to 64-bit `long` first
  (`<<32>>>32`); if divisor `!= 0`: `hi = (unsigned $rs) % (unsigned $rt)`,
  `lo = (unsigned $rs) / (unsigned $rt)`, each truncated back to 32 bits via
  `(int)(... << 32 >> 32)`.
- **Errors/halts**: same as `div` — if `$rt == 0`, returns with hi/lo
  unchanged, no exception.
- **MARS note**: same DEVIATION as `div` — no exception on zero divisor;
  see `div` entry above for the exact source comment.
- **Source**: `InstructionSet.java`, lines 368–391.

### mfhi (R)
- **Encoding**: `opcode=000000`, `funct=010000` (0x10). Fields:
  `000000 00000 00000 fffff 00000 010000` → `rd=fffff`($t1/dest); `rs`,
  `rt` fields unused (must be 0 for this exact match-mask).
- **Semantics**: `$rd = hi` (register 33). No flags, no PC effect beyond
  normal advance.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 392–405.

### mflo (R)
- **Encoding**: `opcode=000000`, `funct=010010` (0x12). Same layout as
  `mfhi` with `rd=fffff`.
- **Semantics**: `$rd = lo` (register 34).
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 406–419.

---

## I-type immediate arithmetic / logic

### addi (I)
- **Encoding**: `opcode=001000` (0x08). Fields:
  `001000 sssss fffff tttttttttttttttt` → `rs=sssss`($t2/src),
  `rt=fffff`($t1/dest), `imm=tttt...`(16-bit field, operand index 2).
- **Semantics**: `imm16 = (operand << 16) >> 16` — Java sign-extension
  of the low 16 bits to 32 bits. `sum = $rs + imm16` (signed 32-bit add).
  If `$rt != $zero`, write `sum`.
- **Errors/halts**: same overflow test as `add`
  (`(rs>=0 && imm16>=0 && sum<0) || (rs<0 && imm16<0 && sum>=0)`) →
  `ProcessingException("arithmetic overflow", ARITHMETIC_OVERFLOW_EXCEPTION)`.
- **MARS note**: none — matches textbook MIPS (`addi` traps on signed
  overflow).
- **Source**: `InstructionSet.java`, lines 140–162.

### addiu (I)
- **Encoding**: `opcode=001001` (0x09). Same field layout as `addi`.
- **Semantics**: `$rt = $rs + sext16(imm)`, plain wraparound, no check.
  (Despite the "u" suffix, the immediate **is** sign-extended — only the
  overflow-trap behavior differs from `addi`, exactly as in real MIPS.)
- **Errors/halts**: none.
- **MARS note**: none — matches textbook MIPS (`addiu` sign-extends the
  immediate but never traps; this is the standard, sometimes-surprising,
  real-hardware behavior, not a MARS-specific quirk).
- **Source**: `InstructionSet.java`, lines 193–207.

### andi (I)
- **Encoding**: `opcode=001100` (0x0c). Fields:
  `001100 sssss fffff tttttttttttttttt` → `rs=sssss`(src), `rt=fffff`(dest),
  `imm=tttt...`.
- **Semantics**: `$rt = $rs & (imm & 0x0000FFFF)` — immediate is
  **zero-extended** (masked with `0x0000FFFF`), not sign-extended; comment
  in source explicitly states this.
- **Errors/halts**: none.
- **MARS note**: none — matches textbook MIPS (`andi` zero-extends).
- **Source**: `InstructionSet.java`, lines 478–493.

### ori (I)
- **Encoding**: `opcode=001101` (0x0d). Same layout as `andi`.
- **Semantics**: `$rt = $rs | (imm & 0x0000FFFF)`, zero-extended immediate.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 494–509.

### xori (I)
- **Encoding**: `opcode=001110` (0x0e). Same layout as `andi`.
- **Semantics**: `$rt = $rs ^ (imm & 0x0000FFFF)`, zero-extended immediate.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 540–555.

### lui (I)
- **Encoding**: `opcode=001111` (0x0f). Fields:
  `001111 00000 fffff ssssssssssssssss` → `rs=00000`(unused, fixed 0),
  `rt=fffff`($t1/dest), `imm=ssss...`(operand index 1).
- **Semantics**: `$rt = imm << 16` (Java `int` left shift; low 16 bits of
  `$rt` become 0, high 16 bits become the 16-bit immediate). No sign
  extension of the immediate is applied before the shift (none is needed —
  shifting left by 16 discards any sign-extended high bits anyway).
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 845–857.

### slti (I)
- **Encoding**: `opcode=001010` (0x0a). Fields:
  `001010 sssss fffff tttttttttttttttt` → `rs=sssss`(src), `rt=fffff`(dest),
  `imm=tttt...`.
- **Semantics**: `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed comparison.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 1032–1049.

### sltiu (I)
- **Encoding**: `opcode=001011` (0x0b). Same layout as `slti`.
- **Semantics**: the 16-bit immediate is **sign-extended** first
  (`operands[2] << 16 >> 16`, explicit in source), *then* the comparison
  `$rs <u imm32` is performed unsigned (same hand-rolled case-split as
  `sltu`). This matches real MIPS: `sltiu`'s "u" affects only the
  comparison, not the immediate's extension.
- **Errors/halts**: none.
- **MARS note**: none — this is standard, if easily misremembered, real
  MIPS behavior (immediate sign-extended even for the "unsigned" compare),
  not a MARS-specific deviation.
- **Source**: `InstructionSet.java`, lines 1050–1073.

---

## Memory access

### lw (I)
- **Encoding**: `opcode=100011` (0x23). Fields:
  `100011 ttttt fffff ssssssssssssssss` → `base=ttttt`($t2, operand index
  2), `rt=fffff`($t1/dest, operand index 0), `offset=ssss...`(operand index
  1).
- **Semantics**: `addr = $base + offset`; `$rt = MEM32[addr]` (4 bytes,
  big-endian — see Global rule 4), full 32-bit word including sign.
- **Errors/halts**: `addr % 4 != 0` → `AddressErrorException` ("fetch
  address not aligned on word boundary", `ADDRESS_EXCEPTION_LOAD`),
  propagated as a halting `ProcessingException`.
- **MARS note**: **SOURCE AMBIGUITY, decision-relevant.** The `simulate()`
  body computes `addr` as `RegisterFile.getValue(operands[2]) + operands[1]`
  with **no explicit sign-extension** of `operands[1]`
  (contrast `lb`/`lh`/`lhu`/`lbu`/`sh`/`addi`/`slti` which all do
  `operands[1 or 2] << 16 >> 16` inline). For instructions built by the
  assembler from source text, `operands[1]` already carries the correctly
  signed Java `int` value of the offset token (see
  `ProgramStatement.buildBasicStatementFromBasicInstruction`,
  `vendor/mars-src/mars/ProgramStatement.java` lines ~245–300), so this is
  invisible in normal assembled-and-run programs. But for instructions
  constructed by decoding a raw 32-bit encoding
  (`ProgramStatement(int binaryStatement, int textAddress)`,
  `ProgramStatement.java` lines 102–146), **only the I_BRANCH_FORMAT's
  3rd operand is sign-extended at decode time** (line 132); a plain
  `I_FORMAT` offset field (as used by `lw`/`sw`) is left as a raw unsigned
  0–65535 value. Combined with `lw`'s lack of an inline sign-extend, a
  negative word offset decoded straight from a 32-bit encoding would be
  treated as a large positive offset by MARS's own source — unlike `lb`,
  `lh`, etc., which defensively re-extend inline and so get it right either
  way. **We could not resolve from source whether this is an intentional
  simplification (offsets are always non-negative in practice for `lw`/`sw`
  generated code) or a latent bug; the Lean `step` function must pick one
  behavior explicitly (uniform sign-extension for all I-format
  loads/stores, matching `lb`/`lh`, is recommended for consistency) rather
  than silently inheriting this asymmetry.**
- **Source**: `InstructionSet.java`, lines 648–668 (`simulate()` body at
  659–667); decode path `ProgramStatement.java` lines 102–146, especially
  126–136.

### sw (I)
- **Encoding**: `opcode=101011` (0x2b). Same field layout as `lw`, with
  `rt=fffff`($t1/source register to store, operand index 0).
- **Semantics**: `addr = $base + offset`; `MEM32[addr] = $rt` (4 bytes,
  big-endian).
- **Errors/halts**: `addr % 4 != 0` → `AddressErrorException` ("store
  address not aligned on word boundary", `ADDRESS_EXCEPTION_STORE`).
- **MARS note**: same SOURCE AMBIGUITY as `lw` — `operands[1]` (offset) is
  used raw with no inline sign-extension in `sw`'s `simulate()` body either.
  See `lw` entry for the full explanation; same decision is required for
  the Lean spec.
- **Source**: `InstructionSet.java`, lines 750–770 (`simulate()` body at
  758–768).

### lb (I)
- **Encoding**: `opcode=100000` (0x20). Fields:
  `100000 ttttt fffff ssssssssssssssss` → `base=ttttt`(operand 2),
  `rt=fffff`(dest, operand 0), `offset=ssss...`(operand 1).
- **Semantics**: `addr = $base + sext16(offset)` (explicit
  `operands[1] << 16 >> 16` inline); `byteVal = MEM8[addr]`;
  `$rt = sext8(byteVal)` (`<<24 >>24` to sign-extend the byte to 32 bits).
- **Errors/halts**: no alignment requirement for byte access; only
  out-of-range address throws `AddressErrorException`
  (`ADDRESS_EXCEPTION_LOAD`).
- **MARS note**: none — this instruction does sign-extend its offset
  inline, unlike `lw`/`sw` (see above).
- **Source**: `InstructionSet.java`, lines 1272–1296.

### lbu (I)
- **Encoding**: `opcode=100100` (0x24). Same layout as `lb`.
- **Semantics**: `addr = $base + sext16(offset)`; `$rt = zext8(MEM8[addr])`
  (masked with `& 0x000000ff`, no sign extension of the loaded byte).
- **Errors/halts**: none beyond out-of-range address.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 1347–1370.

### lh (I)
- **Encoding**: `opcode=100001` (0x21). Same field layout as `lb` (offset
  at operand 1, base at operand 2, dest at operand 0).
- **Semantics**: `addr = $base + sext16(offset)`; `halfVal = MEM16[addr]`
  (2 bytes, big-endian); `$rt = sext16(halfVal)` (`<<16 >>16`).
- **Errors/halts**: `addr % 2 != 0` → `AddressErrorException` ("...not
  aligned on halfword boundary", `ADDRESS_EXCEPTION_LOAD`).
- **MARS note**: none — sign-extends offset inline, consistent with `lb`.
- **Source**: `InstructionSet.java`, lines 1297–1321.

### lhu (I)
- **Encoding**: `opcode=100101` (0x25). Same layout as `lh`.
- **Semantics**: `addr = $base + sext16(offset)` (comment: "offset is
  sign-extended and loaded halfword value is zero-extended");
  `$rt = zext16(MEM16[addr])` (masked `& 0x0000ffff`).
- **Errors/halts**: `addr % 2 != 0` → `AddressErrorException`
  (`ADDRESS_EXCEPTION_LOAD`).
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 1322–1346.

### sh (I)
- **Encoding**: `opcode=101001` (0x29). Fields: `base` at operand 2, `rt`
  (source register) at operand 0, `offset` at operand 1.
- **Semantics**: `addr = $base + sext16(offset)`;
  `MEM16[addr] = $rt & 0x0000ffff` (low 16 bits of `$rt` stored,
  big-endian byte order).
- **Errors/halts**: `addr % 2 != 0` → `AddressErrorException` ("store
  address not aligned on halfword boundary", `ADDRESS_EXCEPTION_STORE`).
- **MARS note**: none — sign-extends offset inline, unlike `sw`.
- **Source**: `InstructionSet.java`, lines 1395–1416.

---

## Control flow

### j (J)
- **Encoding**: `opcode=000010` (0x02). Fields:
  `000010 ffffffffffffffffffffffffff` → `target=ffff...`(26-bit field,
  operand index 0; assembled from an absolute word address shifted right 2,
  per `ProgramStatement.java` line ~357).
- **Semantics**: schedules `PC = (PC_next & 0xF0000000) | (target << 2)`
  as the delay-slot transfer (Global rule 3) rather than applying it
  immediately; `j` itself falls through to `PC_next` so the delay-slot
  instruction executes first. `PC_next` is the PC *after* this
  instruction's fetch-increment (rule 1), so the top 4 bits of the jump
  target come from the region containing the instruction *after* `j`, not
  `j` itself (normal MIPS pseudo-direct jump semantics).
- **Errors/halts**: none directly; a bad target can later cause an
  instruction-fetch `AddressErrorException` on the next fetch; a branch/jump
  occupying `j`'s own delay slot halts with `HaltReason.branchInDelaySlot`
  (Global rule 3).
- **MARS note**: our semantics **overrides MARS's default**
  (`DelayedBranching=false`) and executes one delay-slot instruction before
  `PC` becomes the target, matching real MIPS hardware's architecturally
  mandated delay-slot semantics (Global rule 3) rather than MARS's
  immediate-jump default.
- **Source**: `InstructionSet.java`, lines 1200–1216;
  `processJump` at lines 3288–3298.

### jal (J)
- **Encoding**: `opcode=000011` (0x03). Same field layout as `j`.
- **Semantics**: `$ra ($31) = PC_next + 4` (i.e. `pc + 8`, the address
  *after* the delay slot — see Global rule 1/3, since the delay-slot
  instruction still executes before `jal` can return); then schedules
  `PC = (PC_next & 0xF0000000) | (target << 2)` as the delay-slot transfer,
  identical target computation to `j`. `jal` itself falls through to
  `PC_next` so the delay-slot instruction executes first.
- **Errors/halts**: none directly; a branch/jump occupying `jal`'s own
  delay slot halts with `HaltReason.branchInDelaySlot` (Global rule 3).
- **MARS note**: our semantics **overrides MARS's default**
  (`DelayedBranching=false`, under which `$ra = PC_next` with no delay slot
  executed) to match real MIPS32: one delay-slot instruction always
  executes, so `$ra` must be `PC_next + 4` rather than `PC_next` (Global
  rule 1/3).
- **Source**: `InstructionSet.java`, lines 1228–1244;
  `processReturnAddress` at lines 3309–3316.

### beq (I-branch)
- **Encoding**: `opcode=000100` (0x04). Fields:
  `000100 fffff sssss tttttttttttttttt` → `rs=fffff`($t1, operand 0),
  `rt=sssss`($t2, operand 1), `offset=tttt...`(operand 2, 16-bit signed
  word displacement).
- **Semantics**: if `$rs == $rt` (32-bit equality), schedules
  `PC = PC_next + (offset << 2)` as the delay-slot transfer (Global rule 3)
  — `beq` itself still falls through to `PC_next` so the delay-slot
  instruction executes first; otherwise PC stays at `PC_next` with no
  scheduled transfer (ordinary fallthrough).
- **Errors/halts**: none directly from the comparison; a bad target can
  cause a later fetch error; a branch/jump occupying `beq`'s own delay slot
  (only possible when `beq` is taken) halts with
  `HaltReason.branchInDelaySlot` (Global rule 3).
- **MARS note**: our semantics **overrides MARS's default**
  (`DelayedBranching=false`) and executes one delay-slot instruction before
  the target takes effect, matching real MIPS hardware (Global rule 3)
  rather than MARS's immediate-branch default.
- **Source**: `InstructionSet.java`, lines 858–875;
  `processBranch` at lines 3265–3281.

### bne (I-branch)
- **Encoding**: `opcode=000101` (0x05). Same layout as `beq`.
- **Semantics**: if `$rs != $rt`, schedules `PC = PC_next + (offset << 2)`
  as the delay-slot transfer, same as `beq` (Global rule 3).
- **Errors/halts**: none directly; same delay-slot halt condition as `beq`.
- **MARS note**: same real-MIPS32 delay-slot override as `beq` (Global
  rule 3).
- **Source**: `InstructionSet.java`, lines 876–891.

### blez (I-branch)
- **Encoding**: `opcode=000110` (0x06). Fields:
  `000110 fffff 00000 ssssssssssssssss` → `rs=fffff`($t1, operand 0),
  `rt=00000`(fixed/unused), `offset=ssss...`(operand 1).
- **Semantics**: if `$rs <= 0` (signed comparison, includes zero),
  schedules `PC = PC_next + (offset << 2)` as the delay-slot transfer, same
  as `beq` (Global rule 3).
- **Errors/halts**: none directly; same delay-slot halt condition as `beq`.
- **MARS note**: same real-MIPS32 delay-slot override as `beq` (Global
  rule 3).
- **Source**: `InstructionSet.java`, lines 942–958.

### bgtz (I-branch)
- **Encoding**: `opcode=000111` (0x07). Same layout as `blez`.
- **Semantics**: if `$rs > 0` (signed, strictly positive), schedules
  `PC = PC_next + (offset << 2)` as the delay-slot transfer, same as `beq`
  (Global rule 3).
- **Errors/halts**: none directly; same delay-slot halt condition as `beq`.
- **MARS note**: same real-MIPS32 delay-slot override as `beq` (Global
  rule 3).
- **Source**: `InstructionSet.java`, lines 926–941.

---

## Register-indirect jump/call (real MIPS32 ISA)

`jr` and `jalr` are real MIPS32 instructions that were missing from the
original v1 subset -- per `docs/spec/MIPS-COVERAGE-GAPS.md` §3.1, this was
the single highest-priority gap, since without `jr` no compiled MIPS
function can return (`jr $ra`) and without `jalr` no function pointer /
dynamic-dispatch call can be made. Per this addition's house rule (same as
the "MIPS32 / MIPS32r2 additions" and "Coprocessor 0" sections below), their
semantics are grounded directly in the **standard MIPS32 architecture** --
"MIPS32 Architecture For Programmers, Volume II-A: The MIPS32 Instruction
Set" (MD00086, Rev 2.50, §3.2, Table 3-2, pp. 150/155/25) -- not against
the vendored MARS source; MARS is this project's differential-testing
oracle, not the spec source. Like every other branch/jump in this document,
both get exactly one architectural delay slot (Global rule 3): `pendingBranch`
schedules the register-read target, falling through to the delay-slot
instruction first, exactly like `j`/`jal`.

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `jr` | R | `PC = $rs` |
| `jalr` | R | `$rd = PC_next + 4; PC = $rs` |

### jr (R)
- **Encoding**: `opcode=000000` (SPECIAL), `funct=001000` (0x08). Fields:
  `000000 sssss 00000 00000 00000 001000` → `rs=sssss` (the only field
  that carries information); `rt`/`rd`/`shamt` are `0` in the real encoding
  and are not modeled as separate `Instruction` fields (see
  `Instruction.lean`'s `.jr` docstring).
- **Semantics**: Jump Register. Schedules `PC = $rs` -- the full raw 32-bit
  register value, *not* a 26-bit target field composed with `PC_next`'s top
  4 bits like `j` -- as the delay-slot transfer (Global rule 3); `jr`
  itself falls through to `PC_next` so the delay-slot instruction executes
  first. The canonical real-MIPS32 function-return idiom is `jr $ra`
  (return to the address `jal`/`jalr` linked into `$ra`); it is also used
  for compiled switch-statement jump tables and other computed branches.
- **Errors/halts**: none directly from `jr` itself. If `$rs` holds a value
  that is not 4-byte-aligned, this is **not** special-cased at the point
  `jr` schedules it: the misalignment surfaces as the ordinary
  `HaltReason.addressError` the *next* time `step` tries to fetch an
  instruction at that address (`fetchWord`'s existing alignment check),
  identical to any other misaligned `PC` (Global rule 5). A branch/jump
  occupying `jr`'s own delay slot halts with `HaltReason.branchInDelaySlot`
  (Global rule 3).
- **ISA note**: standard MIPS32 instruction (MIPS I onward); not MARS-
  sourced (see this section's header note). MARS itself does implement
  `jr`, but with its own default `DelayedBranching=false` no-delay-slot
  timing -- this spec instead gives it the real-MIPS32 one-delay-slot
  semantics, the same override every other branch/jump in this document
  already receives (Global rule 3).
- **Source**: MD00086 Rev 2.50, §3.2, Table 3-2, p. 25 and p. 155 ("JR"
  instruction page).

### jalr (R)
- **Encoding**: `opcode=000000` (SPECIAL), `funct=001001` (0x09). Fields:
  `000000 sssss 00000 ddddd 00000 001001` → `rs=sssss` (jump target
  source), `rd=ddddd` (link destination); `rt`/`shamt` are `0` in the real
  encoding and are not modeled as separate `Instruction` fields (see
  `Instruction.lean`'s `.jalr` docstring). Real MIPS32 assembly syntax also
  allows the one-operand form `jalr $rs` as sugar for `jalr $ra, $rs`
  (`rd` defaults to `31`); the assembler (`Asm.lean`) supports this sugar.
- **Semantics**: Jump and Link Register. `$rd = PC_next + 4` (i.e.
  `pc + 8`, the address *after* the delay slot -- same link-value
  convention as `jal`, Global rule 1/3, since the delay-slot instruction
  still executes before control can return to `$rd`); then schedules
  `PC = $rs` (the raw register value, same target computation as `jr`) as
  the delay-slot transfer. `jalr` itself falls through to `PC_next` so the
  delay-slot instruction executes first. If `rd == rs`, the jump target is
  read from `$rs` *before* `$rd` is overwritten with the link value, so
  `jalr $t9, $t9` still jumps to the original `$t9` value. Used for
  indirect procedure calls, dynamic linking stubs, and calls through a
  function pointer (the common real-MIPS32 ABI idiom `jalr $t9`).
- **Errors/halts**: same misaligned-`$rs`-target and delay-slot-in-delay-
  slot conditions as `jr` above.
- **ISA note**: standard MIPS32 instruction (MIPS I onward); not MARS-
  sourced (see this section's header note), same real-MIPS32 one-delay-slot
  override as `jr`/`j`/`jal` (Global rule 3).
- **Source**: MD00086 Rev 2.50, §3.2, Table 3-2, p. 25 and p. 150 ("JALR"
  instruction page).

---

## MIPS32 / MIPS32r2 additions (beyond the MARS-matched v1 baseline)

The six instructions in this section (`movn`, `movz`, `clo`, `clz`, `seb`,
`seh`) are real MIPS32/MIPS32r2 instructions that were out of the original
v1 subset. Per this addition's house rule, their semantics are grounded
directly in the **standard MIPS32 architecture** (as specified in the MIPS32
Architecture Reference Manual, Volume II-A, the "CLO"/"CLZ"/"MOVN"/"MOVZ"/
"SEB"/"SEH" instruction pages), not against the vendored MARS source —
MARS is this project's differential-testing oracle, not the spec source,
and (unlike every v1 instruction above) these encodings/semantics are
pinned from the ISA directly rather than derived from `InstructionSet.java`
line citations.

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `movn` | R | `if ($rt != 0) $rd = $rs` (else `$rd` unchanged) |
| `movz` | R | `if ($rt == 0) $rd = $rs` (else `$rd` unchanged) |
| `clo` | R (SPECIAL2) | `$rd = count of leading one bits in $rs` (32 if all-ones) |
| `clz` | R (SPECIAL2) | `$rd = count of leading zero bits in $rs` (32 if all-zero) |
| `seb` | R (SPECIAL3/BSHFL) | `$rd = sext8($rt[7:0])` |
| `seh` | R (SPECIAL3/BSHFL) | `$rd = sext16($rt[15:0])` |

### movn (R)
- **Encoding**: `opcode=000000` (SPECIAL), `funct=001011` (0x0b). Same
  `rs, rt, rd` field layout as `add`/`slt`/etc.
- **Semantics**: Move Conditional on Not Zero. If `$rt != 0`, `$rd = $rs`.
  **If `$rt == 0`, `$rd` is left completely unchanged** — this is a true
  conditional no-op on the destination register, not "write zero"; a
  common implementation mistake this spec deliberately avoids (see
  `Step.lean`'s `movn`/`movz` test cases, which pre-seed `$rd` with a
  sentinel value to catch exactly this bug).
- **Errors/halts**: none; no overflow concept.
- **ISA note**: standard MIPS32r2 instruction, present from MIPS32 Release 1
  onward alongside `movz`; commonly used to implement branch-free
  conditional-move idioms (e.g. `a = cond ? b : a`).

### movz (R)
- **Encoding**: `opcode=000000` (SPECIAL), `funct=001010` (0x0a). Same
  layout as `movn`.
- **Semantics**: Move Conditional on Zero. If `$rt == 0`, `$rd = $rs`;
  otherwise `$rd` is left unchanged (same "true no-op", not "write zero",
  caveat as `movn`).
- **Errors/halts**: none.
- **ISA note**: standard MIPS32r2 instruction.

### clo (R, SPECIAL2)
- **Encoding**: `opcode=011100` (0x1c, SPECIAL2), `funct=100001` (0x21).
  Fields: `011100 sssss ddddd ddddd 00000 100001` → `rs=sssss` (source),
  `rd=ddddd` (destination). **Encoding quirk**: the raw `rt` field
  (bits 20..16) is required by the ISA to carry the *same* register number
  as `rd` (both field positions are written with the destination register
  when assembling); hardware does not read `rt` for `clo`. This `Instruction`
  constructor therefore stores only `(rs, rd)` — see `Instruction.lean`'s
  `.clo` docstring — and `decode` ignores the raw `rt` field rather than
  validating or surfacing it, matching real hardware behavior.
- **Semantics**: Count Leading Ones. `$rd` = the number of consecutive `1`
  bits starting from the most-significant bit (bit 31) of `$rs`, stopping at
  the first `0` bit. If `$rs` is all-ones (`0xFFFFFFFF`), the result is `32`.
- **Errors/halts**: none; no overflow concept.
- **ISA note**: standard MIPS32 instruction (present since MIPS32 Release 1).

### clz (R, SPECIAL2)
- **Encoding**: `opcode=011100` (0x1c, SPECIAL2), `funct=100000` (0x20).
  Same field layout and `rt`-duplicates-`rd` quirk as `clo`.
- **Semantics**: Count Leading Zeros. `$rd` = the number of consecutive `0`
  bits starting from bit 31 of `$rs`, stopping at the first `1` bit. If
  `$rs` is all-zero, the result is `32`.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction.

### seb (R, SPECIAL3/BSHFL)
- **Encoding**: `opcode=011111` (0x1f, SPECIAL3), `funct=100000` (0x20,
  the shared BSHFL sub-opcode family). Fields: `011111 00000 ttttt ddddd
  10000 100000` → `rs=00000` (unused/fixed 0), `rt=ttttt` (source),
  `rd=ddddd` (destination), and the 5-bit shamt-position sub-field fixed to
  `10000` (0x10) to select SEB specifically out of the BSHFL family (which
  also includes `wsbh`, `seh`, and others not in this scope — any other
  sub-field value under funct 0x20 decodes to `none` here).
- **Semantics**: Sign-Extend Byte. `$rd` = the low byte of `$rt`
  (`$rt[7:0]`), sign-extended to 32 bits.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32r2 instruction.

### seh (R, SPECIAL3/BSHFL)
- **Encoding**: `opcode=011111` (0x1f, SPECIAL3), `funct=100000` (0x20).
  Same layout as `seb`, but the sub-field is `11000` (0x18).
- **Semantics**: Sign-Extend Halfword. `$rd` = the low halfword of `$rt`
  (`$rt[15:0]`), sign-extended to 32 bits.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32r2 instruction.

---

## Syscalls (v1 scope: 1, 4, 10, 11)

Dispatch source: `InstructionSet.java` `findAndSimulateSyscall`
(lines 3237–3246), invoked from the `syscall` basic instruction's
`simulate()` with `RegisterFile.getValue(2)` (i.e. `$v0`) as the service
number (see the `"syscall"` instruction entry around line 1195). Argument
convention: `$v0` = service number, `$a0` = register 4 (first argument).

### syscall 1 — PrintInt
- **Encoding**: not a machine opcode; selected via `$v0 = 1` then the
  `syscall` instruction (`opcode=000000`, `funct=001100`).
- **Semantics**: reads `$a0` (register 4) as a signed 32-bit int, converts
  with `Integer.toString` (decimal, signed), writes to the console via
  `SystemIO.printString` to `System.out.print` (`SyscallPrintInt.java:53`).
  **No trailing newline is appended** -- confirmed both by the source
  (`print`, not `println`) and empirically (a program printing 42 then 99
  produces exactly `"4299"`, concatenated with no separator). No registers
  or memory are modified by the syscall itself.
- **Errors/halts**: none specific; a missing/invalid service number more
  generally throws `ProcessingException(..., SYSCALL_EXCEPTION)` from
  `findAndSimulateSyscall`, but service 1 is always registered in v1 scope.
- **MARS note**: none.
- **Source**: `vendor/mars-src/mars/mips/instructions/syscalls/SyscallPrintInt.java`,
  class `SyscallPrintInt`, constructor registers service number 1
  (`super(1, "PrintInt")`), `simulate()` method (entire ~15-line file).

### syscall 4 — PrintString
- **Encoding**: not a machine opcode; selected via `$v0 = 4` then the `syscall`
  instruction (`opcode=000000`, `funct=001100`).
- **Semantics**: reads `$a0` (register 4) as a byte address; repeatedly
  calls `Globals.memory.getByte(addr)`, printing each byte as a `char` via
  `SystemIO.printString`, incrementing `addr` by 1 each iteration, **until
  a `0x00` byte is read** (null-terminated C-style string; the loop
  condition is literally `while (ch != 0)`). The terminating null byte
  itself is not printed.
- **Errors/halts**: any `AddressErrorException` while scanning (e.g.
  running off the end of mapped memory, or an unmapped byte) is rethrown as
  a `ProcessingException`, halting the program (no alignment requirement
  for byte reads, so this is only an out-of-range condition). If the string
  is never null-terminated within valid memory, this is effectively an
  infinite scan until such an error occurs.
- **MARS note**: none beyond the above — straightforward byte-at-a-time
  scan, no bulk/word-level read optimization.
- **Source**: `vendor/mars-src/mars/mips/instructions/syscalls/SyscallPrintString.java`,
  class `SyscallPrintString`, constructor registers service number 4,
  `simulate()` method (entire file, ~20 lines of logic).

### syscall 10 — Exit
- **Encoding**: not a machine opcode; selected via `$v0 = 10` then the
  `syscall` instruction (`opcode=000000`, `funct=001100`).
- **Semantics**: unconditionally throws `new ProcessingException()` — the
  **zero-argument constructor**, which sets `errs = null`
  (`vendor/mars-src/mars/ProcessingException.java` lines 117–120, with the
  doc comment "No parameter and thus no error list. Use this for normal
  MIPS program termination"). No registers, memory, or `$a0` are
  inspected or modified — this syscall ignores any argument registers.
- **Errors/halts**: this *is* the halt signal. The dispatcher in
  `Simulator.java` special-cases `pe.errors() == null` (line 353) to set
  `constructReturnReason = NORMAL_TERMINATION` and stop cleanly — distinct
  from the `EXCEPTION` return reason used for all error conditions
  elsewhere in this document.
- **MARS note**: **behaviorally notable, not a deviation** — exit code /
  status value is not modeled by this syscall at all (contrast MARS's
  `syscall 17`, `Exit2`, which does read an exit code from `$a0`; that
  syscall is out of v1 scope). For the Lean spec, "exit" should be modeled
  as a halt transition with no observable register/memory side effect.
- **Source**: `vendor/mars-src/mars/mips/instructions/syscalls/SyscallExit.java`
  (entire file, ~12 lines of logic); halt dispatch in
  `vendor/mars-src/mars/simulator/Simulator.java`, lines 352–358;
  `ProcessingException()` zero-arg constructor in
  `vendor/mars-src/mars/ProcessingException.java`, lines 117–120.

### syscall 11 — PrintChar
- **Encoding**: not a machine opcode; selected via `$v0 = 11` then the
  `syscall` instruction (`opcode=000000`, `funct=001100`).
- **Semantics**: reads `$a0` (register 4), masks to the low byte
  (`& 0x000000ff`), casts to Java `char`, prints via
  `SystemIO.printString(Character.toString(t))`. Only one byte/character is
  ever printed per call; the upper 24 bits of `$a0` are ignored.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `vendor/mars-src/mars/mips/instructions/syscalls/SyscallPrintChar.java`
  (entire file, ~15 lines of logic).

---

## Coprocessor 0 / traps and exceptions (real MIPS32 ISA)

Everything above this section is grounded in the vendored MARS 4.5 source
(`vendor/mars-src/`), per the module header. This section is different: it
documents a small, deliberately minimal **addition** on top of the v1 set —
`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu` (trap-on-condition) and `break`
(unconditional trap), plus the coprocessor-0 state and exception-vector
mechanism they use. Per this track's process requirements, these are
ground-truthed against the **real MIPS32 architecture** (the actual ISA, as
commonly documented in "MIPS32 Architecture For Programmers, Volume II-A:
The MIPS32 Instruction Set" and "Volume III: The MIPS32 Privileged Resource
Architecture" / System Control Coprocessor), not against MARS, which was
only ever meant as a differential-testing oracle for this project and does
not model exceptions realistically (MARS's own exception handling is a
Java-exception-based simulation shortcut, not a model of real CP0 register
state). No internet access was available while writing this section; every
encoding/field value below is the standard, commonly documented MIPS32
value, called out explicitly rather than silently guessed. If any value
here is later found to disagree with the written ISA spec, this paragraph
is the place to correct it.

### Coprocessor 0 state modeled (and what is deliberately out of scope)

This is a **minimal** CP0 model: three registers, not the full coprocessor.

| Field (on `State`) | Real MIPS32 register | Modeled behavior |
|---|---|---|
| `cp0Status` | `Status` (CP0 register 12) | Only bit 1 (`EXL`, exception level) is ever set, on any exception; no other bit (`IE`, `ERL`, `KSU`, `UM`, `BEV`, `IM7..IM0`, ...) is modeled. Initialized to `0`. |
| `cp0Cause` | `Cause` (CP0 register 13) | Only the `ExcCode` field (bits 6..2) is ever written, as `excCode <<< 2`; no other field (`BD`, `CE`, `IV`, `WP`, the `IP` pending-interrupt bits, ...) is modeled. Initialized to `0`. |
| `cp0Epc` | `EPC` (CP0 register 14) | Set to the trapping instruction's own address (`pc` at the time of the trap/`break`, *not* `pc + 4`) on every exception. Initialized to `0`. |

**Explicitly out of scope** (documented here rather than silently omitted,
per this track's process requirements): every other CP0 register (`Index`,
`Random`, `EntryLo0/1`, `Context`, `PageMask`, `Wired`, `BadVAddr`, `Count`,
`EntryHi`, `Compare`, `Config0-7`, `PRId`, `EBase`, ...), the full `Status`/
`Cause` bitfields beyond `EXL`/`ExcCode`, interrupts (hardware or software),
TLB/MMU behavior, `eret` (there is no way to leave exception level once
entered — `EXL` is set and never cleared), and any notion of kernel/user
mode. This model answers exactly one question: "did a trap/`break` fire,
and where did control transfer to" — nothing more.

### Exception mechanism (shared by all seven new instructions)

On any trap condition being met, or on executing `break` (always): this is
a **real state transition**, not a `HaltReason` — `step` returns
`StepResult.next`, matching real MIPS32 hardware's exception-taken behavior
(control transfers to the handler; the machine keeps running). Concretely,
from the trapping/`break` instruction's state `s`:

1. `cp0Epc := s.pc` — the address of the trapping instruction *itself*.
   Real MIPS32 hardware would instead write `PC - 4` if the faulting
   instruction were in a branch delay slot (and set `Cause.BD`); this v1
   dialect has no delay slots at all (`SPEC-NOTES.md` §3/§9.1), so that
   case cannot arise and `EPC = s.pc` unconditionally is exactly correct.
2. `cp0Cause := excCode <<< 2` — `excCode` packed into the `ExcCode` field
   position (bits 6..2 of the real `Cause` register). Two `excCode` values
   are used, one per exception type as required: `excCodeBp = 9` ("Bp" —
   Breakpoint, for `break`) and `excCodeTr = 13` ("Tr" — Trap, for all six
   `t*` instructions). Both are the standard MIPS32 `Cause.ExcCode` encoding
   values for these exception classes. Note real MIPS32 hardware does
   *not* distinguish *which* of the six trap conditions fired in `Cause` —
   a handler would have to re-decode the instruction word at `EPC` for
   that, which this model does not need since it has no handler.
3. `cp0Status := s.cp0Status ||| statusExlMask` — bit 1 (`EXL`) set,
   preserving (OR-ing into) whatever was already there, matching real
   hardware's behavior of never clearing unrelated `Status` bits on
   exception entry.
4. `pc := exceptionVectorAddr`, defined as `0x80000180` — the MIPS32
   **general exception vector** (used whenever `Status.BEV = 0`, i.e. the
   normal non-bootstrap case, for every exception other than TLB-refill/
   XTLB-refill/cache-error, none of which this model has any notion of).
   This same address is already referenced informally in Global rule 5
   above ("no exception handler installed at `0x80000180`"); this track
   promotes it to a named, documented constant (`Types.lean`) shared by
   every exception site instead of a repeated literal.

Deliberately **not** added: a synthetic "unhandled exception"/"no handler
installed" `HaltReason`. Since this v1 dialect never installs anything at
`exceptionVectorAddr`, the very next `step` call after a trap/`break`
naturally re-enters the existing fetch path at that address and hits one of
`step`'s pre-existing, already-documented halts: `addressError` (no
instruction recorded there — the expected case for every test program that
doesn't deliberately install a handler) or `illegalInstruction` (if some
word happens to be recorded there but doesn't decode). This gives real
exception-vector semantics for free, without inventing a new halt variant —
and conversely, if a test program *does* install a real handler at
`exceptionVectorAddr`, that handler executes completely normally, since it
is just ordinary code at an ordinary (if high) address.

### teq / tne / tlt / tge / tltu / tgeu (R, trap-on-condition)

- **Encoding**: `opcode=000000`. Fields: `000000 sssss ttttt ----- ----- ffffff`
  → `rs=sssss`, `rt=ttttt`; `rd`/`shamt` unused (always 0), same shape as
  `mult`/`div`. `funct` per mnemonic, the standard MIPS32 SPECIAL-opcode trap
  family: `teq` = `0x34`, `tne` = `0x36`, `tlt` = `0x32`, `tge` = `0x30`,
  `tltu` = `0x33`, `tgeu` = `0x31`. (Funct `0x35`, between `teq` and `tne`,
  is reserved/unused in the real ISA — no mnemonic maps to it.) These are
  the standard MIPS32 values as commonly documented; cited here per this
  track's requirement to state the source plainly rather than guess
  silently.
- **Semantics**: evaluate the named condition on `$rs`/`$rt` — `teq`:
  `$rs == $rt`; `tne`: `$rs != $rt`; `tlt`: `$rs <s $rt` (signed); `tge`:
  `$rs >=s $rt` (signed); `tltu`: `$rs <u $rt` (unsigned); `tgeu`:
  `$rs >=u $rt` (unsigned). If the condition holds, take the exception
  described above with `excCode = excCodeTr`. If the condition does not
  hold, the instruction is a complete no-op other than the ordinary
  fall-through to `pc + 4` — no CP0 state is touched at all.
- **Errors/halts**: none beyond the exception transition itself (which is
  `StepResult.next`, not a halt).
- **MARS note**: not applicable — not part of the MARS-grounded v1 set;
  MARS does implement this family in its own `InstructionSet.java`, but per
  this track's process requirements the ground truth cited here is the real
  MIPS32 ISA, not MARS's implementation of it.

### break (R, unconditional trap)

- **Encoding**: `opcode=000000`, `funct=001101` (0x0d) — the funct value
  immediately after `syscall`'s `0x0c`. Fields: all zero in this model
  (`000000 00000 00000 00000 00000 001101`). Real MIPS32 `break` has an
  optional 20-bit "code" field packed into bits 25..6, purely a
  software-visible hint (e.g. distinguishing different breakpoint call
  sites) with no architecturally-defined effect on the exception itself —
  deliberately out of scope here, so `break`'s only field-level difference
  from `syscall` is its `funct` value.
- **Semantics**: unconditionally takes the exception described above, with
  `excCode = excCodeBp`.
- **Errors/halts**: none beyond the exception transition itself.
- **MARS note**: not applicable, as for the trap family above.

## Flagged MARS deviations (summary)

1. **`div`/`divu` by zero**: no exception, `hi`/`lo` left unchanged
   (explicit source comment citing the MIPS32 spec over the COD3 textbook
   framing). `Exceptions.DIVIDE_BY_ZERO_EXCEPTION` exists but is dead code.
2. **Branch delay slots** (`j`, `jal`, `beq`, `bne`, `blez`, `bgtz`):
   MARS's `DelayedBranching` setting defaults to `false`, so by default PC
   jumps to the target immediately with no delay-slot instruction executed.
   Our semantics does **not** follow that default: it implements real
   MIPS32's architecturally-mandated one-instruction delay slot instead
   (Global rule 3; SPEC-NOTES \u00a79 item 1) \u2014 the one case in this reference
   where we deliberately diverge from MARS's default configuration rather
   than documenting it as a quirk to match.
3. **`lw`/`sw` offset sign-extension asymmetry** (flagged as a source
   ambiguity requiring a Lean-spec decision, not a confirmed intentional
   deviation): unlike `lb`/`lh`/`lhu`/`lbu`/`sh`/`addi`/`addiu`/`slti`/
   `sltiu`, which all inline `operands[n] << 16 >> 16` to sign-extend their
   immediate/offset field defensively, `lw` and `sw`'s `simulate()` bodies
   use the raw operand value with no inline sign-extension. This is
   invisible for assembler-produced programs (the operand is already a
   correctly-signed Java `int` by the time `simulate()` runs) but would
   zero-extend instead of sign-extend a negative offset for an instruction
   constructed directly from a raw 32-bit encoding (self-modifying code /
   direct binary loading), since `ProgramStatement`'s binary-decode
   constructor only sign-extends the branch-displacement operand, not
   generic I-format offsets.

Everything else checked (`add`/`addi`/`sub` overflow trapping, `addu`/
`subu`/`mult`/`multu` never trapping, `andi`/`ori`/`xori` zero-extending,
`sltiu` sign-extending its immediate, `$zero` write-ignore, big-endian
memory) matches textbook/ISA-spec MIPS behavior and is marked "none" above.

---

## Floating point (coprocessor 1, single precision) — v1.x addition

This section documents a v1.x addition: a minimal real-MIPS32 coprocessor-1
(FPU) instruction subset, added on top of the v1 scope documented above.
**Grounding note**: unlike every section above (grounded in the vendored
MARS 4.5 source), this section's semantics are grounded directly in the
**real MIPS32 architecture** — specifically the standard MIPS32 ISA's
"COP1"/FPU encoding (opcode `0x11`, the `fmt`/`ft`/`fs`/`fd`/`funct` field
layout, and the standard `funct` assignments for `ADD.fmt`/`SUB.fmt`/
`MUL.fmt`/`DIV.fmt`/`MOV.fmt`/`CVT.S.fmt`/`CVT.W.fmt`/`C.cond.fmt`/`BC1`), not
MARS-specific behavior, per this track's explicit brief. MARS is not
consulted as ground truth for this section.

### Scope

- **Single precision only.** All 32 FP registers `$f0`..`$f31` are modeled as
  independent 32-bit registers holding a raw IEEE-754 binary32 bit pattern
  (`State.fpRegs`). **Double precision (`.d`) is out of scope for this pass**
  — real MIPS32 pairs adjacent `$f` registers for 64-bit doubles, which this
  v1.x addition does not model at all. This is flagged as a documented
  follow-up, not a silent gap.
- **One FP condition flag, not eight.** Real MIPS32 has 8 FP condition-code
  registers (the 3-bit `cc` field in compare/branch encodings). This addition
  models only `cc = 0`, as a single `State.fpCondFlag : Bool`. Any encoding
  with a nonzero `cc` (or nonzero `nd`/"likely" bit on `BC1`) is treated as
  undecodable (`decode` returns `none`), not silently misinterpreted.
- **No FP traps/exceptions.** Divide-by-zero and invalid operations (e.g.
  `0.0 / 0.0`) are never trapped; IEEE-754 ±Infinity/NaN propagate naturally
  through register writes, matching this project's existing precedent for
  integer `div`/`divu` by zero (see "Flagged MARS deviations" item 1 above).
- **No delay slot for `bc1t`/`bc1f`.** Real MIPS32 hardware has an
  architecturally-mandated branch delay slot for every branch, including
  `bc1t`/`bc1f`. This v1.x addition does **not** model one: `bc1t`/`bc1f`
  jump immediately, matching this codebase's existing no-delay-slot
  convention for `beq`/`bne`/`blez`/`bgtz`/`j`/`jal` (see "Flagged MARS
  deviations" item 2 above — that deviation was MARS's `DelayedBranching`
  default, but the resulting *simulator* behavior is the same shape this
  addition reuses for consistency). Flagged for integration: a parallel
  track is adding real delay-slot semantics (`State.pendingBranch`) for the
  existing branches; `bc1t`/`bc1f` were deliberately left out of that scheme
  to avoid touching the shared `step` dispatch loop, and should be
  reconciled with that track by the orchestrator if delay slots are adopted
  project-wide.
- **Only `CVT.S.W`/`CVT.W.S`** of the `CVT.*` family are implemented (the
  other source/destination format combinations — `.L`, `.D` — are out of
  scope, since they all involve either double precision or 64-bit integers).
  `cvt.w.s` always truncates toward zero; real MIPS32 instead rounds
  according to the current FCSR rounding mode (default: round-to-nearest,
  ties-to-even), since there is no `FCSR` in this project's scope. This is a
  deliberate, documented simplification, not an oversight.
- **Only `ADD.S`/`SUB.S`/`MUL.S`/`DIV.S`/`MOV.S`** of the arithmetic-format
  instructions are implemented; `SQRT.S`, `ABS.S`, `NEG.S`, and the
  `ROUND`/`TRUNC`/`CEIL`/`FLOOR` family are out of scope for this pass.
- **Only `C.EQ.S`/`C.LT.S`/`C.LE.S`** of the sixteen `C.cond.S` compares are
  implemented (the three most common; the rest — `C.UN.S`, `C.OLE.S`, etc. —
  are out of scope).

### Register/state model

- `State.fpRegs : Array W32`, size 32 — `$f0`..`$f31`, each a raw 32-bit
  IEEE-754 binary32 bit pattern (same raw-bit-pattern storage convention as
  the integer `regs` array; conversion to/from Lean's `Float32` happens only
  at the point of doing arithmetic, in `Step.lean`, via `Float32.ofBits`/
  `Float32.toBits`, Lean core's exact IEEE-754 bit-pattern round-trip).
  Initialized to all-zero (`initialState`). Unlike the integer registers,
  **no FP register is hardwired to zero** — `$f0` is an ordinary read/write
  register in real MIPS32, and `writeFpReg` never ignores a write.
- `State.fpCondFlag : Bool` — the single modeled FP condition flag (`cc = 0`
  only; see Scope above). Initialized to `false`.

### Encoding summary

| Mnemonic | Encoding | One-line semantics |
|---|---|---|
| `mtc1 $rt, $fs` | opcode 0x11, fmt=`MT`=0x04 | `$fs = rawbits($rt)`, no conversion |
| `mfc1 $rt, $fs` | opcode 0x11, fmt=`MF`=0x00 | `$rt = rawbits($fs)`, no conversion |
| `lwc1 $ft, off($rs)` | opcode 0x31 | `$ft = MEM32[$rs + off]`, raw bits |
| `swc1 $ft, off($rs)` | opcode 0x39 | `MEM32[$rs + off] = rawbits($ft)` |
| `add.s $fd, $fs, $ft` | opcode 0x11, fmt=`S`=0x10, funct=0x00 | `$fd = $fs + $ft` (IEEE-754) |
| `sub.s $fd, $fs, $ft` | fmt=S, funct=0x01 | `$fd = $fs - $ft` |
| `mul.s $fd, $fs, $ft` | fmt=S, funct=0x02 | `$fd = $fs * $ft` |
| `div.s $fd, $fs, $ft` | fmt=S, funct=0x03 | `$fd = $fs / $ft`; `$ft=0` → ±Inf/NaN, no trap |
| `mov.s $fd, $fs` | fmt=S, funct=0x06 | `$fd = $fs`, raw copy |
| `cvt.s.w $fd, $fs` | fmt=`W`=0x14, funct=0x20 | `$fd = float32(int32bits($fs))` |
| `cvt.w.s $fd, $fs` | fmt=S, funct=0x24 | `$fd = int32bits(trunc($fs))` |
| `c.eq.s $fs, $ft` | fmt=S, funct=0x32, cc=0 | `fpCondFlag := ($fs == $ft)` |
| `c.lt.s $fs, $ft` | fmt=S, funct=0x3c, cc=0 | `fpCondFlag := ($fs < $ft)` |
| `c.le.s $fs, $ft` | fmt=S, funct=0x3e, cc=0 | `fpCondFlag := ($fs <= $ft)` |
| `bc1t target` | opcode 0x11, fmt=`BC1`=0x08, tf=1 | `if fpCondFlag: PC = PC_next + (offset<<2)` |
| `bc1f target` | fmt=BC1, tf=0 | `if !fpCondFlag: PC = PC_next + (offset<<2)` |

Field layout for the arithmetic/compare format (`add.s` etc.): opcode(31-26)
= 0x11, `fmt`(25-21), `ft`(20-16), `fs`(15-11), `fd`(10-6), `funct`(5-0) — the
same positions as a plain R-type word's `rs`/`rt`/`rd`/`shamt`/`funct`, which
is why `Instruction.lean`'s `mkRT` helper is reused (with opcode 0x11 OR'd in
explicitly, since `mkRT` itself always leaves the opcode field 0). `mtc1`/
`mfc1` use the same R-type-shaped layout with `fmt` in the `rs` position and
all of `fd`/`funct` (bits 10-0) fixed to 0. `lwc1`/`swc1` are ordinary I-type
words (opcode/`rs`=base/`rt`-position=`ft`/16-bit offset), identical in shape
to `lw`/`sw`. `bc1t`/`bc1f` are also I-type-shaped: opcode 0x11, `rs`-position
field = `BC1` sub-opcode `0x08`, `rt`-position field holds `cc`(bits 4-2,
forced 0)/`nd`(bit 1, forced 0)/`tf`(bit 0) — so the whole `rt`-position field
is exactly `0` (`bc1f`) or `1` (`bc1t`) in this subset — and a 16-bit
sign-extended branch offset, exactly like `beq`/`bne`.

### Citation

Standard MIPS32 instruction-set architecture (the public "MIPS32 Architecture
For Programmers" reference manual family, Volume II-A, "The MIPS32
Instruction Set" — the COP1/FPU chapter). All opcode/fmt/funct values above
(COP1 = 0x11, `LWC1`/`SWC1` = 0x31/0x39, `fmt` codes `MF`=0, `MT`=4, `BC1`=8,
`S`=0x10, `W`=0x14, and `funct` codes 0x00/0x01/0x02/0x03/0x06/0x20/0x24 and
the `C.cond.fmt` family `0x30 | cond` with `cond(EQ)=2`, `cond(LT)=12`,
`cond(LE)=14`) are the standard, invariant MIPS32 COP1 encodings, not
MARS-specific or implementation-chosen values. No internet access was used to
write this section; these are well-established, memorized ISA constants, and
any single value a future reader doubts should be cross-checked against a
primary MIPS32 ISA reference before relying on it for anything beyond this
simulator.

---

## MIPS32 GPR multiply and variable shifts (v1.x addition)

This section documents a v1.x addition: four more real MIPS32 instructions
(`mul`, `sllv`, `srlv`, `srav`) added on top of the v1 scope and the "MIPS32 /
MIPS32r2 additions" section above. Per `docs/spec/MIPS-COVERAGE-GAPS.md`
§§3.4-3.5, these were specifically chosen because real-world compilers
(GCC/Clang) essentially never emit this project's existing `mult`+`mflo`
sequence for plain 32-bit multiplication, and the existing `sll`/`srl`/`sra`
only support a *compile-time-constant* shift amount — any C `x << y` / `x >> y`
with a runtime-valued `y` needs `sllv`/`srlv`/`srav` instead. **Grounding
note**: like the "MIPS32 / MIPS32r2 additions" and floating-point sections
above, these four are grounded directly in the **standard MIPS32
architecture** — specifically MD00086 ("MIPS32 Architecture For Programmers,
Volume II-A: The MIPS32 Instruction Set"), §3.2, Table 3-1 (`MUL`) and
Table 3-8 (`SLLV`/`SRLV`/`SRAV`) — not MARS-specific behavior; MARS is this
project's differential-testing oracle, not the spec source.

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `mul` | R (SPECIAL2) | `$rd = ` low 32 bits of `$rs * $rt`, signed; `hi`/`lo` unchanged |
| `sllv` | R | `$rd = $rt << ($rs & 0x1f)` (logical, zero-fill) |
| `srlv` | R | `$rd = $rt >> ($rs & 0x1f)` (logical, zero-fill) |
| `srav` | R | `$rd = $rt >> ($rs & 0x1f)` (arithmetic, sign-fill) |

### mul (R, SPECIAL2)

- **Encoding**: `opcode=011100` (0x1c, SPECIAL2, same opcode as `clo`/`clz`),
  `funct=000010` (0x02). Fields: `011100 sssss ttttt ddddd 00000 000010` →
  `rs=sssss`, `rt=ttttt`, `rd=ddddd` — a plain, undupicated `rs`/`rt`/`rd`
  R-type shape (unlike `clo`/`clz`, there is no rt-duplicates-rd encoding
  quirk here).
- **Semantics**: Multiply Word to GPR. `$rd` = the low 32 bits of the signed
  64-bit product `$rs * $rt` — i.e. exactly the bit pattern the existing
  `mult` instruction would leave in `lo` (two's-complement multiplication's
  low 32 bits are identical whether the operands are read as signed or
  unsigned, so this is also exactly what `multu`+`mflo` would produce).
- **`hi`/`lo` dialect decision**: Real MIPS32 hardware leaves `hi` and `lo`
  **architecturally unpredictable** after `mul` (MD00086 §3.2's `MUL`
  pseudocode explicitly marks them `UNPREDICTABLE`, in contrast to `mult`'s
  well-defined `{hi,lo} = $rs * $rt`). Since this is a *deterministic*
  simulator (`State` has no notion of "unpredictable" register content),
  this project pins the simplest, most defensible choice: **`hi`/`lo` are
  left completely unchanged** by `mul`. This is a deliberate dialect
  decision, not a spec gap — any program relying on `hi`/`lo`'s value after
  `mul` is already relying on undefined real-hardware behavior, so no
  simulator choice here could be "more correct" against the real ISA; this
  one is simply the easiest to state, implement, and test (`$rd`'s own
  write is the only observable effect).
- **Errors/halts**: none; no overflow concept (this is the entire point of
  `mul` over `add`'s trapping behavior — compilers use it precisely because
  32-bit multiplication has no architecturally-defined overflow trap).
- **ISA note**: standard MIPS32 instruction (present since MIPS32 Release 1).
  Real compilers (GCC/Clang `-O0` and above) emit `mul rd, rs, rt` for every
  plain `int * int` 32-bit multiplication; the `mult`/`mflo` pair is
  essentially never generated by a modern compiler for this purpose (see
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.5).

### sllv (R)

- **Encoding**: `opcode=000000` (SPECIAL), `funct=000100` (0x04). Fields:
  `000000 sssss ttttt ddddd 00000 000100` → `rs=sssss` (shift-amount
  register), `rt=ttttt` (value to shift), `rd=ddddd` (destination); the
  5-bit shamt-position field (bits 10-6) is unused/fixed `0` in the encoding
  — unlike `sll`, the shift amount is *not* read from this field.
- **Semantics**: Shift Word Left Logical Variable. `$rd = $rt << ($rs &
  0x1f)` — the shift amount is the **low 5 bits of register `$rs`**, masked
  (not clamped or modulo'd in any other way); e.g. `$rs = 33` (`0b100001`)
  behaves identically to `$rs = 1`, and `$rs = 32` behaves identically to
  `$rs = 0` (a full no-op shift, not an all-zero result — a common
  implementation mistake this spec deliberately avoids testing for). Fill
  is logical (zero-fill from the right), matching `sll`.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction (MIPS I onward). Emitted by every
  compiler for `x << y` in C whenever `y` is not a compile-time constant
  (MD00086 §3.2, Table 3-8).

### srlv (R)

- **Encoding**: `opcode=000000` (SPECIAL), `funct=000110` (0x06). Same field
  layout as `sllv`.
- **Semantics**: Shift Word Right Logical Variable. `$rd = $rt >> ($rs &
  0x1f)`, logical (zero-fill from the left), matching `srl`. Same low-5-bit
  masking behavior as `sllv`.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction. Emitted for `(unsigned)x >> y`
  in C with a non-constant `y`.

### srav (R)

- **Encoding**: `opcode=000000` (SPECIAL), `funct=000111` (0x07). Same field
  layout as `sllv`/`srlv`.
- **Semantics**: Shift Word Right Arithmetic Variable. `$rd = $rt >> ($rs &
  0x1f)`, arithmetic (sign-extending fill from the left, replicating bit 31
  of `$rt`), matching `sra`. Same low-5-bit masking behavior as `sllv`.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction. Emitted for `(signed)x >> y` in
  C with a non-constant `y`.

### Citation

MIPS32 Architecture For Programmers, Volume II-A: The MIPS32 Instruction Set
(MD00086, Rev 2.50), §3.2: Table 3-1 (p. 24, entry 217) for `MUL`'s
`opcode=SPECIAL2`/`funct=0x02` encoding and its `UNPREDICTABLE`-HI/LO
pseudocode; Table 3-8 (p. 27, entries 265/273/270) for `SLLV`/`SRLV`/`SRAV`'s
`opcode=SPECIAL`/`funct=0x04`/`0x06`/`0x07` encodings and their register-held
shift-amount pseudocode (`s = GPR[rs]31..0; s = s4..0` — i.e. the low-5-bit
mask documented above). No internet access was used to write this section;
these are well-established, memorized ISA constants, cross-referenced against
`docs/spec/MIPS-COVERAGE-GAPS.md`'s independent research pass (§§3.4-3.5,
which cites the same table/page/entry numbers) before being relied upon here.
