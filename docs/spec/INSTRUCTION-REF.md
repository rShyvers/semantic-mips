# MARS MIPS v1 Instruction Reference

This document is a precise, source-grounded reference for the ~24 machine
instructions plus 4 syscalls in Lean spec v1 scope, intended to ground the
`step` function for MARS MIPS small-step semantics. Every semantic claim is
cited against the vendored MARS 4.5 source (`vendor/mars-src/`). Where MARS
deviates from "textbook" MIPS, or where the source is ambiguous/inconsistent,
this is flagged explicitly rather than normalized away.

Conventions pinned elsewhere and assumed here (see
[`SPEC-NOTES.md`](SPEC-NOTES.md)): no branch delay slots (`DelayedBranching`
default `false`); execution starts at `0x00400000`; big-endian memory;
32 GPRs plus separate 64-bit `hi`/`lo` pair (internally registers 33/34);
`$zero` write-ignored.

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
- **Branches** (`beq`,`bne`,`blez`,`bgtz`): on taken condition,
  `processBranch(displacement)` sets
  `PC = PC_next + (displacement << 2)` (`InstructionSet.java` line ~3272,
  the delayed-branching-off path; the comment literally reads "Decrement
  needed because PC has already been incremented" and that decrement is
  commented out). `displacement` is the instruction's signed 16-bit offset
  field, i.e. the branch target is PC-relative to the instruction *after*
  the branch, scaled by 4 — standard MIPS branch-target arithmetic, but
  **with no delay slot executed** (see rule 3).
- **Jumps** (`j`,`jal`): `processJump(targetAddress)` sets
  `PC = targetAddress` directly, where
  `targetAddress = (PC_next & 0xF0000000) | (target_field << 2)`
  (`InstructionSet.java` lines ~1207–1211, 1238–1240). Note the top 4 bits
  come from `PC_next` (the already-incremented PC), not from the jump
  instruction's own address.
- **Link instructions** (`jal`): `processReturnAddress(31)` sets
  `$ra = PC_next` (plus `INSTRUCTION_LENGTH` only if delayed branching is
  enabled, which is off by default) — `InstructionSet.java` lines
  3309–3315. With delayed branching off (our v1 scope), `$ra` is exactly the
  address of the instruction following `jal`.

### 2. `$zero` is write-ignored

Source: `vendor/mars-src/mars/mips/hardware/RegisterFile.java`,
`updateRegister(int num, int val)`, lines 95–119: when `num == 0` the method
takes the empty branch and returns `old = 0` without touching the register
array. Reads of register 0 always return `0` (it is initialized to 0 and
never written). Every instruction below that writes `$rd`/`$rt` is silently
a no-op if that operand is `$zero`.

### 3. No branch delay slot (default configuration)

Source: `vendor/mars-src/mars/mips/instructions/InstructionSet.java`,
`processBranch`/`processJump` (lines 3265–3306), gated on
`Globals.getSettings().getDelayedBranchingEnabled()`, and
`vendor/mars-src/mars/Settings.java` (`DelayedBranching` defaults to
`false`, per `SPEC-NOTES.md` §3). With the default setting, a taken
branch/jump updates `PC` immediately to the target; the next instruction
fetched is the one at the target, **not** the instruction physically
following the branch/jump in memory. **This differs from real MIPS
hardware**, which always executes one delay-slot instruction after every
branch/jump. Flagged per-instruction below.

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
- **Semantics**: `PC = (PC_next & 0xF0000000) | (target << 2)`. `PC_next`
  is the PC *after* this instruction's fetch-increment (rule 1), so the top
  4 bits of the jump target come from the region containing the
  instruction *after* `j`, not `j` itself (normal MIPS pseudo-direct
  jump semantics).
- **Errors/halts**: none directly; a bad target can later cause an
  instruction-fetch `AddressErrorException` on the next fetch.
- **MARS note**: **DEVIATION** — no delay slot executed (Global rule 3);
  `PC` becomes the target immediately rather than after one more
  sequential instruction, differing from real MIPS hardware's defined
  delay-slot semantics.
- **Source**: `InstructionSet.java`, lines 1200–1216;
  `processJump` at lines 3288–3298.

### jal (J)
- **Encoding**: `opcode=000011` (0x03). Same field layout as `j`.
- **Semantics**: `$ra ($31) = PC_next` (via `processReturnAddress(31)`,
  with delayed branching off this adds no extra offset); then
  `PC = (PC_next & 0xF0000000) | (target << 2)`, identical target
  computation to `j`.
- **Errors/halts**: none directly.
- **MARS note**: **DEVIATION** — same no-delay-slot behavior as `j` (Global
  rule 3). Link-address value itself (`PC_next`, i.e. address of the
  instruction textually following `jal`) matches textbook MIPS; only the
  absence of delay-slot execution differs.
- **Source**: `InstructionSet.java`, lines 1228–1244;
  `processReturnAddress` at lines 3309–3316.

### beq (I-branch)
- **Encoding**: `opcode=000100` (0x04). Fields:
  `000100 fffff sssss tttttttttttttttt` → `rs=fffff`($t1, operand 0),
  `rt=sssss`($t2, operand 1), `offset=tttt...`(operand 2, 16-bit signed
  word displacement).
- **Semantics**: if `$rs == $rt` (32-bit equality), `PC = PC_next +
  (offset << 2)` via `processBranch`; otherwise PC stays at `PC_next`.
- **Errors/halts**: none directly from the comparison; a bad target can
  cause a later fetch error.
- **MARS note**: **DEVIATION** — no delay slot (Global rule 3): the branch,
  if taken, redirects fetch to the target on the very next cycle instead of
  executing one more sequential instruction first.
- **Source**: `InstructionSet.java`, lines 858–875;
  `processBranch` at lines 3265–3281.

### bne (I-branch)
- **Encoding**: `opcode=000101` (0x05). Same layout as `beq`.
- **Semantics**: if `$rs != $rt`, `PC = PC_next + (offset << 2)`.
- **Errors/halts**: none directly.
- **MARS note**: **DEVIATION** — no delay slot, same as `beq`.
- **Source**: `InstructionSet.java`, lines 876–891.

### blez (I-branch)
- **Encoding**: `opcode=000110` (0x06). Fields:
  `000110 fffff 00000 ssssssssssssssss` → `rs=fffff`($t1, operand 0),
  `rt=00000`(fixed/unused), `offset=ssss...`(operand 1).
- **Semantics**: if `$rs <= 0` (signed comparison, includes zero),
  `PC = PC_next + (offset << 2)`.
- **Errors/halts**: none directly.
- **MARS note**: **DEVIATION** — no delay slot, same as `beq`.
- **Source**: `InstructionSet.java`, lines 942–958.

### bgtz (I-branch)
- **Encoding**: `opcode=000111` (0x07). Same layout as `blez`.
- **Semantics**: if `$rs > 0` (signed, strictly positive), `PC = PC_next +
  (offset << 2)`.
- **Errors/halts**: none directly.
- **MARS note**: **DEVIATION** — no delay slot, same as `beq`.
- **Source**: `InstructionSet.java`, lines 926–941.

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
  `SystemIO.printString`. No registers or memory are modified by the
  syscall itself.
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

## Flagged MARS deviations (summary)

1. **`div`/`divu` by zero**: no exception, `hi`/`lo` left unchanged
   (explicit source comment citing the MIPS32 spec over the COD3 textbook
   framing). `Exceptions.DIVIDE_BY_ZERO_EXCEPTION` exists but is dead code.
2. **No branch delay slot by default** (`j`, `jal`, `beq`, `bne`, `blez`,
   `bgtz`): `DelayedBranching` setting defaults to `false`; PC jumps to the
   target immediately with no delay-slot instruction executed, unlike real
   MIPS hardware's architecturally-mandated delay slot.
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
