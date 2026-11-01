# MIPS Architecture Coverage Gaps in Semantic MIPS

This report establishes an authoritative, source-grounded inventory of all features and instructions defined in the official MIPS32 Instruction Set Architecture (ISA) and Privileged Resource Architecture (PRA) that are currently **unimplemented** or **unverified** in Semantic MIPS.

Research date: **November 1, 2026**.

---

## 1. Project Baseline Scope & Verification Coverage Gap

### Implemented Scope (76 Instruction Variants)
Semantic MIPS explicitly targets the real 32-bit MIPS32 architecture (not MARS-specific dialect behaviors; MARS is employed strictly as a differential-testing oracle). It executes with one-instruction branch delay slots, 32 general-purpose registers (GPRs), a hardwired `$zero`, and dedicated 32-bit `hi`/`lo` registers. It currently implements 70 core machine instructions and 6 common assembler pseudo-instructions/variants:
- **Integer R-Type (25)**: `add`, `addu`, `sub`, `subu`, `and`, `or`, `xor`, `nor`, `slt`, `sltu`, `movn`, `movz`, `sll`, `srl`, `sra`, `mult`, `multu`, `div`, `divu`, `mflo`, `mfhi`, `clo`, `clz`, `seb`, `seh`.
- **Integer I-Type (8)**: `addi`, `addiu`, `slti`, `sltiu`, `andi`, `ori`, `xori`, `lui`.
- **Memory (7)**: `lw`, `sw`, `lb`, `lbu`, `lh`, `lhu`, `sh`.
- **Control Flow (6)**: `beq`, `bne`, `blez`, `bgtz`, `j`, `jal` (all with architecturally accurate single-instruction delay-slot semantics).
- **Traps & Syscalls (8)**: `syscall`, `teq`, `tne`, `tlt`, `tge`, `tltu`, `tgeu`, `break`.
- **Floating Point (Coprocessor 1, Single-Precision Only) (16)**: `mfc1`, `mtc1`, `lwc1`, `swc1`, `add.s`, `sub.s`, `mul.s`, `div.s`, `mov.s`, `cvt.s.w`, `cvt.w.s`, `c.eq.s`, `c.lt.s`, `c.le.s`, `bc1t`, `bc1f`.
- **Coprocessor 0 (Minimal Foundation)**: Execution state carries registers `Status`, `Cause`, and `EPC` sufficient to service synchronous software traps, taking exceptions by vectoring to `0x80000180`.
- **Assembler Pseudo-instructions (6)**: `li`, `la`, `move`, `nop`, plus MARS differential test harness conventions.

### Verification Coverage Gap (Pre-existing Baseline)
Of the 76 implemented instruction variants, only ~16 currently have kernel-checked Lean 4 theorem specifications in `Semantics/Specs/StepSpec.lean`: `add`, `sub`, `addi`, `div` (including div-by-zero and negative-dividend boundary cases), `beq`, `bne` (including delay-slot landing behavior), `jal` (including the delay-slot-in-delay-slot halt condition), `lw` (including misaligned access detection), `lb`, `lbu`, and syscalls 1 (`print_int`) and 10 (`exit`). The remaining 60 implemented instruction variants (including 100% of floating-point instructions, trap instructions, and most integer ALU/shift/logical operations) are implemented in `step` but possess zero formal specification theorems. This report focuses on the architectural implementation gaps relative to the real MIPS32 standard.

---

## 2. Authoritative Primary Sources for Real MIPS32

The MIPS architecture is defined across three core volumes published by MIPS Technologies, Inc. (and continued under Imagination Technologies LTD.):

1. **Volume I: Introduction to the MIPS32® Architecture**
   - Document Number: `MD00082` (Revision 0.95, March 2001; Revision 2.50, July 2005; Revision 6.01, August 2014).
   - Scope: Fundamental programming model, register sets, pipeline structure, instruction formats, endianness, and architecture subsetting rules.
2. **Volume II / II-A: The MIPS32® Instruction Set Manual**
   - Document Number: `MD00086` (Revision 2.50, July 1, 2005 [MIPS32 Release 2]; Revision 6.04, November 13, 2015 [MIPS32 Release 6]).
   - Scope: Exact instruction bit-encodings, assembly syntax, pseudocode operational specifications, pipeline exceptions, and compliance tables (Tables 3-1 through 3-24).
3. **Volume III: The MIPS32® Privileged Resource Architecture**
   - Document Number: `MD00090` (Revision 0.95, March 2001; Revision 2.50, July 2005; Revision 6.02, July 2015).
   - Scope: System Coprocessor (CP0), virtual memory address mapping (`kuseg`, `kseg0`, `kseg1`, `ksseg`, `kseg3`), Translation Lookaside Buffer (TLB), exception vectors, interrupt controllers, and cache interfaces.

*Note on Architecture Releases*: MIPS32 Release 1 (MIPS32r1) and Release 2 (MIPS32r2) define the classic 32-bit RISC architecture targeted by Patterson & Hennessy textbooks, GCC/Linux, and educational simulators (SPIM/MARS). Release 6 (MIPS32r6) removed delay slots, branch likely, HI/LO registers, and unaligned load/store (`lwl`/`lwr`). Because Semantic MIPS explicitly models delay slots and HI/LO registers, MIPS32r2 (MD00086 Rev 2.50) serves as the primary baseline, with Release 6 differences noted where relevant.

---

## 3. Categorized Inventory of Unimplemented MIPS32 Features

### 3.1 Register-Indirect Jumps & Procedure Calling
These instructions perform control-flow transfers to dynamically computed target addresses held in general-purpose registers rather than 26-bit PC-region immediate targets.

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `jr rs` | Jump Register | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 155 | **Near-universal**: Used for every standard function return (`jr $ra`), switch statement jump table, and computed branch in compiled C and assembly. |
| `jalr rd, rs` | Jump and Link Register | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 150 | **Near-universal**: Standard instruction for indirect procedure calls, dynamic linking, and function pointers (`jalr $t9`). |
| `jr.hb rs` | Jump Register with Hazard Barrier | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 156 (MIPS32r2) | **Rare**: Kernel/OS only; used when returning across CP0 execution/instruction hazard boundaries. |
| `jalr.hb rd, rs` | Jump and Link Register with Hazard Barrier | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 152 (MIPS32r2) | **Rare**: Used for privileged hazard clearance during indirect linking. |

### 3.2 Conditional Branches (Zero-Comparison & Subroutine Link)
Semantic MIPS implements `beq`, `bne`, `blez`, and `bgtz`, but lacks the single-register branches comparing against zero with `<` or `>=` and linking variants.

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `bltz rs, offset` | Branch on Less Than Zero | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 85 | **Very Common**: Standard conditional branch emitted for C expressions `if (x < 0)`. |
| `bgez rs, offset` | Branch on Greater Than or Equal to Zero | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 73 | **Very Common**: Standard conditional branch emitted for C expressions `if (x >= 0)`. |
| `bltzal rs, offset` | Branch on Less Than Zero and Link | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 87 | **Rare**: Conditional subroutine invocation; rarely emitted by modern compilers. |
| `bgezal rs, offset` | Branch on Greater Than or Equal to Zero and Link | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 75 | **Common**: Hardware foundation for position-independent code address discovery (`bal offset` / `bgezal $0, offset`). |
| `bal offset` | Branch and Link | MD00086 Rev 2.50, §3.2, Table 3-2, p. 25, 59 | **Common**: Standard assembly pseudo-op / encoding for PC-relative subroutine calls. |

### 3.3 Branch-Likely Instructions (Deprecated in MIPS32, Removed in r6)
Branch-likely instructions execute the delay slot *only* if the branch is taken; if not taken, the delay slot instruction is nullified (squashed).

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `beql rs, rt, offset` | Branch on Equal Likely | MD00086 Rev 2.50, §3.2, Table 3-10, p. 28, 69 | **Uncommon**: Classic MIPS II loop optimization; deprecated in MIPS32 and removed in Release 6. |
| `bnel rs, rt, offset` | Branch on Not Equal Likely | MD00086 Rev 2.50, §3.2, Table 3-10, p. 28, 92 | **Uncommon**: Found in older GCC code generated with `-mbranch-likely`. |
| `blezl rs, offset` | Branch on Less Than or Equal to Zero Likely | MD00086 Rev 2.50, §3.2, Table 3-10, p. 28, 83 | **Rare**: Loop termination branch in legacy binaries. |
| `bgtzl rs, offset` | Branch on Greater Than Zero Likely | MD00086 Rev 2.50, §3.2, Table 3-10, p. 28, 81 | **Rare**: Loop termination branch in legacy binaries. |
| `bltzl rs, offset` | Branch on Less Than Zero Likely | MD00086 Rev 2.50, §3.2, Table 3-10, p. 28, 89 | **Rare**: Legacy loop code. |
| `bgezl rs, offset` | Branch on Greater Than or Equal to Zero Likely | MD00086 Rev 2.50, §3.2, Table 3-10, p. 28, 77 | **Rare**: Legacy loop code. |
| `bltzall rs, offset` | Branch on Less Than Zero and Link Likely | MD00086 Rev 2.50, §3.2, Table 3-10, p. 28, 88 | **Very Rare**: Obsolete linking conditional branch. |
| `bgezall rs, offset` | Branch on Greater Than or Equal to Zero and Link Likely | MD00086 Rev 2.50, §3.2, Table 3-10, p. 28, 76 | **Very Rare**: Obsolete linking conditional branch. |

### 3.4 Variable Shifts, Rotates, and Bitfield Operations
Semantic MIPS implements only constant-shamt shifts (`sll`, `srl`, `sra`). Real MIPS32 provides variable shifts and (in r2) bitfield extract/insert and rotate instructions.

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `sllv rd, rt, rs` | Shift Word Left Logical Variable | MD00086 Rev 2.50, §3.2, Table 3-8, p. 27, 265 | **Very Common**: Emitted for any variable shift in C (`x << y`). |
| `srlv rd, rt, rs` | Shift Word Right Logical Variable | MD00086 Rev 2.50, §3.2, Table 3-8, p. 27, 273 | **Very Common**: Emitted for unsigned variable shift in C (`(unsigned)x >> y`). |
| `srav rd, rt, rs` | Shift Word Right Arithmetic Variable | MD00086 Rev 2.50, §3.2, Table 3-8, p. 27, 270 | **Very Common**: Emitted for signed variable shift in C (`(signed)x >> y`). |
| `rotr rd, rt, sa` | Rotate Word Right | MD00086 Rev 2.50, §3.2, Table 3-8, p. 27, 245 (MIPS32r2) | **Moderate**: Common in cryptographic hash implementations and bit manipulation routines. |
| `rotrv rd, rt, rs` | Rotate Word Right Variable | MD00086 Rev 2.50, §3.2, Table 3-8, p. 27, 246 (MIPS32r2) | **Moderate**: Dynamic circular bit rotation. |
| `ext rt, rs, pos, size` | Extract Bit Field | MD00086 Rev 2.50, §3.2, Table 3-6, p. 26, 140 (MIPS32r2) | **Common**: Ubiquitous in MIPS32r2 compiled C for struct bitfields and protocol decoding. |
| `ins rt, rs, pos, size` | Insert Bit Field | MD00086 Rev 2.50, §3.2, Table 3-6, p. 26, 148 (MIPS32r2) | **Common**: Standard MIPS32r2 instruction for packing struct bitfields. |
| `wsbh rd, rt` | Word Swap Bytes Within Halfwords | MD00086 Rev 2.50, §3.2, Table 3-6, p. 26, 321 (MIPS32r2) | **Moderate**: Used in endianness conversion pipelines (`wsbh` + `rotr 16` forms byte-swap 32). |

### 3.5 Integer Multiply-Accumulate & GPR Multiply
Semantic MIPS implements 2-operand `mult`/`multu` to `hi`/`lo` and `mflo`/`mfhi`, but lacks 3-operand GPR multiply and multiply-accumulate operations.

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `mul rd, rs, rt` | Multiply Word to GPR | MD00086 Rev 2.50, §3.2, Table 3-1, p. 24, 217 | **Near-universal**: Compilers (GCC/Clang) overwhelmingly prefer `mul rd, rs, rt` for 32-bit multiplication because it writes directly to GPR without clobbering HI/LO or stalling pipelines. |
| `madd rs, rt` | Multiply and Add Word to HI/LO | MD00086 Rev 2.50, §3.2, Table 3-1, p. 24, 182 | **Moderate**: Core loop instruction in DSP filters, vector dot-products, and numerical libraries. |
| `maddu rs, rt` | Multiply and Add Unsigned Word to HI/LO | MD00086 Rev 2.50, §3.2, Table 3-1, p. 24, 184 | **Moderate**: Unsigned vector dot-product and big-integer arithmetic. |
| `msub rs, rt` | Multiply and Subtract Word to HI/LO | MD00086 Rev 2.50, §3.2, Table 3-1, p. 24, 209 | **Uncommon**: DSP filter routines. |
| `msubu rs, rt` | Multiply and Subtract Unsigned Word to HI/LO | MD00086 Rev 2.50, §3.2, Table 3-1, p. 24, 211 | **Uncommon**: DSP filter routines. |
| `mthi rs` | Move to HI Register | MD00086 Rev 2.50, §3.2, Table 3-7, p. 27, 215 | **Common**: Mandatory for OS context switching and setjmp/longjmp to save/restore HI register. |
| `mtlo rs` | Move to LO Register | MD00086 Rev 2.50, §3.2, Table 3-7, p. 27, 216 | **Common**: Mandatory for OS context switching and setjmp/longjmp to save/restore LO register. |

### 3.6 Unaligned Memory Access (Classic MIPS Feature)
Classic MIPS hardware requires aligned memory accesses for `lw`/`sw`. To handle unaligned words without exception overhead, MIPS I–r5 provides unaligned load/store pairs.

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `lwl rt, offset(rs)` | Load Word Left | MD00086 Rev 2.50, §3.2, Table 3-4, p. 25, 174 | **Very Common**: Found in all classic MIPS standard library implementations (`memcpy`, `strcpy`) and unaligned C struct accesses. |
| `lwr rt, offset(rs)` | Load Word Right | MD00086 Rev 2.50, §3.2, Table 3-4, p. 25, 177 | **Very Common**: Paired with `lwl` to assemble unaligned 32-bit words across byte boundaries. |
| `swl rt, offset(rs)` | Store Word Left | MD00086 Rev 2.50, §3.2, Table 3-4, p. 26, 282 | **Very Common**: Paired with `swr` for unaligned stores in classic MIPS code. |
| `swr rt, offset(rs)` | Store Word Right | MD00086 Rev 2.50, §3.2, Table 3-4, p. 26, 285 | **Very Common**: Paired with `swl` for unaligned stores. |

*Note*: MIPS32 Release 6 obsoleted and removed `lwl`/`lwr`/`swl`/`swr` (MD00086 Rev 6.04 §2.1.2), replacing them with architectural support for misaligned accesses. However, in classic MIPS and textbook MIPS assembly, `lwl`/`lwr` is a defining architectural mechanism.

### 3.7 Atomic Memory Operations & Synchronization
Real MIPS32 defines synchronization and atomic read-modify-write primitives for multiprocessor and multitasking environments.

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `ll rt, offset(rs)` | Load Linked Word | MD00086 Rev 2.50, §3.2, Table 3-4, p. 25, 167 | **Universal for concurrency**: Standard textbook and real-world instruction for atomic lock-free algorithms, spinlocks, and mutexes. Sets hardware `LLbit`. |
| `sc rt, offset(rs)` | Store Conditional Word | MD00086 Rev 2.50, §3.2, Table 3-4, p. 26, 253 | **Universal for concurrency**: Paired with `ll`. Stores conditionally if no intervening write/exception cleared `LLbit`; writes success status (1 or 0) back to `$rt`. |
| `sync [stype]` | Synchronize Shared Memory | MD00086 Rev 2.50, §3.2, Table 3-4, p. 26, 288 | **Very Common**: Memory barrier instruction required between memory writes and locks in concurrent code. |
| `synci offset(rs)` | Synchronize Caches for Instruction Writes | MD00086 Rev 2.50, §3.2, Table 3-4, p. 26, 290 (MIPS32r2) | **Moderate**: Mandatory for JIT compilers, runtime code generators, and dynamic linkers to flush instruction caches. |

### 3.8 Immediate-Operand Traps
Semantic MIPS implements the register-register trap instructions (`teq`, `tne`, `tlt`, `tge`, `tltu`, `tgeu`), but lacks the immediate-operand variants.

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `teqi rs, imm` | Trap if Equal Immediate | MD00086 Rev 2.50, §3.2, Table 3-9, p. 27, 296 | **Rare**: Emitted by specialized compilers for immediate assertion/null checks. |
| `tnei rs, imm` | Trap if Not Equal Immediate | MD00086 Rev 2.50, §3.2, Table 3-9, p. 27, 308 | **Rare**: Assertion/boundary checks. |
| `tgei rs, imm` | Trap if Greater or Equal Immediate | MD00086 Rev 2.50, §3.2, Table 3-9, p. 27, 298 | **Rare**: Array upper-bound checking. |
| `tgeiu rs, imm` | Trap if Greater or Equal Immediate Unsigned | MD00086 Rev 2.50, §3.2, Table 3-9, p. 27, 299 | **Rare**: Unsigned bounds checking. |
| `tlti rs, imm` | Trap if Less Than Immediate | MD00086 Rev 2.50, §3.2, Table 3-9, p. 27, 302 | **Rare**: Lower-bound checking. |
| `tltiu rs, imm` | Trap if Less Than Immediate Unsigned | MD00086 Rev 2.50, §3.2, Table 3-9, p. 27, 304 | **Rare**: Unsigned lower-bound checking. |

### 3.9 Floating-Point Unit (Coprocessor 1) Coverage Gaps
While Semantic MIPS models a basic single-precision subset (16 instructions), real MIPS32 defines a full IEEE-754 FPU with 32 FPRs, double precision, fixed-point conversions, and multiple condition codes.

#### A. Double-Precision Floating Point (`.d` format)
Under MIPS32 compliance rules (MD00086 Rev 2.50, §3.1, p. 23): *"If the FPU is implemented, it must include S, D, and W formats, operate instructions, and all supporting instructions."* Omitting double precision makes Semantic MIPS non-compliant with standard MIPS32 FPU specifications.

| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `add.d fd, fs, ft` | Double-Precision Add | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 48 | **Universal**: Standard C `double` addition (`a + b`). |
| `sub.d fd, fs, ft` | Double-Precision Subtract | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 277 | **Universal**: Standard C `double` subtraction. |
| `mul.d fd, fs, ft` | Double-Precision Multiply | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 219 | **Universal**: Standard C `double` multiplication. |
| `div.d fd, fs, ft` | Double-Precision Divide | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 126 | **Universal**: Standard C `double` division. |
| `sqrt.d fd, fs` | Double-Precision Square Root | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 268 | **Common**: Hardware square root for C `sqrt(double)`. |
| `abs.d fd, fs` | Double-Precision Absolute Value | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 46 | **Common**: Emitted for C `fabs(double)`. |
| `neg.d fd, fs` | Double-Precision Negate | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 222 | **Common**: Emitted for `-x` where `x` is `double`. |
| `mov.d fd, fs` | Double-Precision Register Copy | MD00086 Rev 2.50, §3.2, Table 3-16, p. 30, 196 | **Very Common**: Double-precision register assignment. |
| `ldc1 ft, offset(rs)` | Load Doubleword to Floating Point | MD00086 Rev 2.50, §3.2, Table 3-15, p. 29, 161 | **Universal**: Loads 64-bit IEEE double from memory into FPR pair/register. |
| `sdc1 ft, offset(rs)` | Store Doubleword from Floating Point | MD00086 Rev 2.50, §3.2, Table 3-15, p. 30, 255 | **Universal**: Stores 64-bit IEEE double from FPR to memory. |
| `c.cond.d [cc], fs, ft` | Double-Precision Compare (16 predicates) | MD00086 Rev 2.50, §3.2, Table 3-13, p. 29, 93–97 | **Universal**: All relational comparisons between doubles (`==`, `<`, `<=`, `>`, etc.). |
| `cvt.d.s fd, fs` | Convert Single to Double FP | MD00086 Rev 2.50, §3.2, Table 3-14, p. 29, 115 | **Universal**: Emitted for promotion `(double)my_float`. |
| `cvt.d.w fd, fs` | Convert Word Integer to Double FP | MD00086 Rev 2.50, §3.2, Table 3-14, p. 29, 117 | **Universal**: Emitted for promotion `(double)my_int`. |
| `cvt.s.d fd, fs` | Convert Double to Single FP | MD00086 Rev 2.50, §3.2, Table 3-14, p. 29, 119 | **Universal**: Emitted for demotion `(float)my_double`. |
| `cvt.w.d fd, fs` | Convert Double to Word Integer | MD00086 Rev 2.50, §3.2, Table 3-14, p. 29, 123 | **Universal**: Emitted for truncation `(int)my_double`. |

#### B. Missing Single-Precision Operations & Rounding Primitives
| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `sqrt.s fd, fs` | Single-Precision Square Root | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 268 | **Common**: Hardware square root for C `sqrtf(float)`. |
| `abs.s fd, fs` | Single-Precision Absolute Value | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 46 | **Common**: Hardware absolute value for C `fabsf(float)`. |
| `neg.s fd, fs` | Single-Precision Negate | MD00086 Rev 2.50, §3.2, Table 3-11, p. 28, 222 | **Common**: Sign bit inversion for floating point. |
| `c.cond.s` (remaining 13) | Complete IEEE-754 Single FP Predicates | MD00086 Rev 2.50, §3.2, Table 3-13, p. 29, 93–97 | **Common**: Semantic MIPS implements only `c.eq.s`, `c.lt.s`, and `c.le.s`. Missing 13 standard conditions (`c.f`, `c.un`, `c.ueq`, `c.olt`, `c.ult`, `c.ole`, `c.ule`, `c.sf`, `c.ngle`, `c.seq`, `c.ngl`, `c.nge`, `c.ngt`). |
| `round.w.fmt`, `trunc.w.fmt`, `ceil.w.fmt`, `floor.w.fmt` | Directed Rounding to Integer Word | MD00086 Rev 2.50, §3.2, Table 3-14, p. 29, 101, 142, 247, 311 | **Common**: Explicit IEEE-754 rounding modes used for standard library `round()`, `floor()`, `ceil()`. |

#### C. Control Registers, Multiple Condition Codes, and Register Transfers
| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `cfc1 rt, fs` | Move Control Word from Coprocessor 1 | MD00086 Rev 2.50, §3.2, Table 3-16, p. 30, 102 | **Common**: Reading `FCSR` (Floating-Point Control and Status Register) for exception flags and rounding modes. |
| `ctc1 rt, fs` | Move Control Word to Coprocessor 1 | MD00086 Rev 2.50, §3.2, Table 3-16, p. 30, 112 | **Common**: Setting rounding modes and clearing IEEE-754 exception flags. |
| `mfhc1 rt, fs` | Move Word from High Half of FPR | MD00086 Rev 2.50, §3.2, Table 3-16, p. 30, 192 (MIPS32r2) | **Common in r2**: Allows 32-bit GPR CPU to access the upper 32 bits of 64-bit FPRs. |
| `mthc1 rt, fs` | Move Word to High Half of FPR | MD00086 Rev 2.50, §3.2, Table 3-16, p. 30, 213 (MIPS32r2) | **Common in r2**: Writing upper 32 bits of 64-bit FPRs. |
| Multi-CC support (`cc` 0–7) | 8 Condition Code Flags | MD00082 Rev 0.95 §5.6.3; MD00086 Rev 2.50 p. 61 | **Moderate**: Semantic MIPS hardcodes CC 0. Compilers use CC 1–7 to evaluate multiple floating point conditions without spilling. |
| `movf` / `movt` | Move GPR Conditional on FP False / True | MD00086 Rev 2.50, §3.2, Table 3-7, p. 26–27, 198, 201 | **Moderate**: Conditional branch elimination for float comparisons. |
| `movf.fmt`, `movt.fmt`, `movn.fmt`, `movz.fmt` | Move FPR Conditional on FP CC / GPR | MD00086 Rev 2.50, §3.2, Table 3-16, p. 30, 199–205 | **Moderate**: Floating-point conditional moves. |
| `bc1fl`, `bc1tl` | FP Branch Likely on False / True | MD00086 Rev 2.50, §3.2, Table 3-17, p. 30, 63, 65 | **Uncommon**: Deprecated FP branch likely. |

### 3.10 Privileged Resource Architecture (PRA) & Coprocessor 0
Semantic MIPS provides minimal CP0 state (`Status`, `Cause`, `EPC`) solely as internal trap destination storage; it provides **zero** user- or kernel-accessible CP0 instructions, no return-from-exception instruction, and no virtual memory hardware.

#### A. CP0 Access & Execution Control Instructions
| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `mfc0 rt, rd, sel` | Move from Coprocessor 0 | MD00086 Rev 2.50, §3.2, Table 3-23, p. 31, 186 | **Universal for OS kernels**: Primary instruction to read hardware configuration, interrupt masks, fault addresses, and exception state. |
| `mtc0 rt, rd, sel` | Move to Coprocessor 0 | MD00086 Rev 2.50, §3.2, Table 3-23, p. 31, 210 | **Universal for OS kernels**: Primary instruction to enable/disable interrupts, configure virtual memory, and set timers. |
| `eret` | Exception Return | MD00086 Rev 2.50, §3.2, Table 3-23, p. 31, 139 | **Universal for OS kernels**: Mandatory instruction to exit exception handlers, atomically clearing `Status.EXL` and restoring PC from `EPC`. |
| `wait` | Enter Standby Mode | MD00086 Rev 2.50, §3.2, Table 3-23, p. 32, 319 | **Very Common**: OS idle loop instruction; halts CPU until an interrupt arrives. |
| `di [rt]` | Disable Interrupts | MD00086 Rev 2.50, §3.2, Table 3-23, p. 31, 124 (MIPS32r2) | **Very Common in r2**: Atomic interrupt disabling for critical sections. |
| `ei [rt]` | Enable Interrupts | MD00086 Rev 2.50, §3.2, Table 3-23, p. 31, 134 (MIPS32r2) | **Very Common in r2**: Atomic interrupt enabling. |
| `rdpgpr rd, rt` | Read GPR from Previous Shadow Set | MD00086 Rev 2.50, §3.2, Table 3-23, p. 32, 240 (MIPS32r2) | **Moderate**: Fast interrupt handling with shadow register sets. |
| `wrpgpr rd, rt` | Write GPR to Previous Shadow Set | MD00086 Rev 2.50, §3.2, Table 3-23, p. 32, 320 (MIPS32r2) | **Moderate**: Shadow register management. |
| `ehb` | Execution Hazard Barrier | MD00086 Rev 2.50, §3.2, Table 3-3, p. 25, 133 (MIPS32r2) | **Common in OS kernels**: Synchronizes CP0 register update hazards. |

#### B. Memory Management & Translation Lookaside Buffer (TLB)
MIPS32 uses software-managed dual-entry TLB mapping virtual addresses to physical pages.

| Feature / Mnemonic | Description / Syntax | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `tlbwi` | Write Indexed TLB Entry | MD00086 Rev 2.50, §3.2, Table 3-23, p. 32, 305 | **Universal for OS kernels**: Writes `EntryHi`, `EntryLo0`, `EntryLo1`, `PageMask` to TLB slot `Index`. |
| `tlbwr` | Write Random TLB Entry | MD00086 Rev 2.50, §3.2, Table 3-23, p. 32, 306 | **Universal for OS kernels**: Standard fast TLB refill handler instruction (using pseudo-random replacement). |
| `tlbp` | Probe TLB for Matching Entry | MD00086 Rev 2.50, §3.2, Table 3-23, p. 32, 303 | **Universal for OS kernels**: Checks if virtual page is present in TLB; sets `Index`. |
| `tlbr` | Read Indexed TLB Entry | MD00086 Rev 2.50, §3.2, Table 3-23, p. 32, 304 | **Common for OS kernels**: Reads TLB entry into CP0 registers during page invalidation. |
| Virtual Segments | `kuseg`, `kseg0`, `kseg1`, `ksseg`, `kseg3` | MD00090 Rev 0.95, Chapter 4, pp. 11–16 | **Universal architectural foundation**: Real MIPS processors divide 4GB address space into distinct unmapped/cached, unmapped/uncached, and mapped segments. |
| CP0 Registers (Missing) | `Index` (0), `Random` (1), `EntryLo0/1` (2/3), `Context` (4), `PageMask` (5), `Wired` (6), `BadVAddr` (8), `Count` (9), `EntryHi` (10), `Compare` (11), `PRId` (15), `Config0-3` (16), `EBase` (15, sel 1) | MD00090 Rev 0.95, Chapter 6, pp. 37–72 | **Universal for OS kernels**: Hardware interface for timer interrupts, page table walking, TLB refill, and CPU identification. |

### 3.11 Cache Operations & Memory Prefetching
| Mnemonic | Instruction Name | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `cache op, offset(rs)` | Perform Cache Operation | MD00086 Rev 2.50, §3.2, Table 3-23, p. 31, 100 | **OS / Bootloader only**: Flushes, invalidates, or locks L1/L2 data and instruction caches. Never appears in textbook or user-space assembly. |
| `pref hint, offset(rs)` | Prefetch Data | MD00086 Rev 2.50, §3.2, Table 3-4, p. 25, 238 | **Moderate in compiled code**: Non-blocking data cache prefetching generated by optimizing compilers (`gcc -O3`). |
| `prefx hint, index(base)` | Prefetch Indexed | MD00086 Rev 2.50, §3.2, Table 3-15, p. 30, 241 | **Uncommon**: Array indexed prefetch (requires FPU Cop1X extension). |

### 3.12 Miscellaneous & Co-Processor Extensions
| Mnemonic / Feature | Description | Primary Source Citation | Commonality Assessment |
|---|---|---|---|
| `rdhwr rt, rd` | Read Hardware Register | MD00086 Rev 2.50, §3.2, Table 3-7, p. 27, 242 (MIPS32r2) | **Common in user-space Linux**: Allows unprivileged user code to read cycle counter (`CPUNum`, `SYNCI_Step`, `CC`, `CCRes`, TLS thread pointer). |
| `ssnop` | Superscalar No Operation | MD00086 Rev 2.50, §3.2, Table 3-3, p. 25, 275 | **Uncommon**: Assembly pipeline hazard clearance. |
| `sdbbp` / `deret` | EJTAG Debug Breakpoint / Debug Return | MD00086 Rev 2.50, §3.2, Table 3-24, p. 32, 123, 254 | **Hardware Debugger only**: Used by JTAG debug probes (GDB stubs). |
| Coprocessor 2 (`cop2`, `lwc2`, `swc2`, `mfc2`, etc.) | Vendor-Defined Coprocessor Interface | MD00086 Rev 2.50, §3.2, Tables 3-18–3-22, pp. 30–31 | **Vendor-specific**: Reserved for custom ASIC accelerators; unused in generic MIPS code. |

---

## 4. Confirmed Out-of-Scope Architecture Extensions

The following MIPS extensions exist in official standards but are explicitly excluded from Semantic MIPS because this project deliberately specifies a **32-bit single-issue scalar MIPS32 core**:
- **MIPS64 Architecture**: 64-bit integer registers, 64-bit address space, and doubleword operations (`dadd`, `dsub`, `dsll`, `dsra`, `ld`, `sd`, `dmult`, `ddiv`) (Primary Source: *MIPS64 Architecture For Programmers Volume II: The MIPS64 Instruction Set*, Document MD00087).
- **MIPS DSP Application-Specific Extension (ASE)**: Vector-like fixed-point arithmetic, saturating add/sub, and dual 16-bit / quad 8-bit SIMD math (Primary Source: *MIPS Architecture for Programmers Volume IV-e: The MIPS DSP Application-Specific Extension*, Document MD00374).
- **MIPS SIMD Architecture (MSA)**: 128-bit vector execution unit with 32 vector registers for packed integer and floating-point SIMD (Primary Source: *MIPS Architecture for Programmers Volume IV-j: The MIPS SIMD Architecture Module*, Document MD00866).

---

## 5. Recommended Top 5 Additions for Semantic MIPS

Based on prevalence in real-world compiled C binaries, standard library routines, and textbook educational programs (rather than implementation difficulty), the top 5 highest-priority additions are:

1. **`jr` and `jalr` (Register-Indirect Jumps)**
   - *Rationale*: Their complete absence is currently the single most conspicuous gap in Semantic MIPS. Function returns (`jr $ra`), switch jump tables, dynamic linking, and C function pointers cannot execute without them.
   - *Implementation surface*: Trivial modification to `step` (sets `PC_target = state.readReg(rs)`, subject to existing branch delay slot logic).
2. **`mul rd, rs, rt` (3-Operand GPR Multiply)**
   - *Rationale*: Modern compilers virtually never emit the 2-operand `mult` + `mflo` sequence for standard 32-bit arithmetic; they emit `mul rd, rs, rt` to avoid pipeline stalls and preserve HI/LO.
   - *Implementation surface*: Straightforward R-type (SPECIAL2) operation computing `(rs.toNat * rt.toNat) % 2^32`.
3. **`sllv`, `srlv`, and `srav` (Variable Shifts)**
   - *Rationale*: Essential for any C code performing variable shifts (`x << y`). Currently, Semantic MIPS can only shift by static immediate amounts.
   - *Implementation surface*: R-type ALU operation masking low 5 bits of `$rs` as shift amount.
4. **`bltz` and `bgez` (Branch on `< 0` and `>= 0`)**
   - *Rationale*: Common conditional branches used in sign testing and loop conditions (`for (i = n; i >= 0; i--)`). Completes the fundamental conditional branch family alongside `beq`, `bne`, `blez`, `bgtz`.
   - *Implementation surface*: Standard REGIMM opcode with delay slot handling identical to existing branches.
5. **`ll` and `sc` (Load Linked / Store Conditional)**
   - *Rationale*: The quintessential MIPS synchronization mechanism taught in Patterson & Hennessy and required for all concurrent / lock-free algorithms.
   - *Implementation surface*: Requires adding a 1-bit `llBit : Bool` and optional `llAddr : W32` to processor `State`.

---

## 6. Sources

Every claim and instruction specification in this document is cited against authoritative primary vendor manuals:

| Source Document | Document ID / Revision | Publisher & Date | Verified Sections / Content | Access Date |
|---|---|---|---|---|
| *MIPS32® Architecture For Programmers Volume I: Introduction to the MIPS32® Architecture* | MD00082, Rev 0.95 & Rev 2.50 | MIPS Technologies, Inc. (2001, 2005) | §2.5 Instruction lists (Table 2-1), §4 CPU instruction formats, §5 FPU data types & registers | 2026-11-01 |
| *MIPS32® Architecture For Programmers Volume II: The MIPS32® Instruction Set* | MD00086, Rev 2.50 | MIPS Technologies, Inc., July 1, 2005 | §3.1 Subsetting rules, §3.2 Instruction Tables (Tables 3-1 through 3-24, pp. 24–32), Individual instruction pages (pp. 33–322) | 2026-11-01 |
| *MIPS® Architecture for Programmers Volume II-A: The MIPS32® Instruction Set Manual* | MD00086, Rev 6.04 | Imagination Technologies LTD., Nov 13, 2015 | Release 6 changes: removal of branch likely, removal of HI/LO and 2-operand mult/div, removal of unaligned load/store (`lwl`/`lwr`), compact branches | 2026-11-01 |
| *MIPS32™ Architecture For Programmers Volume III: The MIPS32™ Privileged Resource Architecture* | MD00090, Rev 0.95 & Rev 2.50 | MIPS Technologies, Inc. (2001, 2005) | Chapter 3 Operating Modes, Chapter 4 Virtual Memory & Segments, Chapter 5 Exceptions, Chapter 6 CP0 Registers (Index, Status, Cause, EPC, EntryHi/Lo, TLB) | 2026-11-01 |
| *Semantic MIPS Repository Source Files* | Git Worktree (`/home/barracuda/Desktop/semantic-mips`) | Semantic MIPS Project | `Semantics/Instruction.lean`, `Semantics/Step.lean`, `Semantics/Specs/StepSpec.lean`, `docs/spec/INSTRUCTION-REF.md`, `docs/spec/SPEC-NOTES.md` | 2026-11-01 |
