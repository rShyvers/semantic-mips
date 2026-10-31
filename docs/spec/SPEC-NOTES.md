# MIPS semantics — pinned conventions (seed for Lean spec S)

**The target is the MIPS language.** The Lean small-step semantics specifies
what MIPS programs mean. **MARS 4.5 is a test environment**: an executable
oracle we run MIPS programs in and differentially compare against.

Where MARS's behavior matches the MIPS architecture, it confirms our spec.
Where it deviates, **the language wins** and the deviation is listed in
§9. Facts below are sourced from the vendored MARS 4.5 source in
[`vendor/mars-src/`](../../vendor/mars-src/) (MIT license) and MARS's own help
files; per-instruction semantics live in
[`INSTRUCTION-REF.md`](INSTRUCTION-REF.md).

## 1. Memory map (default / SPIM-based configuration)

Source: `vendor/mars-src/mars/mips/hardware/MemoryConfigurations.java` (lines 79–96).

| Region | Address |
|---|---|
| `.text` base (first instruction) | `0x00400000` |
| data segment base | `0x10000000` |
| `.extern` base | `0x10000000` |
| global pointer `$gp` | `0x10008000` |
| `.data` base | `0x10010000` |
| heap base (sbrk) | `0x10040000` |
| stack pointer `$sp` initial value | `0x7fffeffc` |
| stack base (top of user space) | `0x7ffffffc` |
| highest user-space address | `0x7fffffff` |
| kernel space starts at | `0x80000000` |

Memory is byte-addressable; the whole range `0x00000000–0xffffffff` is
addressable. Note: `$sp = 0x7fffeffc` comes from SPIM, not classic MIPS —
do not "fix" it to `0x1000ffff`.

## 2. Registers

Source: `vendor/mars-src/mars/mips/hardware/RegisterFile.java`.

- 32 general-purpose registers, 32-bit bit patterns.
- `$zero` is hardwired: reads return 0, writes are silently ignored
  (`RegisterFile.java`, "you can not change the value of the zero register").
- `$sp` (register 29) initialized to `Memory.stackPointer` = `0x7fffeffc`.
- All other registers start at 0.
- `mult`/`div` use a separate 64-bit `hi,lo` pair (see `Instruction.java`).

## 3. Execution conventions

Source: `vendor/mars-src/mars/simulator/Simulator.java`,
`vendor/mars-src/mars/Settings.java`.

- **No branch delay slots by default.** `DelayedBranching` setting defaults to
  `false` (`Settings.java`, index 8 of `defaultBooleanSettingsValues`). A taken
  branch/jump updates PC to the target immediately; the "next" instruction is
  the one at the target. (MARS can model delay slots if the user enables the
  setting — out of scope for our spec.)
- **Execution starts at the `.text` base** (`0x400000`), not at `main`:
  `StartAtMain` defaults to `false`.
- PC fetches must be word-aligned; instruction fetch reads a 32-bit big-endian
  word from memory.
- Program halts on: `exit`/`exit2` syscall, illegal/unimplemented instruction,
  address error (out of range or misaligned), or step limit.

## 4. Alignment and errors

Source: `vendor/mars-src/mars/mips/hardware/Memory.java`.

- Word access (`lw`, `sw`, fetch): address must be a multiple of 4, else
  `AddressErrorException` ("not aligned on word boundary").
- Halfword access (`lh`, `lhu`, `sh`): multiple of 2.
- Byte access: no alignment requirement.
- In our semantics these become a defined halt (error) outcome of `step`, not
  an undefined behavior.

## 5. Syscalls

Source: `vendor/mars-src/Syscall.properties`,
`vendor/mars-src/help/SyscallHelp.html`, and the classes in
`vendor/mars-src/mars/mips/instructions/syscalls/`.

Full MARS table (number → name): 1 PrintInt, 2 PrintFloat, 3 PrintDouble,
4 PrintString, 5 ReadInt, 6 ReadFloat, 7 ReadDouble, 8 ReadString, 9 Sbrk,
10 Exit, 11 PrintChar, 12 ReadChar, 13 Open, 14 Read, 15 Write, 16 Close,
17 Exit2, 30 Time, 31 MidiOut, 32 Sleep, 33 MidiOutSync, 34 PrintIntHex,
35 PrintIntBinary, 36 PrintIntUnsigned, 40 RandSeed, 41 RandInt,
42 RandIntRange, 43 RandFloat, 44 RandDouble, 50–59 dialogs.

**v1 scope: syscalls 1 (print int), 4 (print string, null-terminated from
memory), 10 (exit), 11 (print char).** Argument convention: `$v0` = syscall
number, `$a0` (+ `$a1`, …) = arguments.

## 6. Instruction set (v1 scope)

Core subset (~20 instructions); full MARS list is in
`vendor/mars-src/help/mipsref.pdf` (MIPS/SPIM reference card) and the
pseudo-op expansions in `vendor/mars-src/PseudoOps.txt`.

- R-type: `add addu sub subu and or xor nor sll srl sra slt sltu`
  plus `mult multu div divu mflo mfhi`
- I-type: `addi addiu slti sltiu andi ori xori lui`
  loads/stores: `lw sw lb lbu lh lhu sh`
- J-type / branches: `j jal beq bne blez bgtz`

Pseudo-instructions (`li`, `la`, `move`, `nop`, …) are assembler sugar; our
Lean assembler expands them using the table in `PseudoOps.txt`. They are not
part of the machine-level semantics.

## 7. Endianness and data representation

Our language (the spec target) follows the classic MIPS big-endian
convention. **MARS itself defaults to little-endian** — see §9 item 4 for
the correction to an earlier (incorrect) "big-endian throughout" claim here;
that was a misreading of `Memory.java`. Integers are two's complement;
arithmetic instructions operate on bit patterns with defined wraparound
(`addu`, `subu`) or the MARS-documented behavior for signed variants —
per-instruction details are pinned in Lean spec S against `Instruction.java`.

## 8. What is trusted / not

- **Spec target:** the MIPS language (educational dialect, §9). Our Lean
  semantics is proven against the written spec S.
- **Empirical oracle:** MARS 4.5 — we run programs in it and compare outputs.
  Agreement on the faithful region (§9) validates our implementation; it does
  not define the spec.
- **Not in v1 scope:** macros, exception handler loading, kernel space,
  coprocessors, floating point, delay slots (see §9).

## 9. Divergence list (language vs MARS)

Places where MARS's behavior differs from the plain MIPS architecture, and
the decision for our semantics:

1. **Branch delay slots: OUT OF SCOPE (dialect choice).** Real MIPS executes
   the instruction after a branch in a delay slot; MARS's default configuration
   does not (`DelayedBranching=false`). Our semantics models the no-delay-slot
   educational dialect (same as SPIM). Documented, not hidden.
2. **`div`/`divu` by zero: hi/lo unchanged, no trap.** The MIPS32 spec is
   read (by MARS itself, with an explicit source comment) as "no arithmetic
   exception under any circumstances"; COD3 textbooks say "divide with
   overflow". We follow the no-trap reading — also forced by v1 having no
   exception-handler mechanism.
3. **`lw`/`sw` offset sign-extension: MARS latent bug, we follow the ISA.**
   MARS uses the raw 16-bit I-format offset without sign extension for
   `lw`/`sw` (defensive re-extension exists in `lb`/`lh`/`sh`/`addi`/`slti`
   but not there). Invisible for assembler-built programs; would zero-extend
   negative offsets on raw binary input. Our semantics sign-extends per the
   ISA. Differential corpus is assembler-built, so MARS still matches;
   this deviation is documented as a found defect in the test environment.
4. **Endianness: MARS 4.5 headless defaults to LITTLE-ENDIAN memory
   storage; we follow the classic MIPS big-endian convention (ISA truth).**
   `vendor/mars-src/mars/mips/hardware/Memory.java:90`:
   `private static boolean byteOrder = LITTLE_ENDIAN;`. `setByteOrder`
   (line 328) exists but is never called anywhere in this source tree, so
   there is no CLI/GUI override available in headless MARS — every run
   observes little-endian memory. An earlier version of §7 above claimed
   MARS was "big-endian throughout"; that was a misreading of this file and
   has been corrected. Consequence for differential testing: byte-order-
   sensitive probes (e.g. `lb` at offset 0 of a `.word`-declared value) will
   diverge between MARS and our big-endian spec *by design*, not due to a
   bug in either. The differential corpus must stick to endian-invariant
   access patterns — `lw`/`sw` round-trips (store and reload a word through
   the same-width access), and sequential `.byte`/`.asciiz` data accessed
   byte-by-byte — which produce identical observable results under either
   byte order.
