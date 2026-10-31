# MipsSim — design & module contracts

Small-step semantics of MIPS (educational dialect, see `docs/spec/SPEC-NOTES.md` §9)
plus a differential harness against MARS. This file pins module boundaries and
interfaces so modules can be built in parallel without depending on each other.
Per-instruction ground truth: `docs/spec/INSTRUCTION-REF.md`.

## 1. Scope (v1)

- ~24 machine instructions: R-type arith/logic/shifts, mult/div family, I-type
  immediates, byte/halfword/word memory, j/jal/beq/bne/blez/bgtz.
- Syscalls 1, 4, 10, 11 (print int / print string / exit / print char).
- No delay slots, no exception handlers beyond halting, no floats/coprocessors.
- Dialect decisions and MARS divergences: SPEC-NOTES §9 (language wins).

## 2. Module map & dependency graph

```
Word ─┬─ Types ─┬─ State      (Wave 1, parallel)
      │         ├─ Instruction+Decode  (Wave 1, parallel)
      │         └─ Asm           (Wave 1, parallel)
      └──────────── Step (+Sim run loop)   (Wave 2, after Wave 1 merges)
                     DiffHarness exe       (Wave 3, after Step)
```

| File | Owns | Depends on |
|---|---|---|
| `MipsSim/Word.lean` | W32 type + bit-level helpers + tests | mathlib BitVec only |
| `MipsSim/Types.lean` | Program, State struct, HaltReason, StepResult, instruction-word constructors, environment constants + tests | Word |
| `MipsSim/State.lean` | hardware operations on State (init, reg read/write, mem read/write) + tests | Word, Types |
| `MipsSim/Instruction.lean` | `Instruction` enum, `decode`, `encode` + tests vs INSTRUCTION-REF encodings | Word, Types |
| `MipsSim/Asm.lean` | assembler: v1 subset source text → Program + golden tests | Word, Types |
| `MipsSim/Step.lean` | `step` (small-step semantics) + `Sim.run` loop + per-instruction unit tests | all of the above |
| `MipsSim/DiffHarness.lean` | exe: run corpus through Sim, spawn MARS, compare outputs | Step, Asm, IO |

Foundation = Word + Types (Wave 0: implemented by a worker against §3, reviewed
and committed by the orchestrator; **read-only for all subsequent workers**).
Wave 1 workers each own exactly one file and import only foundation. Wave 2 is a single writer (Step is the heart; no parallelism risk).

## 3. Foundation types (pinned)

```lean
-- Word.lean
abbrev W32 := BitVec 32
def signExt16 : W32 → W32          -- sign-extend low 16 bits to 32 (I-format immediates)
def asSigned  : W32 → Int          -- two's-complement interpretation
def ofInt32   : Int → W32          -- wrap into 32 bits
-- (+ any further bit helpers needed; each with a docstring and tests)

-- Types.lean
abbrev Program := Std.HashMap W32 W32        -- PC → instruction word
structure State where
  pc  : W32
  regs : Array W32                            -- size 32; index = register number
  hi  : W32
  lo  : W32
  mem : Std.HashMap W32 UInt8                 -- byte-addressable, sparse
  out : String                                -- accumulated syscall output
inductive HaltReason where
  | exit                          -- syscall 10/17
  | illegalInstruction (word : W32)
  | addressError (addr : W32)    -- out of range or misaligned
  | arithmeticOverflow           -- add/sub trap (no handler installed in v1)
inductive StepResult where
  | next (s : State)
  | halt (r : HaltReason)

-- instruction-word constructors (bit layouts per INSTRUCTION-REF summary table)
def mkRT : (rs rt rd shamt funct : W32) → W32   -- fields are 5/5/5/5/6 bits
def mkIT : (opcode rs rt imm : W32) → W32       -- 6/5/5/16 bits
def mkJT : (target : W32) → W32                 -- 26-bit target

-- environment constants (MARS default configuration; SPEC-NOTES §1)
def textBase : W32 := 0x00400000
def spInit   : W32 := 0x7fffeffc
```

`step` signature (implemented in Wave 2): `def step (p : Program) (s : State) : StepResult`.
Total function — halting is a value, not an exception. Syscall output accumulates
in `State.out`; `step` has no I/O.

## 4. Wave 1 interface contracts

### State.lean (worker B)
- `initialState (pc : W32) : State` — all regs 0 except `$sp := spInit`, pc as given, empty mem, empty out.
- `readReg (s : State) (i : Fin 32) : W32`
- `writeReg (s : State) (i : Fin 32) (v : W32) : State` — **silently ignores i == 0** ($zero rule).
- `fetchWord (p : Program) (pc : W32) : Option W32` — none if pc misaligned or absent.
- `readMemByte / readMemHalf / readMemWord : State → W32 → Option _` — none on misalignment; big-endian composition for half/word; absent bytes read as 0 (MARS memory is zero-filled).
- `writeMemByte / writeMemHalf / writeMemWord : State → W32 → _ → Option State` — none on misalignment.
- Tests: $zero write-ignore, sp init, endianness of half/word composition, alignment failures.

### Instruction.lean (worker C)
- `inductive Instruction` — one variant per v1 instruction with named fields
  (e.g. `.add {rs rt rd : W32}`, `.lw {rs rt imm : W32}` where imm is the RAW 16-bit
  field, `.beq {rs rt imm : W32}`, `.j {target : W32}` …). Field names/widths per
  INSTRUCTION-REF encodings.
- `decode (w : W32) : Option Instruction` — none for unimplemented opcodes/functs.
- `encode (i : Instruction) : W32` — inverse of decode on the v1 set.
- Tests: for every v1 instruction, a hand-computed word from INSTRUCTION-REF decodes
  to the expected variant; encode∘decode round-trips; unknown opcodes → none.

### Asm.lean (worker D)
- `assemble (src : String) : AsmResult` where `AsmResult = Except AsmError Program`.
- Supported: labels, `.text`, `.data`, `.word`, `.half`, `.byte`, `.asciiz`, `.space`,
  comments (`#`), all v1 real instructions, pseudo-ops `li`, `la`, `move`, `nop`.
- Layout rules per MARS/SPIM convention (SPEC-NOTES §1): code at `textBase`, data at
  the data-segment base; `.asciiz` null-terminated; word/half/byte alignment.
- Errors: unknown mnemonics, bad register names, undefined labels, bad immediates —
  each a distinct `AsmError` case (message + line number where feasible).
- Tests: golden programs (source → expected Program contents), including a `li` that
  needs the lui+addiu split, `.asciiz` byte layout, and one error case per AsmError.

## 5. Testing conventions (all modules)

- Unit tests live in the module file as `example ... := by decide` / `by rfl` plus
  `#guard cond` lines (CLAUDE.md §5). No separate test targets in v1.
- Build one module per edit: `lake build MipsSim.<Module>`. Never run two lake
  processes in the same checkout — parallel workers use git worktrees, not shared builds.
- `plausible` property tests arrive with the Step/Specs waves, not Wave 1.

## 6. Waves & gates

- **Wave 0:** worker implements Word.lean + Types.lean per §3 with tests;
  orchestrator reviews, runs the gate, commits.
- **Wave 1 (3 parallel workers, isolated worktrees):** State ∥ Instruction+Decode ∥ Asm.
  Gate: each worktree builds its module green with tests; orchestrator merges to main,
  full `lake build` green, then next wave.
- **Wave 2 (single worker):** Step.lean + Sim.run + per-instruction unit tests.
  Gate: all unit tests green; plausible on key invariants.
- **Wave 3 (parallel):** DiffHarness (exe vs MARS) ∥ Specs layer (spec S statements,
  satisfiable examples, bad-output rejections per CLAUDE.md §4).

## 7. Worker rules

- Foundation files (Word, Types) are READ-ONLY. If a foundation type is missing or
  wrong, report it in your final message; do not edit foundation or other modules.
- Edit only your assigned file. No edits under vendor/, docs/, or outside MipsSim/.
- No `sorry`, no `axiom`, no `set_option` tricks (CLAUDE.md §7).
- If stuck after real effort, report the exact goal state you're blocked on.
