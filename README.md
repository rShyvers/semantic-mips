# Semantic MIPS

A small-step operational semantics of the real MIPS32 architecture, written
and proved in Lean 4, differentially validated against the real MARS 4.5
simulator.

Extracted from [VibeCheck](https://github.com/rShyvers/VibeCheck) (a
hackathon project that builds a consumer product on top of this semantics)
so the semantics can be read, built, and reviewed on their own, with no
dependency on anything else in that project.

## What this is

- `Semantics/Step.lean`'s `step : Program → State → StepResult` is a **total,
  one-instruction transition function**: fetch, decode, execute exactly one
  instruction, and either produce the next `State` or halt with a reason.
  That one-step relation *is* the semantics; `run` (same file) is nothing
  more than `step` iterated with a fuel bound, built strictly on top of it.
- `Semantics/Specs/StepSpec.lean` is a human-readable specification of `step`:
  one theorem per semantically important behavior (arithmetic + overflow,
  branches, jumps, memory, the `$zero`-register rule), each citing the
  instruction-reference section it encodes, plus bad-output rejections
  (`¬ Spec input badOutput` for known-wrong behaviors) and concrete
  satisfiable examples.
- `DiffHarness.lean` is an executable that runs every program in
  `tests/corpus/` through both this semantics and real MARS 4.5
  (`vendor/mars/Mars4_5.jar`) and compares the outputs — the check that the
  Lean model is the system it claims to model, not just an internally
  consistent one.
- `EquivHarness.lean` is a second executable, with a different job: it runs
  pairs of our own `tests/equiv/` programs (a direct-instruction "base" and a
  bit-shift/bitwise "variant" computing the same arithmetic) through this
  semantics only, no MARS, and checks whether they agree. See "Equivalence
  corpus" below.
- `MipsRun.lean` is a third executable: a thin CLI wrapper (no new
  semantics) that assembles and runs an arbitrary `.asm` program and prints
  one JSON object describing the outcome (assembled/halted/halt reason/step
  count/output/final registers). Built for VibeCheck's interactive demo —
  paste MIPS assembly into a web page, see what the verified semantics does
  with it.

## Scope: the real MIPS32 architecture, not a MARS clone

This project's priority is the **real MIPS32 instruction set architecture**
(MIPS32 Architecture For Programmers, Vol I–III — MD00082/MD00086/MD00090),
not MARS-specific behavior. MARS 4.5 is used only as a differential-testing
oracle; where its behavior diverges from the real architecture, the
architecture wins (see `docs/spec/SPEC-NOTES.md` §9 for the full divergence
list — real one-instruction branch delay slots instead of MARS's default
no-delay-slot config is the biggest one).

Current coverage, grounded in real MIPS32 semantics and citations (MD00086
§3.2 per-instruction, unless noted):

- **Full core integer ISA**: R-type arith/logic/shift/compare/conditional
  move, variable shifts, rotate, bitfield extract/insert, byte/halfword
  swap, I-type immediates, all memory widths including classic unaligned
  `lwl`/`lwr`/`swl`/`swr`, multiply/divide + the HI/LO register pair,
  multiply-accumulate (`madd`/`maddu`/`msub`/`msubu`), the atomic
  `ll`/`sc` primitive.
- **Full branch/jump family, with real delay slots**: `beq`/`bne`/`blez`/
  `bgtz`, the REGIMM zero-comparison family (`bltz`/`bgez`/`bltzal`/
  `bgezal`), `j`/`jal`, and register-indirect `jr`/`jalr`. Every one gets
  the architecturally-mandated one-instruction delay slot — the instruction
  immediately following a branch/jump always executes before control
  transfers, modeled via `State.pendingBranch`.
- **Traps/exceptions**: register-register and immediate-operand trap
  families (`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu` and their `i`-suffixed
  immediate siblings), `break`, `syscall`, and a minimal real
  exception-vector model (coprocessor-0 `Status`/`Cause`/`EPC`, jump to
  `0x80000180`) with `mfc0`/`mtc0`/`eret`/`wait`.
- **Floating point (coprocessor 1, single-precision)**: raw GPR↔FPR moves,
  memory load/store, the four basic arithmetic operations, `sqrt`/`abs`/
  `neg`, four directed-rounding-to-integer instructions, 10 of 16 IEEE-754
  compare predicates, and the FP-conditional branches `bc1t`/`bc1f` (with
  real delay slots, same as every other branch). Double precision is out of
  scope for now.

See [`docs/spec/MIPS-COVERAGE-GAPS.md`](docs/spec/MIPS-COVERAGE-GAPS.md)
for a cited, categorized inventory of what's *not* yet covered (branch
likely, `sync`/`synci`, double-precision FP, the full privileged/TLB
architecture, cache operations) and why each gap is prioritized the way it
is — grounded in real-world instruction commonality, not implementation
difficulty.

Deliberately, permanently out of scope: MIPS64, the DSP ASE, and MSA SIMD
(this project is a 32-bit, single-issue scalar core); full TLB/virtual
memory and privileged-mode execution (kernel territory, a different
project).

## Equivalence corpus (`tests/equiv/`, `EquivHarness.lean`)

The original plan was to unseal a real hand-written MIPS program, find a
math bug in it with this semantics, and prove a fix. That program needs
assembler macros, which `docs/spec/SPEC-NOTES.md` §9 puts explicitly out of
scope -- `Asm.lean` can't even assemble it. In its place: a small corpus we
wrote ourselves, built around the same idea (use the semantics to catch a
real arithmetic bug), but self-contained.

Each pair is two `tests/equiv/*.asm` programs that are supposed to compute
the same function: one using a direct instruction (`mult`, `div`, `sub`),
the other using bit-shifting/bitwise instructions instead -- the kind of
strength-reduction a compiler or a hand-optimizing assembly programmer would
do. Two of the seven comparisons are **deliberately wrong** -- the classic
"replace division/remainder by a power of two with a raw shift/bitmask" bug,
which breaks on negative dividends -- specifically so the corpus has to
catch a real divergence, not just confirm agreement everywhere:

| Case | Base | Variant | Claim |
|---|---|---|---|
| `mul_pow2` | `mult`/`mflo` (x * 8) | `sll` by 3 | equivalent, every input |
| `mul_const5` | `mult`/`mflo` (x * 5) | `sll`+`addu` ((x<<2)+x) | equivalent, every input |
| `div_pow2_buggy` | `div`/`mflo` (/4) | plain `sra` by 2 | **wrong**: rounds toward negative infinity, not zero |
| `div_pow2_correct` | `div`/`mflo` (/4) | bias-corrected `sra` | equivalent, every input |
| `mod_pow2_buggy` | `div`/`mfhi` (%4) | plain `andi` mask | **wrong**: always non-negative |
| `mod_pow2_correct` | `div`/`mfhi` (%4) | `a0 - quotient*4` | equivalent, every input |
| `sub_twos_complement` | `subu` | `nor`+`addiu`+`addu` | equivalent, every input |

**Why no MARS here:** `DiffHarness` answers "is this semantics the same
language as the real simulator?", which needs an external oracle (real
MARS). `EquivHarness` answers "do these two already-validated programs
compute the same function?", a question entirely internal to the semantics
-- so it runs both programs directly through our own `assemble`/`run`, no
subprocess, no JVM, no per-case compilation. This is the "thin interpreter"
approach: the semantics itself is the fast, native execution engine, and
MARS is reserved for the one question that actually needs an external
oracle.

Run it with `lake exe EquivHarness`; exit code `0` iff every case's actual
outcome (equivalent, or diverges) matches what it claims. Each pair's own
`.asm` header comment explains the specific claim and, for the buggy ones,
the exact arithmetic reason it's wrong.

## Trust chain

The MIPS language spec lives in `docs/spec/` — `INSTRUCTION-REF.md` is the
per-instruction ground truth, `SPEC-NOTES.md` pins conventions and the
language-vs-MARS divergence list, `MIPS-COVERAGE-GAPS.md` is the cited
gap-analysis against the real architecture. `step` (`Semantics/Step.lean`)
is the Lean implementation of that spec. The spec's key claims are
kernel-checked theorems (`Semantics/Specs/StepSpec.lean`), judged by
`lake comparator` against a trusted statement file (`comparator.json`), and
the core semantics is differentially validated against real MARS 4.5 on a
12-program corpus (`DiffHarness`, `tests/corpus/`).

**What's trusted, explicitly:**
- Lean 4.35.0 + its kernel, and the three axioms it treats as standard:
  `propext`, `Classical.choice`, `Quot.sound`.
- `docs/spec/*.md` as an accurate account of the real MIPS32 architecture
  (and, for the parts sourced to it, MARS 4.5's behavior) — human-written,
  not derived from the implementation.
- The real MARS 4.5 jar (`vendor/mars/Mars4_5.jar`) as ground truth for the
  differential harness (covers the original v1 instruction subset; later
  additions grounded directly in the MIPS32 ISA manuals are not all
  independently differentially tested against MARS).
- Nothing else: no `sorry` reaches either verification gate below, no
  `axiom`, no `native_decide`, no `partial def`.

## Verification gates

Two gates decide whether a proof counts as "done" (see the parent project's
`CLAUDE.md` for the full rationale):

- **`lake check`** rebuilds this project's default target (`Checked`,
  `DiffHarness`) and replays the result through Lean's own kernel, failing on
  any axiom beyond the three standard ones. It is all-or-nothing: one
  unfinished proof anywhere in the target fails the whole gate.
- **`lake comparator`** checks a named list of theorems
  (`comparator.json`) against an explicit per-theorem axiom allowlist. Unlike
  `lake check`, it works theorem-by-theorem, so it is the right tool for
  `Semantics/Specs/StepSpec.lean`, which mixes finished and (honestly
  documented) unfinished proofs.

### Current status

- **`lake comparator`: green.** Trusted surface (8 of the spec's theorems —
  one from each kind of claim the spec makes, kept deliberately small —
  see CLAUDE.md §4 on keeping a trusted surface short and reviewable):
  `add_spec_raw`, `sub_spec_raw` (arithmetic + signed-overflow trapping),
  `div_by_zero_spec` (division edge case), `beq_taken_spec` (branching),
  `jal_sets_ra` (jump-and-link), `lw_spec_raw` (memory load),
  `add_overflow_not_wrapped` (bad-output rejection: overflow halts, never
  silently wraps), `zero_write_not_observable` (the `$zero`-register
  invariant, closed form).
- **`lake check`: green**, over the `Checked` library (`Checked.lean`): the
  sorry-free subset of the project — `Word`, `Types`, `State`, `Instruction`,
  `Asm`, `Step`, and their unit tests — plus `DiffHarness`. `Semantics.Specs.StepSpec`
  (the spec file) is excluded from this target by design (see below) but is
  still built by `lake build Semantics` and still checked, theorem-by-theorem,
  by `lake comparator` above.
- **Proof coverage**: 123 implemented instruction variants; 145 theorems
  in `StepSpec.lean`, covering 85 of those 123 instructions with at least
  one `_spec_raw`-style theorem (every proven theorem independently
  verified to use only the three permitted axioms, or none). The remaining
  38 — mostly floating-point, bit-manipulation, and immediate-trap
  instructions that landed in later ISA-expansion passes — are implemented
  and tested (`#guard`/`example` unit tests in their own module) but don't
  yet have a formal `StepSpec.lean` theorem; that gap is tracked as
  ongoing work, not hidden.

### Open items: 4 documented `sorry`s

All four are in `Semantics/Specs/StepSpec.lean`, each with a closed,
weaker version proved instead and/or a concrete `#guard`-checked example —
see that file's "STALL NOTE" comments for the exact mechanism each stalls
on, including what was tried and why it didn't close:

1. **`step_preserves_zero_register`** — "`$zero` always reads `0` after any
   instruction," for every instruction kind at once. Closed substitute:
   `step_preserves_zero_register_nontrivial`, the same claim closed for
   every instruction that has a `_spec_raw` theorem (around 70 of 123),
   dispatching case-by-case and proving each via that instruction's own
   equation plus `writeReg_preserves_zero_slot`. Its own trailing case for
   the remaining ~40 instructions (no `_spec_raw` theorem to dispatch to
   yet) is the second, narrower documented `sorry`.
2. **`syscall1_spec`** — "syscall 1 prints `$a0`'s signed decimal value."
   Genuinely stalled on a chicken-and-egg: the hypothesis pinning the
   syscall number can't be used to reduce `step`'s private dispatch match
   until that match is exposed by unfolding, but exposing it requires a
   whole-term `rfl`, which doesn't consult hypotheses. (A prior version of
   this theorem was additionally missing a `pendingBranch = none`
   hypothesis every other `mkNext`-based theorem carries, making it false
   as literally stated for some inputs — found via a concrete
   counterexample, fixed; the statement is correct now, still `sorry`'d for
   the unfolding reason above.) Closed substitute: a `#guard` on a
   concrete, well-formed starting state.
3. **`syscall10_spec`** — "syscall 10 halts cleanly." Same stall mechanism
   as `syscall1_spec`. Closed substitute: a `#guard` on a concrete state.

## Building

```sh
lake exe cache get   # fetch the mathlib build cache (don't build it from source)
lake build           # builds the default targets: Checked, DiffHarness
lake check           # kernel-replay gate
lake comparator       # trusted-theorem gate (comparator.json)
lake exe DiffHarness  # differential test vs real MARS 4.5 on tests/corpus/
lake exe EquivHarness # arithmetic equivalence corpus, no MARS, on tests/equiv/
lake build MipsRun && lake exe MipsRun prog.asm   # assemble+run, print JSON verdict
```

Requires Lean/Lake via `elan` (toolchain pinned in `lean-toolchain`,
currently `leanprover/lean4:v4.35.0`) and a JRE on `PATH` for
`lake exe DiffHarness` (it shells out to `java -jar vendor/mars/Mars4_5.jar`).
`MipsRun` is deliberately not in `defaultTargets` — Lake can't combine two
default-target executables that each define `main` into one `lake check`
environment — so build it explicitly with `lake build MipsRun`.

## Layout

```
lakefile.toml, lean-toolchain, lake-manifest.json   — Lean project files
Checked.lean            — sorry-free default-target root (see its header)
comparator.json         — trusted-theorem config for `lake comparator`
Semantics/Word.lean            — W32 bit-level helpers
Semantics/Types.lean           — Program, State, HaltReason, StepResult
Semantics/State.lean           — register/memory operations on State
Semantics/Instruction.lean     — Instruction enum, decode/encode
Semantics/Asm.lean             — assembler (source text → Program)
Semantics/Step.lean            — step (the semantics) + run (fuel-bounded iteration)
Semantics/Specs/StepSpec.lean  — the reviewable specification + proofs
DiffHarness.lean        — differential-testing executable (Step vs MARS)
tests/corpus/           — .asm programs used by DiffHarness
EquivHarness.lean       — arithmetic equivalence-corpus executable (no MARS)
tests/equiv/            — .asm program pairs used by EquivHarness
MipsRun.lean            — thin assemble+run exe, JSON output, for VibeCheck's demo
docs/spec/INSTRUCTION-REF.md     — per-instruction ground truth
docs/spec/SPEC-NOTES.md          — pinned conventions, language-vs-MARS divergences
docs/spec/MIPS-COVERAGE-GAPS.md  — cited gap analysis vs. the real MIPS32 ISA
vendor/mars/            — real MARS 4.5 jar, used only by DiffHarness
DESIGN.md               — module map, dependency graph, build waves
```

## License / provenance

MARS 4.5 (`vendor/mars/Mars4_5.jar`) is a third-party simulator, vendored
here only as a differential-testing oracle; see its own license. Everything
else in this repository was written for this project.
