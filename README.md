# Semantic MIPS

A small-step operational semantics of a v1 educational MIPS dialect, written
and proved in Lean 4, differentially validated against the real MARS 4.5
simulator.

Extracted from [VibeCheck](https://github.com/rShyvers/VibeCheck) (a
hackathon project that builds a consumer product on top of this semantics)
so the semantics can be read, built, and reviewed on their own, with no
dependency on anything else in that project.

## What this is

- `MipsSim/Step.lean`'s `step : Program → State → StepResult` is a **total,
  one-instruction transition function**: fetch, decode, execute exactly one
  instruction, and either produce the next `State` or halt with a reason.
  That one-step relation *is* the semantics; `run` (same file) is nothing
  more than `step` iterated with a fuel bound, built strictly on top of it.
- `MipsSim/Specs/StepSpec.lean` is a human-readable specification of `step`:
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

Scope (v1 dialect): ~24 machine instructions (R-type arith/logic/shifts,
mult/div, I-type immediates, byte/halfword/word memory, branches, j/jal),
syscalls 1/4/10/11. No delay slots, no exception handlers beyond halting, no
floats/coprocessors. See `DESIGN.md` for the module map and
`docs/spec/INSTRUCTION-REF.md` + `docs/spec/SPEC-NOTES.md` for the ground
truth this implementation is built against (human-written, sourced to real
MARS 4.5 behavior).

## Trust chain

The MIPS language spec lives in `docs/spec/` (`INSTRUCTION-REF.md` and
`SPEC-NOTES.md`), human-written and sourced to the real MARS 4.5 simulator's
behavior. `step` (`MipsSim/Step.lean`) is the Lean implementation of that
spec. The spec's key claims are kernel-checked theorems
(`MipsSim/Specs/StepSpec.lean`), judged by `lake comparator` against a
trusted statement file (`comparator.json`), and the whole semantics is
differentially validated against real MARS 4.5 on a 12-program corpus
(`DiffHarness`, `tests/corpus/`).

**What's trusted, explicitly:**
- Lean 4.35.0 + its kernel, and the three axioms it treats as standard:
  `propext`, `Classical.choice`, `Quot.sound`.
- `docs/spec/*.md` as an accurate account of MARS 4.5's behavior (human-written,
  not derived from the implementation).
- The real MARS 4.5 jar (`vendor/mars/Mars4_5.jar`) as ground truth for the
  differential harness.
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
  `MipsSim/Specs/StepSpec.lean`, which mixes finished and (honestly
  documented) unfinished proofs.

### Current status

- **`lake comparator`: green.** Trusted surface (8 of the spec's theorems —
  one from each kind of claim the spec makes):
  `add_spec_raw`, `sub_spec_raw` (arithmetic + signed-overflow trapping),
  `div_by_zero_spec` (division edge case), `beq_taken_spec` (branching),
  `jal_sets_ra` (jump-and-link), `lw_spec_raw` (memory load),
  `add_overflow_not_wrapped` (bad-output rejection: overflow halts, never
  silently wraps), `zero_write_not_observable` (the `$zero`-register
  invariant, closed form).
- **`lake check`: green**, over the `Checked` library (`Checked.lean`): the
  sorry-free subset of the project — `Word`, `Types`, `State`, `Instruction`,
  `Asm`, `Step`, and their unit tests — plus `DiffHarness`. `MipsSim.Specs.StepSpec`
  (the spec file) is excluded from this target by design (see below) but is
  still built by `lake build MipsSim` and still checked, theorem-by-theorem,
  by `lake comparator` above.

### Open items: 3 documented `sorry`s

All three are in `MipsSim/Specs/StepSpec.lean`, each with a closed, weaker
version proved instead and a concrete `#guard`-checked example — see that
file's "STALL NOTE" comments for the exact mechanism they stall on:

1. **`step_preserves_zero_register`** — "`$zero` always reads `0` after any
   instruction," for all 24 instruction kinds at once. Closed substitute:
   `step_add_preserves_zero_register` (the representative hard case) plus a
   fully generic, closed proof for every instruction without memory access,
   branching, or jumping.
2. **`syscall1_spec`** — "syscall 1 prints `$a0`'s signed decimal value."
   Closed substitute: a `#guard` on a concrete starting state.
3. **`syscall10_spec`** — "syscall 10 halts cleanly." Closed substitute: a
   `#guard` on a concrete starting state.

## Building

```sh
lake exe cache get   # fetch the mathlib build cache (don't build it from source)
lake build           # builds the default targets: Checked, DiffHarness
lake check           # kernel-replay gate
lake comparator       # trusted-theorem gate (comparator.json)
lake exe DiffHarness  # differential test vs real MARS 4.5 on tests/corpus/
```

Requires Lean/Lake via `elan` (toolchain pinned in `lean-toolchain`,
currently `leanprover/lean4:v4.35.0`) and a JRE on `PATH` for
`lake exe DiffHarness` (it shells out to `java -jar vendor/mars/Mars4_5.jar`).

## Layout

```
lakefile.toml, lean-toolchain, lake-manifest.json   — Lean project files
Checked.lean           — sorry-free default-target root (see its header)
comparator.json        — trusted-theorem config for `lake comparator`
MipsSim/Word.lean       — W32 bit-level helpers
MipsSim/Types.lean      — Program, State, HaltReason, StepResult
MipsSim/State.lean      — register/memory operations on State
MipsSim/Instruction.lean — Instruction enum, decode/encode
MipsSim/Asm.lean        — assembler (v1 source text → Program)
MipsSim/Step.lean       — step (the semantics) + run (fuel-bounded iteration)
MipsSim/Specs/StepSpec.lean — the reviewable specification + proofs
DiffHarness.lean        — differential-testing executable (Step vs MARS)
tests/corpus/           — .asm programs used by DiffHarness
docs/spec/              — human-written MIPS spec (ground truth for `step`)
vendor/mars/            — real MARS 4.5 jar, used only by DiffHarness
DESIGN.md               — module map, dependency graph, build waves
```

## License / provenance

MARS 4.5 (`vendor/mars/Mars4_5.jar`) is a third-party simulator, vendored
here only as a differential-testing oracle; see its own license. Everything
else in this repository was written for this project.
