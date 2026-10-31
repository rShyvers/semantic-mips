-- Root of the `Checked` library: the subset of `MipsSim` with **zero**
-- `sorry`s anywhere in its transitive closure. This is `lake check`'s
-- default target (see `lakefile.toml`), so `lake check` kernel-replays
-- exactly this code and fails on any non-standard axiom.
--
-- `MipsSim.Specs.StepSpec` is deliberately left out: it has 3 documented
-- `sorry`s (see its header and the "Verification gates" section of the
-- root README). `lake check` has no way to allow specific axioms for
-- specific theorems -- it is all-or-nothing for the whole target -- so a
-- file with any `sorry` at all would fail the whole gate. The 8 StepSpec
-- theorems people should actually trust are checked a different way, one
-- that *does* support an explicit theorem list and axiom allow-list:
-- `lake comparator` (see `comparator.json`). Between the two gates, every
-- theorem in this project is either kernel-checked here with the standard
-- axioms, or kernel-checked by name by `comparator`, or is one of the 3
-- documented `sorry`s. Nothing is unaccounted for.
--
-- `MipsSim.Specs.StepSpec` is still built by plain `lake build MipsSim`
-- (see the `MipsSim` library, still present in `lakefile.toml` for that
-- purpose) and by `lake comparator`; it is only excluded from `lake
-- check`'s default target.
import MipsSim.Word
import MipsSim.Types
import MipsSim.State
import MipsSim.Instruction
import MipsSim.Asm
import MipsSim.Step
