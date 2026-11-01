-- Root of the `Semantics` library: importing here makes plain `lake build`
-- (and CI) cover every module.
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Asm
import Semantics.Step
import Semantics.Specs.StepSpec
