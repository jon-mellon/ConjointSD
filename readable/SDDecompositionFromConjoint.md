# SDDecompositionFromConjoint.lean

Lean file: [ConjointSD/SDDecompositionFromConjoint.lean](../ConjointSD/SDDecompositionFromConjoint.lean)

This file connects a sequence of attribute draws to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) results for any score function, and then extends that to a family of [block](jargon_block.md) scores. It now uses `ProbMeasureAssumptions` instead of standalone probability-measure hypotheses.

Key definitions:
- `DesignAttrIID` packages IID assumptions for the attribute process `A` (see [iid](jargon_iid.md)).
- `Zcomp` composes attributes with a score function: `Z i = g (A i)`.
- `ScoreAssumptions` adds [measurability](jargon_measurable.md) and a second-moment condition for `g`; [integrability](jargon_integrable.md) of `g(A 0)` is derived under a probability measure.

Main results:
- If `g` is bounded, then the second-moment and [integrable](jargon_integrable.md) conditions hold automatically.
- `iidAssumptions_Zcomp` shows that the score process `Zcomp` inherits [IID](jargon_iid.md) properties from `A`.
- `sd_component_consistent` proves the empirical [standard deviation](jargon_standard_deviation.md) of `g(A i)` [converges](jargon_convergence.md) to the target attribute-distribution [SD](jargon_standard_deviation.md).
- `sd_component_consistent_of_design` is a wrapper that takes `ConjointDesignAssumptions` and yields the same SD-consistency result, making the link to identification explicit.
- `sd_component_consistent_of_bounded` is a convenient bounded version.

Block version:
- `DecompAssumptions` bundles boundedness and [measurability](jargon_measurable.md) for all [blocks](jargon_block.md).
- `sd_block_consistent` applies the single-score result to any chosen block.

This file is the [bridge](jargon_bridge.md) from general [IID](jargon_iid.md) assumptions on the data to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) for scores and blocks.
