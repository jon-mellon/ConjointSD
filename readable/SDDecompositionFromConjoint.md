# SDDecompositionFromConjoint.lean

Lean file: [ConjointSD/SDDecompositionFromConjoint.lean](../ConjointSD/SDDecompositionFromConjoint.lean)

This file connects a sequence of attribute draws to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) results for any score function, and then extends that to a family of [block](jargon_block.md) scores. It now uses `ProbMeasureAssumptions` instead of standalone probability-measure hypotheses.

Key definitions:
- `DesignAttrIID` packages IID assumptions for the attribute process `A` (see [iid](jargon_iid.md)).
- `Zcomp` composes attributes with a score function: `Z i = g (A i)`.
- `ScoreAssumptions` still packages [measurability](jargon_measurable.md) and a second-moment condition, but the LLN lemmas in this file now take measurability + boundedness and derive those moments internally.

Main results:
- If `g` is bounded, then the second-moment and [integrable](jargon_integrable.md) conditions hold automatically.
- `meanHatZ_tendsto_ae_of_score`, `m2HatZ_tendsto_ae_of_score`, and `sdHatZ_tendsto_ae_of_score` apply the [LLN](jargon_lln.md) to score processes from `DesignAttrIID` plus boundedness/measurability.
- `meanHatZW_tendsto_ae_of_score`, `m2HatZW_tendsto_ae_of_score`, and `sdHatZW_tendsto_ae_of_score` provide weighted analogues using bounded scores and weights.
- `sd_component_consistent` proves the empirical [standard deviation](jargon_standard_deviation.md) of `g(A i)` [converges](jargon_convergence.md) to the target attribute-distribution [SD](jargon_standard_deviation.md).
- `sd_component_consistent_of_bounded` is a convenient wrapper with the same boundedness inputs.

Block version:
- `DecompAssumptions` bundles boundedness and [measurability](jargon_measurable.md) for all [blocks](jargon_block.md).
- `sd_block_consistent` applies the single-score result to any chosen block.

This file is the [bridge](jargon_bridge.md) from design-based attribute IID to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) for scores and blocks.
