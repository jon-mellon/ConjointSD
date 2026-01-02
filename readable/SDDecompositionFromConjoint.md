# SDDecompositionFromConjoint.lean

Lean file: [ConjointSD/SDDecompositionFromConjoint.lean](../ConjointSD/SDDecompositionFromConjoint.lean)

This file connects a sequence of attribute draws to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) results for any score function, and then extends that to a family of [block](jargon_block.md) scores. It now uses `ProbMeasureAssumptions` instead of standalone probability-measure hypotheses.

Key definitions:
- `DesignAttrIID` packages IID assumptions for the attribute process `A` (see [iid](jargon_iid.md)).
- `Zcomp` composes attributes with a score function: `Z i = g (A i)`.
- `ScoreAssumptions` still packages [measurability](jargon_measurable.md) and a second-moment condition, but the LLN lemmas in this file now take measurability + boundedness and derive those moments internally.

Main results:
- If `g` is bounded, then the second-moment and [integrable](jargon_integrable.md) conditions hold automatically.
- `meanHatZ_tendsto_ae_of_score` applies the [LLN](jargon_lln.md) to score processes from `DesignAttrIID` plus boundedness/measurability.
- Convergence results for derived RMSE/variance estimators are handled by combining the mean and second-moment limits rather than standalone lemmas.
- `meanHatZW_tendsto_ae_of_score`, `m2HatZW_tendsto_ae_of_score`, and `sdHatZW_tendsto_ae_of_score` provide weighted analogues using bounded scores and weights.

Block version:
- `DecompAssumptions` bundles boundedness and [measurability](jargon_measurable.md) for all [blocks](jargon_block.md).

This file is the [bridge](jargon_bridge.md) from design-based attribute IID to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) for scores and blocks.
