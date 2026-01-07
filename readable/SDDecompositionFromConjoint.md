# SDDecompositionFromConjoint.lean

Lean file: [ConjointSD/SDDecompositionFromConjoint.lean](../ConjointSD/SDDecompositionFromConjoint.lean)

This file connects a sequence of attribute draws to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) results for any score function, and then extends that to a family of [block](jargon_block.md) scores. It now uses `IsProbabilityMeasure` instead of standalone probability-measure hypotheses.

Key definitions:
- `EvalAttrIID` packages IID assumptions for the attribute process `A` (see [iid](jargon_iid.md)).
- `Zcomp` composes attributes with a score function: `Z i = g (A i)`.
- The LLN lemmas in this file take measurability + boundedness and derive integrability internally.

Main results:
- If `g` is bounded, then the second-moment and [integrable](jargon_integrable.md) conditions hold automatically.
- `meanHatZ_tendsto_ae_of_score` applies the [LLN](jargon_lln.md) to score processes from `EvalAttrIID` plus boundedness/measurability.
- Convergence results for derived RMSE/variance estimators are handled by combining the mean and second-moment limits rather than standalone lemmas.
- Bounded-score integrability is assembled directly in proofs instead of via a dedicated helper lemma.
- `m2HatZ_tendsto_ae_of_score` and `sdHatZ_tendsto_ae_of_score` extend the LLN results to second moments and standard deviations for bounded scores.

This file is the [bridge](jargon_bridge.md) from attribute IID to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) for scores and blocks.
