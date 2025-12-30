# SurveyWeights.lean

Lean file: [ConjointSD/SurveyWeights.lean](../ConjointSD/SurveyWeights.lean)

This file adds weighted versions of the target human [population](jargon_population.md) targets (under the attribute distribution) and defines finite-population targets. It now uses `ProbMeasureAssumptions` in place of standalone probability-measure hypotheses.

Weighted targets:
- `weightMeanAttr`, `weightM2Attr`, `weightVarAttr`, `weightSDAttr` compute weighted versions of the [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), and [standard deviation](jargon_standard_deviation.md).
- `WeightAssumptions` ensures weights are nonnegative, [integrable](jargon_integrable.md), and have positive total mass so the [normalization](jargon_normalization.md) makes sense.
- Lemmas show that with weight 1, the weighted targets reduce to the usual target human population targets.
- `weightVarAttr_eq_attrVar_of_moments` and `weightSDAttr_eq_attrSD_of_moments` show that if weighted moments match target human population moments, then weighted variance/SD equals the target human population variance/SD.

Finite-population targets:
- `finitePopMean`, `finitePopM2`, `finitePopVar`, `finitePopSD` define deterministic targets for a finite set of [profiles](jargon_profile.md), with `finitePopSD` as the finite-population [standard deviation](jargon_standard_deviation.md).

This file does not prove new [convergence](jargon_convergence.md) results; it provides alternative targets that can plug into the same [consistency](jargon_consistency.md) framework.
