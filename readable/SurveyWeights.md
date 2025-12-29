# SurveyWeights.lean

This file adds weighted versions of the population targets and defines finite-population targets.

Weighted targets:
- `weightMeanAttr`, `weightM2Attr`, `weightVarAttr`, `weightSDAttr` compute weighted versions of the [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), and [standard deviation](jargon_standard_deviation.md).
- `WeightAssumptions` ensures weights are nonnegative, integrable, and have positive total mass so the normalization makes sense.
- Lemmas show that with weight 1, the weighted targets reduce to the usual population targets.

Finite-population targets:
- `finitePopMean`, `finitePopM2`, `finitePopVar`, `finitePopSD` define deterministic targets for a finite set of profiles, with `finitePopSD` as the finite-population [standard deviation](jargon_standard_deviation.md).

This file does not prove new [convergence](jargon_convergence.md) results; it provides alternative targets that can plug into the same [consistency](jargon_consistency.md) framework.
