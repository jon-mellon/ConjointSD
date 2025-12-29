# Transport.lean

Lean file: [ConjointSD/Transport.lean](../ConjointSD/Transport.lean)

This file defines the [population](jargon_population.md)-level targets and the transport assumptions linking experimental and population scores.

Population targets:
- `popMeanAttr`, `popM2Attr`, `popVarAttr`, `popSDAttr` define the mean, second moment, variance, and standard deviation of a score function under a population [distribution](jargon_distribution.md) `nu` (see [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md)).
- `PopulationMomentAssumptions` bundles [integrable](jargon_integrable.md) conditions so these quantities are well-defined.

Transport assumptions:
- `InvarianceAE` says the experimental and population scores match
  [almost everywhere](jargon_almost_everywhere.md) under the population
  [distribution](jargon_distribution.md). This is the transport condition used by
  later results.

This file is the foundation: it defines the population targets that all later [consistency](jargon_consistency.md) results point to.
