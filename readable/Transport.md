# Transport.lean

Lean file: [ConjointSD/Transport.lean](../ConjointSD/Transport.lean)

This file defines the target human [population](jargon_population.md)-level targets and the transport assumptions linking experimental and target-population scores.

Population targets:
- `attrMean`, `attrM2`, `attrVar`, `attrSD` define the mean, second moment, variance, and standard deviation of a score function under the attribute [distribution](jargon_distribution.md) `nu` for the target human population (see [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md)).
- `AttrMomentAssumptions` bundles [integrable](jargon_integrable.md) conditions so these quantities are well-defined.

Transport assumptions:
- `InvarianceAE` says the experimental and target-population scores match
  [almost everywhere](jargon_almost_everywhere.md) under the attribute
  [distribution](jargon_distribution.md). This is the transport condition used by
  later results.

This file is the foundation: it defines the target human population targets that all later [consistency](jargon_consistency.md) results point to.
