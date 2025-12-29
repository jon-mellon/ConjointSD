# Transport.lean

This file defines the [population](jargon_population.md)-level targets and the transport assumptions linking experimental and population scores.

Population targets:
- `popMeanAttr`, `popM2Attr`, `popVarAttr`, `popSDAttr` define the mean, second moment, variance, and standard deviation of a score function under a population [distribution](jargon_distribution.md) `nu` (see [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md)).
- `PopulationMomentAssumptions` bundles [integrable](jargon_integrable.md) conditions so these quantities are well-defined.

Transport assumptions:
- `Overlap` [means](jargon_mean.md) the population [distribution](jargon_distribution.md) is supported where the design [distribution](jargon_distribution.md) has mass.
- `Invariance` says the experimental score and population score match everywhere; `InvarianceAE` relaxes this to [almost everywhere](jargon_almost_everywhere.md).
- `TransportAssumptions` bundles probability conditions, overlap, and invariance.

This file is the foundation: it defines the population targets that all later [consistency](jargon_consistency.md) results point to.
