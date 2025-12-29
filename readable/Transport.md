# Transport.lean

This file defines the population-level targets and the transport assumptions linking experimental and population scores.

Population targets:
- `popMeanAttr`, `popM2Attr`, `popVarAttr`, `popSDAttr` define the mean, second moment, variance, and standard deviation of a score function under a population distribution `nu` (see [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md)).
- `PopulationMomentAssumptions` bundles integrability conditions so these quantities are well-defined.

Transport assumptions:
- `Overlap` means the population distribution is supported where the design distribution has mass.
- `Invariance` says the experimental score and population score match everywhere; `InvarianceAE` relaxes this to "almost everywhere".
- `TransportAssumptions` bundles probability conditions, overlap, and invariance.

This file is the foundation: it defines the population targets that all later [consistency](jargon_consistency.md) results point to.
