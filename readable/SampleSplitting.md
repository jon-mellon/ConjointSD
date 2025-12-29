# SampleSplitting.lean

This file handles the evaluation stage in a sample-splitting setup.

Key definitions:
- `SplitEvalAssumptions` bundles the assumptions needed to treat the plug-in score at training index `m` as fixed and apply the oracle [standard deviation](jargon_standard_deviation.md) [convergence](jargon_convergence.md) result.
- `SplitEvalAssumptionsBounded` is a boundedness-based version of the same assumptions.

Main results:
- `sdHat_fixed_m_tendsto_ae_popSDAttr` says: for fixed `m`, the evaluation-stage [standard deviation](jargon_standard_deviation.md) estimator [converges](jargon_convergence.md) ([almost everywhere](jargon_almost_everywhere.md)) to the population SD of the plug-in score under the evaluation [distribution](jargon_distribution.md).
- `sdHat_fixed_m_tendsto_ae_popSDAttr_of_bounded` is the boundedness variant.

This file is the building block for the two-stage (m then n) [convergence](jargon_convergence.md) results.
