# SampleSplitting.lean

This file handles the evaluation stage in a sample-splitting setup.

Key definitions:
- `SplitEvalAssumptions` bundles the assumptions needed to treat the [plug-in](jargon_plug_in.md) score at training index `m` as fixed and apply the [oracle](jargon_oracle.md) [standard deviation](jargon_standard_deviation.md) [convergence](jargon_convergence.md) result.
- `SplitEvalAssumptionsBounded` is a boundedness-based version of the same assumptions.

Main results:
- `sdHat_fixed_m_tendsto_ae_popSDAttr` says: for fixed `m`, the evaluation-stage [standard deviation](jargon_standard_deviation.md) [estimator](jargon_estimator.md) [converges](jargon_convergence.md) ([almost everywhere](jargon_almost_everywhere.md)) to the [population](jargon_population.md) [SD](jargon_standard_deviation.md) of the [plug-in](jargon_plug_in.md) score under the evaluation [distribution](jargon_distribution.md).
- `sdHat_fixed_m_tendsto_ae_popSDAttr_of_bounded` is the boundedness variant.

This file is the building [block](jargon_block.md) for the two-stage (m then n) [convergence](jargon_convergence.md) results.
