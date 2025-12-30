# SampleSplitting.lean

Lean file: [ConjointSD/SampleSplitting.lean](../ConjointSD/SampleSplitting.lean)

This file handles the evaluation stage in a sample-splitting setup. It now uses `ProbMeasureAssumptions` and the bundled `MapLawAssumptions` when translating experimental-design SDs to attribute-distribution SDs.

Key definitions:
- `SplitEvalAssumptions` bundles the assumptions needed to treat the [plug-in](jargon_plug_in.md) score at training index `m` as fixed and apply the [standard deviation](jargon_standard_deviation.md) [convergence](jargon_convergence.md) result; measurability of `A 0` is inherited from the bundled `DesignAttrIID`.
- `SplitEvalAssumptionsBounded` is a boundedness-based version of the same assumptions.

Main results:
- `sdHat_fixed_m_tendsto_ae_attrSD` says: for fixed `m`, the evaluation-stage [standard deviation](jargon_standard_deviation.md) [estimator](jargon_estimator.md) [converges](jargon_convergence.md) ([almost everywhere](jargon_almost_everywhere.md)) to the target human [population](jargon_population.md) [SD](jargon_standard_deviation.md) of the [plug-in](jargon_plug_in.md) score under the evaluation attribute [distribution](jargon_distribution.md).

This file is the building [block](jargon_block.md) for the two-stage (m then n) [convergence](jargon_convergence.md) results.
