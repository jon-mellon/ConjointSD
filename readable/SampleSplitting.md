# SampleSplitting.lean

Lean file: [ConjointSD/SampleSplitting.lean](../ConjointSD/SampleSplitting.lean)

This file handles the evaluation stage in a sample-splitting setup. It uses `ProbMeasureAssumptions` for the target attribute distribution `ν` and assumes `EvalAttrMoments` so the evaluation draw `A 0` under the evaluation law `μ` matches the target mean/second moment for the score being evaluated. The training data that produced `θhat` is not modeled here.

Key definitions:
- `SplitEvalAssumptions` bundles the evaluation-stage assumptions needed to treat the
  [plug-in](jargon_plug_in.md) score at training index `m` as fixed and apply the
  [standard deviation](jargon_standard_deviation.md) [convergence](jargon_convergence.md)
  result. Concretely, once `m` is fixed, the evaluation draws behave like an i.i.d.
  sample for the fixed score `gHat g θhat m`, so LLN-style SD consistency applies.
  Measurability of `A 0` is inherited from the bundled `DesignAttrIID`.
- `SplitEvalAssumptionsBounded` is a boundedness-based version of the same assumptions; i.i.d.
  properties for the evaluation draws are supplied separately when converting to
  `ScoreAssumptions`.

Main results:
- `sdHat_fixed_m_tendsto_ae_attrSD` says: for fixed `m`, the evaluation-stage [standard deviation](jargon_standard_deviation.md) [estimator](jargon_estimator.md) [converges](jargon_convergence.md) ([almost everywhere](jargon_almost_everywhere.md)) to the target human [population](jargon_population.md) [SD](jargon_standard_deviation.md) of the [plug-in](jargon_plug_in.md) score, using the evaluation-to-population moment match.

This file is the building [block](jargon_block.md) for the two-stage (m then n) [convergence](jargon_convergence.md) results.
