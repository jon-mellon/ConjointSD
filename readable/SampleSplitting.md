# SampleSplitting.lean

Lean file: [ConjointSD/SampleSplitting.lean](../ConjointSD/SampleSplitting.lean)

This file handles the evaluation stage in a sample-splitting setup. It uses `ProbMeasureAssumptions` for the target attribute distribution `ν` and assumes `EvalAttrLawEqPop` so the evaluation draw `A 0` under the evaluation law `ρ` has the target attribute law `ν`. The training data that produced `θhat` is not modeled here.

Key definitions:
- `SplitEvalAssumptionsBounded` bundles the evaluation-stage assumptions needed to
  treat the [plug-in](jargon_plug_in.md) score at training index `m` as fixed and apply
  LLNs. It supplies `EvalAttrIID` for the evaluation draws and boundedness/measurability
  for `gHat`.
Main results:
- `sdHat_fixed_m_tendsto_ae_attrSD` says: for fixed `m`, the evaluation-stage
  [standard deviation](jargon_standard_deviation.md) [estimator](jargon_estimator.md)
  [converges](jargon_convergence.md) ([almost everywhere](jargon_almost_everywhere.md))
  to the target human [population](jargon_population.md) [SD](jargon_standard_deviation.md)
  of the [plug-in](jargon_plug_in.md) score, using boundedness-based evaluation assumptions
  and the SRS law-equality assumption.
This file is the building [block](jargon_block.md) for the two-stage (m then n) [convergence](jargon_convergence.md) results.
