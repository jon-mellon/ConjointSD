# SampleSplitting.lean

Lean file: [ConjointSD/SampleSplitting.lean](../ConjointSD/SampleSplitting.lean)

This file handles the evaluation stage in a sample-splitting setup. It uses `ProbMeasureAssumptions` for the target attribute distribution `ν` and assumes `EvalWeightMatchesPopMoments` so the *weighted* evaluation draw `A 0` under the evaluation law `ρ` matches the target mean/second moment for the score being evaluated. The training data that produced `θhat` is not modeled here.

Key definitions:
- `SplitEvalWeightAssumptions` bundles the weighted evaluation-stage assumptions needed to
  treat the [plug-in](jargon_plug_in.md) score at training index `m` as fixed and apply
  weighted LLNs. It supplies `EvalAttrIID` for the evaluation draws, score assumptions
  for `w`, `w * gHat`, and `w * (gHat)^2`, plus a nonzero weight mean so ratios are
  well-defined.
- `SplitEvalWeightAssumptionsNoIID` is the same bundle without the IID component, for
  cases where IID is derived separately (e.g. from randomized assignment).
- `SplitEvalAssumptionsBounded` is a boundedness-based version of the unweighted score
  assumptions used inside the weighted bundles; i.i.d. properties for the evaluation
  draws are supplied separately when converting to the full evaluation assumptions.

Main results:
- `sdHat_fixed_m_tendsto_ae_attrSD` says: for fixed `m`, the *weighted* evaluation-stage
  [standard deviation](jargon_standard_deviation.md) [estimator](jargon_estimator.md)
  [converges](jargon_convergence.md) ([almost everywhere](jargon_almost_everywhere.md))
  to the target human [population](jargon_population.md) [SD](jargon_standard_deviation.md)
  of the [plug-in](jargon_plug_in.md) score, using the weighted moment match.
- `splitEvalWeightAssumptions_of_stream` derives `SplitEvalWeightAssumptions` from
  `SplitEvalWeightAssumptionsNoIID` when IID is obtained from a
  `ConjointRandomizationStream`.

This file is the building [block](jargon_block.md) for the two-stage (m then n) [convergence](jargon_convergence.md) results.
