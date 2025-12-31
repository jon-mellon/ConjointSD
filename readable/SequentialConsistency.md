# SequentialConsistency.lean

Lean file: [ConjointSD/SequentialConsistency.lean](../ConjointSD/SequentialConsistency.lean)

This file proves a two-stage [convergence](jargon_convergence.md) statement for [standard deviation](jargon_standard_deviation.md) estimation with sample splitting. It uses `ProbMeasureAssumptions` and `EpsilonAssumptions`, and takes raw `Tendsto θhat atTop (nhds θ0)` plus continuity to derive plug‑in moment convergence. The target is the attribute-distribution SD under `ν`, with `EvalWeightMatchesAttrMoments` matching weighted evaluation moments under `μ`. The training distribution that produces `θhat` is left abstract.
It uses the notion of [sequential [consistency](jargon_consistency.md)](jargon_sequential_consistency.md).

Definitions:
- `sdEst`: the evaluation-stage [standard deviation](jargon_standard_deviation.md) [estimator](jargon_estimator.md) using a fixed training index `m`, evaluation size `n`, and a weight function `w`.
- `sdOracle`: the target [standard deviation](jargon_standard_deviation.md) computed with the true score (see [oracle](jargon_oracle.md)).
- `trainErr`: the gap between the [plug-in](jargon_plug_in.md) [standard deviation](jargon_standard_deviation.md) at training index `m` and the oracle [SD](jargon_standard_deviation.md).
- `totalErr`: the gap between the weighted evaluation estimator and the oracle [standard deviation](jargon_standard_deviation.md).

Main logic (three steps):
1) For fixed `m`, as `n` grows, `totalErr` [converges](jargon_convergence.md) to `trainErr` for almost all outcomes (see [almost everywhere](jargon_almost_everywhere.md)).
2) As `m` grows, `trainErr` goes to 0, using parameter convergence + continuity to derive the plug‑in moment [convergence](jargon_convergence.md).
3) Combine the two to show: for any epsilon, there is an `M` so that for all `m >= M`, the evaluation error becomes less than epsilon for large enough `n` ([almost everywhere](jargon_almost_everywhere.md)).
