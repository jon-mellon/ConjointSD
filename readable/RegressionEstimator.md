# RegressionEstimator.lean

Lean file: [ConjointSD/RegressionEstimator.lean](../ConjointSD/RegressionEstimator.lean)

This file formalizes an [OLS](jargon_ols.md)-style [regression](jargon_regression.md) [estimator](jargon_estimator.md) and the assumptions needed for its [consistency](jargon_consistency.md). It now uses `ProbMeasureAssumptions` in place of standalone probability-measure hypotheses.

Key pieces:
- `empiricalRisk`: the average squared error for a [linear model](jargon_linear_model.md) on the first `n` samples.
- `OLSSequence`: a sequence of [parameter](jargon_parameter.md) estimates that minimize the empirical risk at each `n`.
- `gramMatrix` and `crossVec`: the empirical matrices used in the normal equations.
- `olsThetaHat`: the closed-form normal-equation estimator based on `gramMatrix` and `crossVec`.

Moment assumptions and [consistency](jargon_consistency.md):
- `OLSMomentAssumptions` says the inverse Gram matrix and cross moments [converge](jargon_convergence.md) entrywise to limits, and that the true [parameter](jargon_parameter.md) equals the limit product.
- `olsThetaHat_tendsto_of_moment_assumptions` proves the estimator [converges](jargon_convergence.md) to `theta0` under those assumptions.

Population versions:
- `popGram` and `popCross` define [population](jargon_population.md) analogs of the Gram matrix and cross moments.
- `OLSMomentAssumptionsOfPop` is the same [convergence](jargon_convergence.md) statement, but with population targets.
- `olsThetaHat_tendsto_of_pop_moments` connects these to estimator [convergence](jargon_convergence.md).
 - `OLSMomentAssumptionsOfPop.to_OLSMomentAssumptions` is a small adapter from population assumptions to the abstract limit form.

Final [bridge](jargon_bridge.md):
- `GEstimationAssumptions_of_OLSConsistency` says that if an OLS sequence [converges](jargon_convergence.md) and the population functionals are [continuous](jargon_continuity.md), then the [plug-in](jargon_plug_in.md) moment assumptions hold.

This file supplies the regression backbone used by the paper-level [consistency](jargon_consistency.md) results.
