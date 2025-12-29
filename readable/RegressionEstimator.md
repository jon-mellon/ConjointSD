# RegressionEstimator.lean

This file formalizes an [OLS](jargon_ols.md)-style [regression](jargon_regression.md) [estimator](jargon_estimator.md) and the assumptions needed for its [consistency](jargon_consistency.md).

Key pieces:
- `empiricalRisk`: the average squared error for a linear model on the first `n` samples.
- `OLSSequence`: a sequence of parameter estimates that minimize the empirical risk at each `n`.
- `gramMatrix` and `crossVec`: the empirical matrices used in the normal equations.
- `olsThetaHat`: the closed-form normal-equation estimator based on `gramMatrix` and `crossVec`.

Moment assumptions and [consistency](jargon_consistency.md):
- `OLSMomentAssumptions` says the inverse Gram matrix and cross moments [converge](jargon_convergence.md) entrywise to limits, and that the true parameter equals the limit product.
- `olsThetaHat_tendsto_of_moment_assumptions` proves the estimator [converges](jargon_convergence.md) to `theta0` under those assumptions.

Population versions:
- `popGram` and `popCross` define population analogs of the Gram matrix and cross moments.
- `OLSMomentAssumptionsOfPop` is the same [convergence](jargon_convergence.md) statement, but with population targets.
- `olsThetaHat_tendsto_of_pop_moments` connects these to estimator [convergence](jargon_convergence.md).

Final bridge:
- `GEstimationAssumptions_of_OLSConsistency` says that if an OLS sequence [converges](jargon_convergence.md) and the population functionals are continuous, then the plug-in moment assumptions hold.

This file supplies the regression backbone used by the paper-level [consistency](jargon_consistency.md) results.
