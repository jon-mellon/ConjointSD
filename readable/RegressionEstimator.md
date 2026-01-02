# RegressionEstimator.lean

Lean file: [ConjointSD/RegressionEstimator.lean](../ConjointSD/RegressionEstimator.lean)

This file formalizes an [OLS](jargon_ols.md)-style [regression](jargon_regression.md) [estimator](jargon_estimator.md) and the assumptions needed for its [consistency](jargon_consistency.md). It now uses `ProbMeasureAssumptions` in place of standalone probability-measure hypotheses.

Key pieces:
- `gramMatrix` and `crossVec`: the empirical matrices used in the normal equations.
- `olsThetaHat`: the closed-form normal-equation estimator based on `gramMatrix` and `crossVec`.

Moment assumptions and [consistency](jargon_consistency.md):
- `OLSMomentAssumptions` says the inverse Gram matrix and cross moments [converge](jargon_convergence.md) entrywise to limits.
- `olsThetaHat_tendsto_of_moment_assumptions` proves the estimator [converges](jargon_convergence.md) to the limit product, and `olsThetaHat_tendsto_of_moment_assumptions_id` adds the separate identification equation to conclude convergence to `theta0`.

Attribute‑distribution versions:
- `attrGram` and `attrCross` define the Gram and cross moments under a generic attribute distribution `xiAttr` (use `kappaDesign` in the first-stage OLS setting).
- `OLSMomentAssumptionsOfAttr` is the same [convergence](jargon_convergence.md) statement, but with limits pinned to `xiAttr` moments rather than abstract limits.
- `olsThetaHat_tendsto_of_attr_moments` adds the identification equation to connect these limits to estimator [convergence](jargon_convergence.md).
- `OLSMomentAssumptionsOfAttr.to_OLSMomentAssumptions` is a small adapter from `xiAttr`-based assumptions to the abstract limit form.

This file supplies the regression backbone used by the paper-level [consistency](jargon_consistency.md) results.
