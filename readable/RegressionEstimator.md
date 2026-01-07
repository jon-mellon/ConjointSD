# RegressionEstimator.lean

Lean file: [ConjointSD/RegressionEstimator.lean](../ConjointSD/RegressionEstimator.lean)

This file formalizes an [OLS](jargon_ols.md)-style [regression](jargon_regression.md) [estimator](jargon_estimator.md) and the assumptions needed for its [consistency](jargon_consistency.md). It now uses `IsProbabilityMeasure` in place of standalone probability-measure hypotheses.

Key pieces:
- `gramMatrix` and `crossVec`: the empirical matrices used in the normal equations.
- `olsThetaHat`: the closed-form normal-equation estimator based on `gramMatrix` and `crossVec`.

Moment assumptions and [consistency](jargon_consistency.md):
- `attrGram` and `attrCross` define the Gram and cross moments under a generic attribute distribution `xiAttr` (use `kappaDesign` in the first-stage OLS setting).
- `olsThetaHat_tendsto_of_attr_moments` assumes entrywise convergence of the inverse Gram and cross moments to these `xiAttr` targets, then uses the identification equation to get estimator [convergence](jargon_convergence.md).

This file supplies the regression backbone used by the paper-level [consistency](jargon_consistency.md) results.
