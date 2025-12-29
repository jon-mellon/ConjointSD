# PaperOLSConsistency.lean

This file specializes the regression [consistency](jargon_consistency.md) machinery to the paper's OLS estimator and term set.

Key definition:
- `gPaper` is the score function defined by the paper's regression terms (intercept, main effects, interactions). It uses the linear model setup.

Assumption package:
- `PaperOLSMomentAssumptions` says that for almost every sample path, the empirical Gram matrix and cross moments [converge](jargon_convergence.md) to their population versions for the causal target. This is the key input for OLS [consistency](jargon_consistency.md).

Main results:
- `theta_tendsto_of_paper_ols_moments_ae` gives almost-everywhere [convergence](jargon_convergence.md) of the OLS coefficient estimates to `theta0`.
- A non-AE version is provided for deterministic sequences.
- `GEstimationAssumptions_of_paper_ols_gStar` combines OLS [convergence](jargon_convergence.md) with functional continuity to produce `GEstimationAssumptions` for the paper's score.
- `GEstimationAssumptions_of_paper_ols_moments_ae` provides the same bridge a.e. when the OLS moment assumptions hold along sample paths.

This file is the link from [regression](jargon_regression.md) / [OLS](jargon_ols.md) [consistency](jargon_consistency.md) to the plug-in moment assumptions used in the [standard deviation](jargon_standard_deviation.md) consistency proofs.
