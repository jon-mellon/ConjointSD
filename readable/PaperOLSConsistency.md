# PaperOLSConsistency.lean

Lean file: [ConjointSD/PaperOLSConsistency.lean](../ConjointSD/PaperOLSConsistency.lean)

This file specializes the regression [consistency](jargon_consistency.md) machinery to the paper's OLS [estimator](jargon_estimator.md) and [term](jargon_term.md) set.

Key definition:
- `gPaper` is the score function defined by the paper's regression [terms](jargon_term.md) (intercept, main effects, [interactions](jargon_interaction.md)). It uses the [linear model](jargon_linear_model.md) setup.

Assumption package:
- `PaperOLSMomentAssumptions` says that for almost every sample path, the empirical Gram matrix and cross moments [converge](jargon_convergence.md) to their [population](jargon_population.md) versions for the causal target. This is the key input for OLS [consistency](jargon_consistency.md).
- `PaperOLSLLNA`, `PaperOLSInverseStability`, and `PaperOLSIdentifiability` break the moment package into LLN for Gram/cross, inverse stability, and the population normal-equation identity for `theta0`.
- `paper_ols_lln_of_score_assumptions_ae` derives the LLN part from existing `ScoreAssumptions`, plus a law-of-attributes condition and a (strong) noiseless link `Yobs = gStar ∘ A` on sample paths.

Main results:
- `theta_tendsto_of_paper_ols_moments_ae` gives almost-everywhere [convergence](jargon_convergence.md) of the OLS coefficient estimates to `theta0`.
- A non-AE version is provided for deterministic sequences.
- `GEstimationAssumptions_of_paper_ols_gStar` combines OLS [convergence](jargon_convergence.md) with functional [continuity](jargon_continuity.md) to produce `GEstimationAssumptions` for the paper's score.
- `GEstimationAssumptions_of_paper_ols_moments_ae` provides the same [bridge](jargon_bridge.md) a.e. when the OLS moment assumptions hold along sample paths.
- `gPaper_eq_gTotalΘ_blocks` identifies the paper score with the block-sum total score (for any `blk`), so the OLS path can feed into the block/total [standard deviation](jargon_standard_deviation.md) chain.
- `GEstimationAssumptions_of_paper_ols_gStar_total` and `GEstimationAssumptions_of_paper_ols_moments_total_ae` lift the OLS assumptions from `gPaper` to the block-sum total score.
- `paper_ols_moment_assumptions_of_lln_fullrank_ae` assembles the a.e. moment package from LLN-style and inverse-stability assumptions plus the population normal equations.

This file is the link from [regression](jargon_regression.md) / [OLS](jargon_ols.md) [consistency](jargon_consistency.md) to the [plug-in](jargon_plug_in.md) moment assumptions used in the [standard deviation](jargon_standard_deviation.md) consistency proofs.
