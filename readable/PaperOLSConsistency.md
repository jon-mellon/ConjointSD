# PaperOLSConsistency.lean

Lean file: [ConjointSD/PaperOLSConsistency.lean](../ConjointSD/PaperOLSConsistency.lean)

This file specializes the regression [consistency](jargon_consistency.md) machinery to the paper's OLS [estimator](jargon_estimator.md) and [term](jargon_term.md) set. It uses bundled `ProbMeasureAssumptions` where probability assumptions are required, and the LLN statements target the experimental pushforward attribute law `Measure.map (A 0) μ` (the experiment data used to fit the model).

Key definition:
- `gPaper` is the score function defined by the paper's regression [terms](jargon_term.md) (intercept, main effects, [interactions](jargon_interaction.md)). It uses the [linear model](jargon_linear_model.md) setup.

Assumption package:
- The core package is `OLSMomentAssumptionsOfAttr` from the generic regression section, specialized to `φPaper` and `gStar`. It says the empirical Gram and cross moments converge to their attribute‑distribution targets and the normal equations identify `theta0`.
- `paper_ols_lln_of_score_assumptions_ae` derives the Gram/cross LLN part from existing `ScoreAssumptions` and a (strong) noiseless link `Yobs = gStar ∘ A` on sample paths, with the attribute moments computed under `Measure.map (A 0) μ` for the experimental design.
- `PaperOLSDesignAssumptions` packages design IID, bounded/measurable features, bounded `gStar`, and equality of design vs target Gram/cross moments. From this bundle:
  - `paper_ols_lln_of_design_ae` derives the LLN statement with limits expressed under the target `ν`.
  - `paper_ols_attr_moments_of_design_ae` combines that LLN with inverse‑Gram stability and identification to yield `OLSMomentAssumptionsOfAttr` a.e.
- `paper_ols_attr_moments_of_lln_fullrank_ae` packages Gram/cross LLN, inverse‑Gram stability, and identifiability into the a.e. `OLSMomentAssumptionsOfAttr` statement used by later theorems.
- In the Gram/cross convergence proofs, empirical means are now routed through `meanHatZ_tendsto_ae_of_score`, keeping the flow explicitly tied to `ScoreAssumptions` rather than standalone IID bundles.

Main results:
- `theta_tendsto_of_paper_ols_moments_ae` gives almost-everywhere [convergence](jargon_convergence.md) of the OLS coefficient estimates to `theta0`.
- A non-AE version is provided for deterministic sequences.
- `theta_tendsto_of_paper_ols_design_ae` derives the same convergence from `PaperOLSDesignAssumptions` plus inverse‑Gram stability and identification.
- `attrMean_tendsto_of_paper_ols_gStar` / `attrM2_tendsto_of_paper_ols_gStar` combine OLS [convergence](jargon_convergence.md) with functional [continuity](jargon_continuity.md) to produce plug‑in mean/second‑moment convergence for the paper’s score.
- `attrMean_tendsto_of_paper_ols_moments_ae` / `attrM2_tendsto_of_paper_ols_moments_ae` provide the same [bridge](jargon_bridge.md) a.e. when the OLS moment assumptions hold along sample paths.
- `attrMean_tendsto_of_paper_ols_design_ae` / `attrM2_tendsto_of_paper_ols_design_ae` are the end‑to‑end a.e. bridges from the design‑side bundle to plug‑in moment convergence.
- `gPaper_eq_gTotalΘ_blocks` identifies the paper score with the block-sum total score (for any `blk`), so the OLS path can feed into the block/total [standard deviation](jargon_standard_deviation.md) chain.
- `attrMean_tendsto_of_paper_ols_gStar_total` / `attrM2_tendsto_of_paper_ols_gStar_total` and their a.e. counterparts lift the OLS assumptions from `gPaper` to the block-sum total score.
- `paper_ols_attr_moments_of_lln_fullrank_ae` assembles the a.e. moment package from [LLN](jargon_lln.md)-style and inverse-stability assumptions plus the target human population normal equations.

This file is the link from [regression](jargon_regression.md) / [OLS](jargon_ols.md) [consistency](jargon_consistency.md) to the [plug-in](jargon_plug_in.md) moment assumptions used in the [standard deviation](jargon_standard_deviation.md) consistency proofs.
