# PaperOLSConsistency.lean

Lean file: [ConjointSD/PaperOLSConsistency.lean](../ConjointSD/PaperOLSConsistency.lean)

This file specializes the regression [consistency](jargon_consistency.md) machinery to the paper's OLS [estimator](jargon_estimator.md) and [term](jargon_term.md) set. It uses bundled `ProbMeasureAssumptions` where probability assumptions are required, and the LLN statements target the experimental pushforward attribute law `kappaDesign := Measure.map (A 0) μexp` (the experiment data used to fit the model). In the code, this distribution is denoted `xiAttr`; the target population distribution `ν` is not used in this first-stage OLS file.

Key definition:
- `gPaper` is the score function defined by the paper's regression [terms](jargon_term.md) (intercept, main effects, [interactions](jargon_interaction.md)). It uses the [linear model](jargon_linear_model.md) setup.

Assumption package:
- The core package is `OLSMomentAssumptionsOfAttr` from the generic regression section, specialized to `φPaper` and `gStar`. It says the empirical Gram and cross moments converge to their attribute‑distribution targets under `xiAttr`. In the core‑idea flow, those targets are the design pushforward law `kappaDesign`, with population transport handled separately.
- `paper_ols_lln_of_score_assumptions_ae` derives the Gram/cross LLN part from existing `ScoreAssumptions` plus an `ObservationNoiseAssumptions` bundle that makes the feature-weighted noise term converge to 0, so the cross moment still targets `gStar` under `kappaDesign`. The algebraic split of the cross moment is factored into `crossVec_eq_meanHatZ_add_noise`.
- `PaperOLSDesignAssumptions` packages bounded/measurable features, bounded `gStar`, and the observation-noise LLN, while `DesignAttrIID` is supplied separately. From these:
  - `paper_ols_lln_of_design_ae` derives the LLN statement with limits expressed under the design pushforward law `kappaDesign`.
  - `paper_ols_attr_moments_of_design_ae` combines that LLN with inverse‑Gram stability to yield `OLSMomentAssumptionsOfAttr` a.e. under the design law.
- `PaperOLSFullRankAssumptions` is the explicit full‑rank premise that feeds the derivation of inverse‑Gram stability and identification (`hInv`/`hId`) from the design; the normal equations are now derived from well‑specification plus bounded/measurable features.
- `paper_ols_gramInv_tendsto_of_design_ae` derives inverse‑Gram convergence a.e. from the design bundle plus `PaperOLSFullRankAssumptions`.
- `paper_ols_fullRank_of_orthogonal` derives the full‑rank condition from an orthogonality/variation assumption on the paper features (`PaperOLSOrthogonalAssumptions`).
- `paper_ols_fullRank_of_posDef` derives the full‑rank condition from positive definiteness of the Gram matrix (`PaperOLSPosDefAssumptions`).
- `paper_ols_theta0_eq_of_normal_eq` derives the identification equation `θ0 = (attrGram)⁻¹ * attrCross` from the normal‑equation identity and full‑rank.
- `paper_ols_normal_eq_of_wellSpecified` derives the normal‑equation identity from well‑specification plus bounded/measurable paper features.
- `paper_ols_attr_moments_of_lln_fullrank_ae` packages Gram/cross LLN and inverse‑Gram stability into the a.e. `OLSMomentAssumptionsOfAttr` statement used by later theorems.
- In the Gram/cross convergence proofs, empirical means are now routed through `meanHatZ_tendsto_ae_of_score`, keeping the flow explicitly tied to `ScoreAssumptions` rather than standalone IID bundles.

Main results:
- `theta_tendsto_of_paper_ols_moments_ae` gives almost-everywhere [convergence](jargon_convergence.md) of the OLS coefficient estimates to `theta0`, given a separate identification equation for `theta0`.
- A non-AE version is provided for deterministic sequences.
- `theta_tendsto_of_paper_ols_design_ae` derives the same convergence from `DesignAttrIID` plus `PaperOLSDesignAssumptions` and the full‑rank condition, with normal equations derived from well‑specification.
- `attrMean_tendsto_of_paper_ols_gStar` / `attrM2_tendsto_of_paper_ols_gStar` combine OLS [convergence](jargon_convergence.md) with functional [continuity](jargon_continuity.md) to produce plug‑in mean/second‑moment convergence for the paper’s score.
- `attrMean_tendsto_of_paper_ols_moments_ae` / `attrM2_tendsto_of_paper_ols_moments_ae` provide the same [bridge](jargon_bridge.md) a.e. when the OLS moment assumptions hold along sample paths.
- `attrMean_tendsto_of_paper_ols_design_ae` / `attrM2_tendsto_of_paper_ols_design_ae` are the end‑to‑end a.e. bridges from the design‑side bundle plus full‑rank (and normal equations derived from well‑specification) to plug‑in moment convergence.
- `gPaper_eq_gTotalΘ_blocks` identifies the paper score with the block-sum total score (for any `blk`), so the OLS path can feed into the block/total [standard deviation](jargon_standard_deviation.md) chain.
- `functionalContinuity_gPaper_of_bounded` and `functionalContinuity_gTotalΘ_of_bounded` derive the required functional [continuity](jargon_continuity.md) for the paper score and total block score directly from bounded/measurable features.
- `functionalContinuity_gBlockTerm_of_bounded` does the same for each block score, using a block-specific feature map and the same bounded/measurable feature hypotheses.
- `attrMean_tendsto_of_paper_ols_gStar_total` / `attrM2_tendsto_of_paper_ols_gStar_total` and their a.e. counterparts lift the OLS assumptions from `gPaper` to the block-sum total score.
- `paper_ols_attr_moments_of_lln_fullrank_ae` assembles the a.e. moment package from [LLN](jargon_lln.md)-style and inverse-stability assumptions plus the normal equations (derived from well‑specification when needed) under the attribute distribution in use.

This file is the link from [regression](jargon_regression.md) / [OLS](jargon_ols.md) [consistency](jargon_consistency.md) to the [plug-in](jargon_plug_in.md) moment assumptions used in the [standard deviation](jargon_standard_deviation.md) consistency proofs.
