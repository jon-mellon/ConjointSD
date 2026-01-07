# PaperOLSConsistency.lean

Lean file: [ConjointSD/PaperOLSConsistency.lean](../ConjointSD/PaperOLSConsistency.lean)

This file specializes the regression [consistency](jargon_consistency.md) machinery to the paper's OLS [estimator](jargon_estimator.md) and [term](jargon_term.md) set. It uses `IsProbabilityMeasure` where probability assumptions are required, and the LLN statements target the experimental pushforward attribute law `kappaDesign := Measure.map (A 0) μexp` (the experiment data used to fit the model). In the code, this distribution is denoted `xiAttr`; the target population distribution `ν_pop` is not used in this first-stage OLS file.

Moment convergence facts:
- The core moment statement is that the inverse Gram and cross moments converge entrywise to their attribute‑distribution targets under `xiAttr`. In the core‑idea flow, those targets are the design pushforward law `kappaDesign`, with population transport handled separately.
- `paper_ols_lln_of_score_assumptions_ae` derives the Gram/cross LLN part from `DesignAttrIID`, bounded/measurable features, bounded `gStar`, and an `ObservationNoiseAssumptions` bundle that makes the feature-weighted noise term converge to 0, so the cross moment still targets `gStar` under `kappaDesign`. The algebraic split of the cross moment is factored into `crossVec_eq_meanHatZ_add_noise`.
- `PaperOLSDesignAssumptions` packages bounded/measurable features, bounded `gStar`, and the observation-noise LLN. For the design-based wrappers, `DesignAttrIID` is derived from `ConjointRandomizationStream`.
  - `paper_ols_lln_of_design_ae` derives the LLN statement with limits expressed under the design pushforward law `kappaDesign`.
  - `paper_ols_attr_moments_of_design_ae` combines that LLN with inverse‑Gram stability to yield the inverse‑Gram and cross‑moment convergence a.e. under the design law.
- `PaperOLSFullRankAssumptions` is the explicit full‑rank premise that feeds the derivation of inverse‑Gram stability and identification (`hInv`/`hId`) from the design; the normal equations are now derived from well‑specification plus bounded/measurable features.
- `paper_ols_gramInv_tendsto_of_design_ae` derives inverse‑Gram convergence a.e. from the design bundle plus `PaperOLSFullRankAssumptions`.
- `paper_ols_theta0_eq_of_normal_eq` derives the identification equation `θ0 = (attrGram)⁻¹ * attrCross` from the normal‑equation identity and full‑rank.
- `paper_ols_normal_eq_of_wellSpecified` derives the normal‑equation identity from well‑specification plus bounded/measurable paper features.
- `paper_ols_attr_moments_of_lln_fullrank_ae` packages Gram/cross LLN and inverse‑Gram stability into the a.e. convergence statement used by later theorems.
- In the Gram/cross convergence proofs, empirical means are routed through `meanHatZ_tendsto_ae_of_score`, which now takes `DesignAttrIID` plus boundedness/measurability.
- Design-based score integrability for Gram/cross terms is derived inline from boundedness/measurability.

Main results:
- `theta_tendsto_of_paper_ols_design_ae` derives almost-everywhere [convergence](jargon_convergence.md) of the OLS coefficient estimates to `theta0` from `ConjointRandomizationStream`, `PaperOLSDesignAssumptions`, and the full‑rank condition, with normal equations derived from well‑specification.
- `cont_mean_gBlockTerm_of_bounded` / `cont_m2_gBlockTerm_of_bounded` derive the required functional [continuity](jargon_continuity.md) for individual block scores directly from bounded/measurable features. The blockwise variants `cont_mean_blocks_gBlockTerm_of_bounded` and `cont_m2_blocks_gBlockTerm_of_bounded` provide the per-block continuity facts for all blocks.
- `paper_ols_attr_moments_of_lln_fullrank_ae` assembles the a.e. inverse‑Gram and cross‑moment convergence from [LLN](jargon_lln.md)-style and inverse-stability assumptions under the attribute distribution in use.

This file is the link from [regression](jargon_regression.md) / [OLS](jargon_ols.md) [consistency](jargon_consistency.md) to the [plug-in](jargon_plug_in.md) moment assumptions used in the [standard deviation](jargon_standard_deviation.md) consistency proofs.
