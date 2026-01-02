# Main theorem narrative (end-to-end)

This document walks through the end-to-end theorem chain that starts from randomized assignment and ends with sequential consistency of the predicted population SD for the paper OLS model. It is written to mirror the flow of `core_idea.md` while pointing to the formal nodes used in the chain.

## 1) Start with randomized assignment

We assume a randomized assignment stream for attributes:
- **Assumption**: `ConjointRandomizationStream` (see `ConjointSD/Assumptions.lean`).
- **Intuition**: the attributes shown in the conjoint are generated from i.i.d. randomization variables, independent of potential outcomes.

**Formal bridge**:
- `DesignAttrIID.of_randomization_stream` turns this randomization into i.i.d. attribute draws (`DesignAttrIID`).
- This is the link from experimental design to the i.i.d. law needed for later [consistency](readable/jargon_consistency.md).

## 2) Add OLS design-side conditions

We then assume the paper OLS design bundle:
- `PaperOLSDesignAssumptions`: bounded/measurable features, bounded `gStar`, and a noise LLN.
- `PaperOLSFullRankAssumptions`: the Gram matrix is invertible (full rank).

**Intuition**: these are standard conditions to make OLS behave well and to ensure the normal equations identify coefficients.

## 3) Add the no-interactions structure and a full main-effects basis

This is the structural modeling assumption:
- `NoInteractions`: the causal score `gStar` is additive in attributes (no [interactions](readable/jargon_interaction.md)).
- `FullMainEffectsTerms` for the paper feature map `phiPaper`: the [term](readable/jargon_term.md) basis can represent any additive main-effects surface.

**Intuition**: no interactions says the true causal function is a sum of main effects; the full main-effects basis says the model class can represent that sum exactly.

## 4) Derive well-specification from no interactions

**Formal bridge**:
- `wellSpecified_of_noInteractions_of_fullMainEffects` (in `ConjointSD/WellSpecifiedFromNoInteractions.lean`).

**Meaning**:
- There exists a coefficient vector `theta0` such that the linear model `gLin theta0 phiPaper` matches `gStar` exactly. This is [well-specified](readable/jargon_well_specified.md) but derived, not assumed.

## 5) Build the OLS moment convergence chain

With the design conditions in place, we can now prove OLS consistency for `theta0`.

Key steps (theorem nodes in order):
- `paper_ols_gramInv_tendsto_of_design_ae`: Gram inverse converges along almost every training path.
- `paper_ols_attr_moments_of_design_ae`: packages the Gram/cross moment limits into `OLSMomentAssumptionsOfAttr`.
- `paper_ols_normal_eq_of_wellSpecified`: uses well-specification to derive the normal equations at the population limit.
- `paper_ols_theta0_eq_of_normal_eq`: turns the normal equations into the identification equation `theta0 = gramInv * cross`.
- `olsThetaHat_tendsto_of_moment_assumptions` and `olsThetaHat_tendsto_of_moment_assumptions_id`: gives `thetaHat -> theta0` from those moments.
- `theta_tendsto_of_paper_ols_design_ae`: combines the above to conclude `thetaHat -> theta0` along almost every training path.

**Intuition**:
- The random design plus boundedness gives moment convergence; well-specification pins down the limit to the true `theta0`; hence the OLS estimator converges.

## 6) Weighted evaluation sample (transport to the population)

The evaluation stage uses **weights** to align the evaluation sample with the target population distribution.

Key objects:
- `w : Attr → ℝ` are the evaluation weights.
- `Aeval : ℕ → Ω → Attr` are evaluation draws.
- `ν` is the target population attribute distribution.

Two assumption bundles encode the weighted transport:

1) `EvalWeightMatchesPopMoments`:
   - This says the **weighted** evaluation moments match the population moments.
   - Concretely, the weighted mean and weighted second moment under the evaluation draw equal `attrMean ν` and `attrM2 ν`.

2) `SplitEvalWeightAssumptions`:
   - This bundles IID/integrability conditions for the weighted evaluation process.
   - It ensures the weighted LLNs used in sequential consistency are valid for the weighted score process.

**Intuition**:
- The evaluation sample may not be distributed like the population, so we reweight it.
- These assumptions make the weighted sample behave as if it were drawn from `ν`, so plug‑in SD estimates target the population SD.

## 7) Add the external-validity link

The transport step needs a direct equality of score functions on the target support:
- `InvarianceAE (ν := ν) (gStar (μexp := μexp) (Y := Y)) gTrue`.

**Intuition**:
- The experimental score function agrees with the population score function almost everywhere under `ν`.
- This is the explicit external-validity assumption in `core_idea.md`.

## 8) End-to-end wrapper (randomization to population SD)

Finally, the full end-to-end result:
- `paper_sd_total_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`.

**What it does**:
- Starts from `ConjointRandomizationStream`.
- Derives `DesignAttrIID`.
- Uses `NoInteractions` + `FullMainEffectsTerms` to derive well-specification and choose `theta0`.
- Uses OLS convergence + weighted evaluation to get SD consistency for `gTotalΘ θ0`.
- Uses `InvarianceAE` to move from `gStar` to the true population score `gTrue`.

**Conclusion (plain language)**:
There exists a coefficient vector `theta0` such that, with randomized assignment, the paper OLS design assumptions, and external validity, the weighted plug‑in SD converges to the population SD of the true score function.

## Where this matches core_idea

- **Stage 1 (identify the status rule)**: randomization + no interactions + full main-effects basis yield a well-specified linear rule with coefficients `theta0`.
- **Stage 2 (transport to the population)**: evaluation weighting plus continuity deliver convergence of predicted population SDs.

So the chain formalizes the core idea: estimate the additive status rule in the experiment, then use it to get consistent estimates of population status dispersion.
