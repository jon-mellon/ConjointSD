# Main theorem narrative (block SD only)

This document walks through the **block‑level** end‑to‑end theorem chain. The target is the
block components of the total score, not the total score itself. The final wrapper is:
`paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`.

## Assumptions the reader must accept

This is the full set of assumptions required by the block‑level wrapper. The descriptions
reuse and extend the wording from `readable/Assumptions.md`.

### 1) Randomized assignment (training design)
**Assumption**: `ConjointRandomizationStream` for `Atrain`.

**Meaning**:
- There exist randomization variables `U i` and a measurable map `f` such that
  `Atrain i = f (U i)` for all `i`.
- `U i` is measurable for each `i`, and the `U i` are i.i.d. across indices.
- Each `U i` is independent of every potential outcome `Y x`.

**Intuition**: the experimental assignment is genuinely randomized, which supplies IID‑style
structure for the training design and supports identification of the model.

### 2) IID evaluation stream
**Assumption**: `EvalAttrIID` for `Aeval` (packaged inside `SplitEvalWeightAssumptions`).

**Meaning** (subassumptions):
- `EvalAttrIID.measA`: each `Aeval i` is measurable.
- `EvalAttrIID.indepA`: pairwise independence across indices.
- `EvalAttrIID.identA`: identical distribution across indices.

**Intuition**: the evaluation sample is a random sample of people/profiles, so IID is an
assumption about the sampling process, not about experimental randomization.

### 3) Paper OLS design bundle
**Assumption**: `PaperOLSDesignAssumptions`.

**Meaning**:
Subassumptions:
- `obs_noise`: observation‑noise assumptions for the paper feature map.
- `meas_fMain`, `meas_fInter`: measurability of main/interactions features.
- `bound_fMain`, `bound_fInter`: uniform boundedness of main/interactions features.
- `meas_gStar`, `bound_gStar`: measurability and boundedness of `gStar` under `μexp`.

**Intuition**: the paper’s feature map and the true score are stable and bounded, so the
normal‑equation and LLN arguments are legitimate.

### 4) Full‑rank design
**Assumption**: `PaperOLSFullRankAssumptions`.

**Meaning**: the attribute‑distribution Gram matrix of the paper feature map is invertible.

Subassumption:
- `gram_isUnit`: the Gram matrix is a unit (invertible).

**Intuition**: the regression is identifiable (no collinearity under the design distribution).

### 5) Full main‑effects basis
**Assumption**: `FullMainEffectsTerms`.

**Meaning**: the paper term basis can represent any additive main‑effects surface.

Subassumptions (as encoded by `FullMainEffectsTerms`):
- coverage of every main‑effects component by the term map,
- compatibility with the `PaperTerm` basis used by `φPaper`.

**Intuition**: if the world is additive, the model class is expressive enough to match it.

### 6) No interactions
**Assumption**: `NoInteractions`.

**Meaning**: the causal score is additive in attributes (no interaction effects in the
formal sense used by the project).

Subassumptions (as encoded by `NoInteractions`):
- the causal score can be written as a sum of main‑effect contributions only.

**Intuition**: there are no interaction terms in the true status‑assigning function.

### 7) Weighted evaluation moments
**Assumption**: `EvalWeightMatchesPopMoments` (for every block score and every `m`).

**Meaning**: the weighted evaluation mean and weighted second moment match the population
mean and second moment under `ν` for the score being evaluated.

Subassumptions:
- `measA0`: measurability of `Aeval 0`.
- `mean_eq`: weighted mean equals `attrMean ν`.
- `m2_eq`: weighted second moment equals `attrM2 ν`.

**Intuition**: after reweighting, the evaluation sample is representative of the target
population for the block scores.

### 8) Weighted evaluation score/weight conditions (with IID)
**Assumption**: `SplitEvalWeightAssumptions` (for every block score and every `m`).

**Meaning**:
Subassumptions:
- `hIID`: `EvalAttrIID` for the evaluation draws.
- `hScore`: score assumptions for `gHat g θhat m`.
- `hWeight`: score assumptions for weights `w`.
- `hWeightScore`: score assumptions for `w * gHat`.
- `hWeightScoreSq`: score assumptions for `w * (gHat)^2`.
- `hW0`: nonzero weight mean (`designMeanZ ≠ 0`).

**Intuition**: the weighted evaluation process has enough integrability and stability to
apply weighted LLNs, and IID is assumed directly for the evaluation draws.

### 9) External validity (transport)
**Assumption**: `InvarianceAE`.

**Meaning** (subassumption):
- `InvarianceAE`: for each block, the model score equals the target score `ν`‑a.e.

**Intuition**: the experimental score function transports to the population support.

### 10) Epsilon positivity
**Assumption**: `EpsilonAssumptions`.

**Meaning** (subassumption):
- `EpsilonAssumptions.pos`: `0 < ε`.

**Intuition**: standard technical positivity for convergence bounds.

## 1) Start with randomized assignment

We assume randomized assignment for the training stream, and IID for the evaluation stream:
- `ConjointRandomizationStream` for `Atrain`.
- IID for `Aeval` (via `SplitEvalWeightAssumptions`).

**Formal bridge**:
- `DesignAttrIID.of_randomization_stream` derives IID for the training design only.

## 2) Add OLS design‑side conditions

We assume the paper OLS design bundle and full‑rank condition:
- `PaperOLSDesignAssumptions`
- `PaperOLSFullRankAssumptions`

These ensure the normal equations are well behaved and identify coefficients.

## 3) Add the no‑interactions structure and full main‑effects basis

We assume:
- `NoInteractions`
- `FullMainEffectsTerms`

**Formal bridge**:
- `wellSpecified_of_noInteractions_of_fullMainEffects` derives well‑specification of
  the paper linear model.

## 4) Build the OLS moment convergence chain (optional)

Key steps (theorem nodes in order):
- `paper_ols_gramInv_tendsto_of_design_ae`: Gram inverse converges a.e. along training paths.
- `paper_ols_attr_moments_of_design_ae`: packages Gram/cross limits as `OLSMomentAssumptionsOfAttr`.
- `paper_ols_normal_eq_of_wellSpecified`: well‑specification gives the population normal equations.
- `paper_ols_theta0_eq_of_normal_eq`: solves the normal equations for `theta0`.
- `olsThetaHat_tendsto_of_moment_assumptions` and `olsThetaHat_tendsto_of_moment_assumptions_id`:
  consistency of the OLS estimator.
- `theta_tendsto_of_paper_ols_design_ae`: assembles the chain to give `thetaHat → theta0` a.e.

**Intuition**: random design + boundedness give moment convergence; well‑specification pins the
limit to `theta0`; therefore OLS converges. In the current Route‑1 proof, we do **not**
use this chain to derive plug‑in moments; it is kept as a separate justification pathway.

## 5) Route 1: plug‑in moment convergence (assumed)

The sequential‑consistency chain now assumes plug‑in mean and second‑moment convergence
directly, via `PlugInMomentAssumptions` for each block score.

Key component:
- `PlugInMomentAssumptions` for each block score (mean + second‑moment convergence under `ν`).

## 6) Weighted evaluation (block SD targets)

We combine:
- `EvalWeightMatchesPopMoments` for each block score and each `m`,
- `SplitEvalWeightAssumptions` for each block score and each `m`.

This yields block‑level sequential consistency of the weighted SD estimator.

## 7) External validity (block targets)

We add:
- `InvarianceAE` linking the model‑implied block scores to the population target
  block scores under `ν`.

This turns consistency for the model’s block SDs into consistency for the **true**
block SDs.

## 8) End‑to‑end block wrapper

The final block‑level result is:
- `paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`.

It asserts that, under the assumptions listed at the top, the weighted evaluation SDs
for **each block component** converge (sequentially) to the true population block SDs.
