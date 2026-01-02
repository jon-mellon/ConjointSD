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

**Formal statement (Lean)**:
```lean
structure ConjointRandomizationStream
    [MeasurableSpace Attr] (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ) : Prop where
  exists_randomization :
    ∃ (R : Type 0) (_ : MeasurableSpace R) (U : ℕ → Ω → R) (f : R → Attr),
      (∀ i, Measurable (U i)) ∧
      Measurable f ∧
      (∀ i, A i = fun ω => f (U i ω)) ∧
      Pairwise (fun i j => IndepFun (U i) (U j) μexp) ∧
      (∀ i, IdentDistrib (U i) (U 0) μexp μexp) ∧
      ∀ i x, (fun ω => U i ω) ⟂ᵢ[μexp] (fun ω => Y x ω)
```
**English version**: there is a randomization variable sequence `U i` and a measurable map `f`
so that each `A i` is generated as `f (U i)`; the `U i` are measurable, i.i.d. across indices,
and each `U i` is independent of every potential outcome `Y x` under `μexp`.

### 2) IID evaluation stream
**Assumption**: `EvalAttrIID` for `Aeval`.

**Meaning** (subassumptions):
- `EvalAttrIID.measA`: each `Aeval i` is measurable.
- `EvalAttrIID.indepA`: pairwise independence across indices.
- `EvalAttrIID.identA`: identical distribution across indices.

**Intuition**: the evaluation sample is a random sample of people/profiles, so IID is an
assumption about the sampling process, not about experimental randomization.

**Formal statement (Lean)**:
```lean
structure EvalAttrIID (A : ℕ → Ω → Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) κ)
  identA : ∀ i, IdentDistrib (A i) (A 0) κ κ
```
**English version**: each evaluation draw `A i` is measurable; any two distinct draws are
independent; and every draw has the same distribution as `A 0` under `κ`.

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

**Formal statement (Lean)**:
```lean
structure ObservationNoiseAssumptions
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    {Term : Type*}
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : ℕ → Ω → ℝ)
    (φ : Term → Attr → ℝ) : Prop where
  condMean_zero :
    ∀ i a,
      condMean (κ := μexp)
          (fun ω => Yobs i ω - gStar (μexp := μexp) (Y := Y) (A i ω))
          (eventX (X := A i) a)
        = 0
  noise_lln :
    ∀ i,
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n : ℕ =>
            ((n : ℝ)⁻¹) *
              ∑ k ∈ Finset.range n,
                φ i (A k ω)
                  * (Yobs k ω - gStar (μexp := μexp) (Y := Y) (A k ω)))
          atTop
          (nhds 0)

structure PaperOLSDesignAssumptions
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : ℕ → Ω → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  obs_noise :
    ObservationNoiseAssumptions
      (μexp := μexp) (A := A) (Y := Y) (Yobs := Yobs)
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
  meas_fMain : ∀ m, Measurable (fMain m)
  meas_fInter : ∀ i, Measurable (fInter i)
  bound_fMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C
  bound_fInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C
  meas_gStar : Measurable (gStar (μexp := μexp) (Y := Y))
  bound_gStar : ∃ C, 0 ≤ C ∧ ∀ a, |gStar (μexp := μexp) (Y := Y) a| ≤ C
```
**English version**: the paper feature map has measurable, uniformly bounded main and
interaction components; the true causal score `gStar` is measurable and uniformly bounded;
and the observation noise has zero conditional mean and satisfies a feature-weighted LLN.

### 4) Full‑rank design
**Assumption**: `PaperOLSFullRankAssumptions`.

**Meaning**: the attribute‑distribution Gram matrix of the paper feature map is invertible.

Subassumption:
- `gram_isUnit`: the Gram matrix is a unit (invertible).

**Intuition**: the regression is identifiable (no collinearity under the design distribution).

**Formal statement (Lean)**:
```lean
structure PaperOLSFullRankAssumptions
    (xiAttr : Measure Attr)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  gram_isUnit :
    IsUnit
      (attrGram
        (xiAttr := xiAttr)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
```
**English version**: the Gram matrix of the paper feature map under the attribute law
`xiAttr` is invertible.

### 5) Full main‑effects basis
**Assumption**: `FullMainEffectsTerms`.

**Meaning**: the paper term basis can represent any additive main‑effects surface.

Subassumptions (as encoded by `FullMainEffectsTerms`):
- coverage of every main‑effects component by the term map,
- compatibility with the `PaperTerm` basis used by `φPaper`.

**Intuition**: if the world is additive, the model class is expressive enough to match it.

**Formal statement (Lean)**:
```lean
def FullMainEffectsTerms
    (φ : Term → Profile K V → ℝ) : Prop :=
  ∀ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∃ β : Term → ℝ,
      ∀ x : Profile K V,
        gLin (Attr := Profile K V) (Term := Term) (β := β) (φ := φ) x
          =
        α0 + ∑ k : K, main k (x k)
```
**English version**: for any intercept `α0` and any collection of per-attribute main
effects, there exists coefficients `β` so that `gLin` exactly reproduces the additive
surface `α0 + Σ_k main k (x k)` for all profiles `x`.

### 6) No interactions
**Assumption**: `NoInteractions`.

**Meaning**: the causal score is additive in attributes (no interaction effects in the
formal sense used by the project).

Subassumptions (as encoded by `NoInteractions`):
- the causal score can be written as a sum of main‑effect contributions only.

**Intuition**: there are no interaction terms in the true status‑assigning function.

**Formal statement (Lean)**:
```lean
def NoInteractions
    (μexp : Measure Ω) (Y : Profile K V → Ω → ℝ) : Prop :=
  ∃ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V, gStar (μexp := μexp) (Y := Y) x = α0 + ∑ k : K, main k (x k)
```
**English version**: there exists an intercept and per-attribute main effects so that the
true causal score `gStar` is exactly additive in attributes for every profile.

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

**Formal statement (Lean)**:
```lean
structure EvalWeightMatchesPopMoments
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (ν : Measure Attr) (w s : Attr → ℝ) : Prop where
  measA0 : Measurable (A 0)
  mean_eq :
    (∫ a, w a * s a ∂kappaDesign (κ := ρ) (A := A)) /
      (∫ a, w a ∂kappaDesign (κ := ρ) (A := A))
      =
    attrMean ν s
  m2_eq :
    (∫ a, w a * (s a) ^ 2 ∂kappaDesign (κ := ρ) (A := A)) /
      (∫ a, w a ∂kappaDesign (κ := ρ) (A := A))
      =
    attrM2 ν s
```
**English version**: for the evaluation sample, the weight-normalized mean and second
moment of score `s` match the population mean and second moment under `ν`.

### 8) Weighted evaluation boundedness (with IID)
**Assumption**: `SplitEvalWeightAssumptionsBounded` (for every block score and every `m`).

**Meaning**:
Subassumptions:
- `hIID`: `EvalAttrIID` for the evaluation draws.
- `hMeasG` / `hBoundG`: measurability and boundedness of `gHat g θhat m`.
- `hMeasW` / `hBoundW`: measurability and boundedness of the weights `w`.
- `hW0`: nonzero weight mean (`designMeanZ ≠ 0`).

**Intuition**: boundedness of the score and weights lets us derive the score‑level
integrability conditions needed for the weighted LLNs, while IID is assumed directly.

**Formal statement (Lean)**:
```lean
structure SplitEvalWeightAssumptionsBounded
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (w : Attr → ℝ) (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hIID : EvalAttrIID (κ := ρ) A
  hMeasG : Measurable (gHat g θhat m)
  hBoundG : ∃ C, 0 ≤ C ∧ ∀ a, |gHat g θhat m a| ≤ C
  hMeasW : Measurable w
  hBoundW : ∃ C, 0 ≤ C ∧ ∀ a, |w a| ≤ C
  hW0 : designMeanZ (κ := ρ) (Z := Zcomp (A := A) (g := w)) ≠ 0
```
**English version**: the evaluation attributes are IID; both the fitted score `gHat` and
weights `w` are measurable and uniformly bounded; and the mean of the weight process is
nonzero.

### 9) External validity (transport)
**Assumption**: `InvarianceAE`.

**Meaning** (subassumption):
- `InvarianceAE`: for each block, the model score equals the target score `ν`‑a.e.

**Intuition**: the experimental score function transports to the population support.

**Formal statement (Lean)**:
```lean
def InvarianceAE (ν : Measure Attr) (gExp gPop : Attr → ℝ) : Prop :=
  ∀ᵐ x ∂ν, gExp x = gPop x
```
**English version**: the experimental score and population target score agree for
`ν`-almost every attribute profile.

### 10) Epsilon positivity
**Assumption**: `EpsilonAssumptions`.

**Meaning** (subassumption):
- `EpsilonAssumptions.pos`: `0 < ε`.

**Intuition**: standard technical positivity for convergence bounds.

**Formal statement (Lean)**:
```lean
structure EpsilonAssumptions (ε : ℝ) : Prop where
  pos : 0 < ε
```
**English version**: the tolerance parameter `ε` is strictly positive.

## 1) Start with randomized assignment

We assume randomized assignment for the training stream, and IID for the evaluation stream:
- `ConjointRandomizationStream` for `Atrain`.
- IID for `Aeval`.

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

## 4) Build the OLS moment convergence chain

Key steps (theorem nodes in order):
- `paper_ols_gramInv_tendsto_of_design_ae`: Gram inverse converges a.e. along training paths.
- `paper_ols_attr_moments_of_design_ae`: packages Gram/cross limits as `OLSMomentAssumptionsOfAttr`.
- `paper_ols_normal_eq_of_wellSpecified`: well‑specification gives the population normal equations.
- `paper_ols_theta0_eq_of_normal_eq`: solves the normal equations for `theta0`.
- `olsThetaHat_tendsto_of_moment_assumptions` and `olsThetaHat_tendsto_of_moment_assumptions_id`:
  consistency of the OLS estimator.
- `theta_tendsto_of_paper_ols_design_ae`: assembles the chain to give `thetaHat → theta0` a.e.

**Intuition**: random design + boundedness give moment convergence; well‑specification pins the
limit to `theta0`; therefore OLS converges. We then push this convergence through the
plug‑in functionals using continuity at `θ0`, yielding the needed moment convergence.

## 5) Derive plug‑in moment convergence from OLS

We derive the plug‑in assumptions (mean + second moment under `ν`) from:
- `theta_tendsto_of_paper_ols_design_ae` (OLS consistency),
- boundedness/measurability of the paper features (gives functional continuity under `ν`).

Formally:
- `functionalContinuity_gBlockTerm_of_bounded` and
  `blockFunctionalContinuity_gBlockTerm_of_bounded` give continuity of block scores at `θ0`,
- `plugInMomentAssumptions_blocks_of_theta_tendsto` converts `θhat → θ0` into
  `PlugInMomentAssumptions` for each block score.

## 6) Weighted evaluation (block SD targets)

We combine:
- `EvalWeightMatchesPopMoments` for each block score and each `m`,
- `SplitEvalWeightAssumptionsBounded` for each block score and each `m`.

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

**Formal statement (Lean)**:
```lean
theorem paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization
    (Atrain : ℕ → Ω → Profile K V) (Yobs : ℕ → Ω → ℝ)
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Atrain) (Y := Y))
    (hMomBlocks : ∀ ω m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := Aeval) (ν := ν)
        (w := w)
        (s := gHat
          (gBlock
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
            b)
          (fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n) m))
    (hSplitBlocks :
      ∀ ω m b,
        SplitEvalWeightAssumptionsBounded
          (ρ := ρ) (A := Aeval) (w := w)
          (g := gBlock
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
            b)
          (θhat := fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n) m)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Atrain) (Y := Y) (Yobs := Yobs)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Atrain)) (fMain := fMain) (fInter := fInter))
    (hTerms :
      FullMainEffectsTerms (K := K) (V := V) (Term := PaperTerm Main Inter)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)))
    (hNoInt : NoInteractions (K := K) (V := V) (μexp := μexp) (Y := Y))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ θ0 : PaperTerm Main Inter → ℝ,
      ∀ᵐ ω ∂μexp,
        ∃ M : ℕ,
          ∀ m ≥ M,
            ∀ b : B,
              (∀ᵐ ω' ∂ρ,
                ∀ᶠ n : ℕ in atTop,
                  totalErr ρ Aeval (ν) w
                    (gBlock
                      (gB := fun b θ a =>
                        gBlockTerm (blk := blk) (β := θ)
                          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                      b)
                    θ0
                    (fun n =>
                      olsThetaHat
                        (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
                        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
                        n)
                    m n ω' < ε)
              ∧
              attrSD (ν)
                  (gBlock
                    (gB := fun b θ a =>
                      gBlockTerm (blk := blk) (β := θ)
                        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                    b θ0)
                =
                attrSD (ν)
                  (gBlockTerm (blk := blk) (β := θ0)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b)
```
**English version**: there exists a coefficient vector `θ0` such that, for `μexp`‑almost
every training path `ω`, there is a cutoff `M` where for all `m ≥ M` and every block `b`,
the weighted evaluation error `totalErr` is eventually below `ε` along `ρ`‑almost every
evaluation path, and the population SD of the model block score at `θ0` equals the
population SD of the true block term.
