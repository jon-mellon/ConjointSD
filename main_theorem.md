# Main theorem narrative ([block](readable/jargon_block.md) [SD](readable/jargon_standard_deviation.md) only)

This document walks through the **[block](readable/jargon_block.md)‑level** end‑to‑end
[theorem](readable/jargon_theorem.md) chain.
The target is the [block](readable/jargon_block.md) components of the total score, not the total
score itself. The final wrapper is:
`paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`.
Note: the total-score wrapper
`paper_sd_total_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`
uses the experiment-subject sampling LLN bridge (`SubjectSamplingLLN`).
The implied ν-a.e. equality `gStar = gPop` is derived from the two LLN limits
(uniqueness of limits), not assumed as a separate transport axiom.

## Assumptions the reader must accept

This is the full set of assumptions required by the block‑level wrapper. The descriptions
reuse and extend the wording from `readable/Assumptions.md`.

### 1) [Randomized assignment](readable/jargon_randomization.md) (training design)
**Assumption**: `ConjointRandomizationStream` for `Atrain`.

**Meaning**:
- There exist randomization [random variables](readable/jargon_random_variable.md) `U i` and a
  [measurable](readable/jargon_measurable.md) map `f` such that
  `Atrain i = f (U i)` for all `i`.
- `U i` is [measurable](readable/jargon_measurable.md) for each `i`, and the `U i` are
  [IID](readable/jargon_iid.md) across indices.
- Each `U i` is [independent](readable/jargon_independent.md) of every
  [potential outcome](readable/jargon_potential_outcome.md) `Y x`.

**Intuition**: the experimental assignment is genuinely randomized, which supplies
[IID](readable/jargon_iid.md)‑style structure for the training design and supports
[identification](readable/jargon_identification.md) of the model.

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
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
\exists (R,\mathcal{M}_R, U:\mathbb{N}\to\Omega\to R, f:R\to Attr),\;
&(\forall i,\; U_i \text{ is measurable}) \land f \text{ is measurable} \\
&\land (\forall i,\; A_i = f \circ U_i) \\
&\land \text{Pairwise}(i \ne j \Rightarrow U_i \perp U_j \text{ under } \mu_{exp}) \\
&\land (\forall i,\; U_i \stackrel{d}{=} U_0 \text{ under } \mu_{exp}) \\
&\land (\forall i,x,\; U_i \perp Y_x \text{ under } \mu_{exp}).
\end{aligned}
\]
```
**English version**: there is a randomization [random variable](readable/jargon_random_variable.md)
sequence `U i` and a
[measurable](readable/jargon_measurable.md) map `f`
so that each `A i` is generated as `f (U i)`; the `U i` are measurable,
[IID](readable/jargon_iid.md) across indices, and each `U i` is independent of every
potential outcome `Y x` under `μexp`.

### 2) [IID](readable/jargon_iid.md) evaluation stream
**Assumption**: `EvalAttrIID` for `Aeval`.

**Meaning** (subassumptions):
- `EvalAttrIID.measA`: each `Aeval i` is [measurable](readable/jargon_measurable.md).
- `EvalAttrIID.indepA`: pairwise [independence](readable/jargon_independent.md) across indices.
- `EvalAttrIID.identA`: [identically distributed](readable/jargon_identically_distributed.md) across indices.

**Intuition**: the evaluation sample is a random sample of people/[profiles](readable/jargon_profile.md),
so [IID](readable/jargon_iid.md) is an assumption about the sampling process, not about
experimental [randomization](readable/jargon_randomization.md).

**Formal statement (Lean)**:
```lean
structure EvalAttrIID (A : ℕ → Ω → Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) κ)
  identA : ∀ i, IdentDistrib (A i) (A 0) κ κ
```
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&(\forall i,\; A_i \text{ is measurable}) \\
&\land \text{Pairwise}(i \ne j \Rightarrow A_i \perp A_j \text{ under } \kappa) \\
&\land (\forall i,\; A_i \stackrel{d}{=} A_0 \text{ under } \kappa).
\end{aligned}
\]
```
**English version**: each evaluation draw `A i` is [measurable](readable/jargon_measurable.md);
any two distinct draws are [independent](readable/jargon_independent.md); and every draw has the
same [distribution](readable/jargon_distribution.md) as `A 0` under `κ`.

### 3) Experiment-subject sampling
**Assumption**: `SubjectSamplingLLN`.

**Meaning** (subassumptions):
- `SubjectSamplingLLN.lln_gStar`: subject-average scores converge to `gStar`.
- `SubjectSamplingLLN.lln_gPop`: subject-average scores converge to `gPop`.

**Intuition**: experiment subjects are an IID sample from the population, so averaging
individual scoring functions recovers the population-mean scoring function.
The implied `gStar = gPop` ν-a.e. is derived from uniqueness of limits.

**Formal statement (Lean)**:
```lean
structure SubjectSamplingLLN
    (μexp : Measure Ω) (ν : Measure Attr) (μpop : Measure Person)
    (R : ℕ → Ω → Person) (gP : Person → Attr → ℝ) (Y : Attr → Ω → ℝ) : Prop where
  lln_gStar :
    ∀ x, ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n => gHatSubject (R := R) (gP := gP) n x ω)
        atTop
        (nhds (gStar (μexp := μexp) (Y := Y) x))
  lln_gPop :
    ∀ x, ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n => gHatSubject (R := R) (gP := gP) n x ω)
        atTop
        (nhds (gPop (μpop := μpop) gP x))
```
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&\forall x,\; \text{a.e.}_{\mu_{exp}}\; \lim_{n\to\infty}
\Big(\frac{1}{n}\sum_{i<n} g_P(R_i, x)\Big) = g^\star(x), \\
&\forall x,\; \text{a.e.}_{\mu_{exp}}\; \lim_{n\to\infty}
\Big(\frac{1}{n}\sum_{i<n} g_P(R_i, x)\Big) = g_{Pop}(x).
\end{aligned}
\]
```

### 4) Paper [OLS](readable/jargon_ols.md) design bundle
**Assumption**: `PaperOLSDesignAssumptions`.

**Meaning**:
Subassumptions:
- `obs_noise`: observation‑noise assumptions for the paper feature map.
- `meas_fMain`, `meas_fInter`: [measurability](readable/jargon_measurable.md) of main/[interaction](readable/jargon_interaction.md) features.
- `bound_fMain`, `bound_fInter`: uniform [boundedness](readable/jargon_boundedness.md) of main/interaction features.
- `meas_gStar`, `bound_gStar`: measurability and boundedness of `gStar` under `μexp`.

**Intuition**: the paper’s feature map and the true score are stable and bounded, so the
[normal equations](readable/jargon_normal_equations.md) and [LLN](readable/jargon_lln.md)
arguments are legitimate.

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
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&\text{ObservationNoiseAssumptions:} \\
&\forall i,a,\;
\mathbb{E}_{\mu_{exp}}\!\left[ Y^{obs}_i - g^\star(A_i) \,\middle|\, A_i = a \right] = 0, \\
&\forall i,\; \frac{1}{n}\sum_{k<n} \varphi_i(A_k)\bigl(Y^{obs}_k - g^\star(A_k)\bigr)
\to 0 \text{ a.e. as } n\to\infty. \\
&\text{PaperOLSDesignAssumptions:} \\
&\text{obs\_noise holds, } f_{Main}, f_{Inter} \text{ are measurable and uniformly bounded,} \\
&g^\star \text{ is measurable and uniformly bounded.}
\end{aligned}
\]
```
**English version**: the paper feature map has [measurable](readable/jargon_measurable.md),
uniformly [bounded](readable/jargon_boundedness.md) main and interaction components; the true
causal score `gStar` is measurable and uniformly bounded; and the observation noise has zero
[conditional mean](readable/jargon_conditional_mean.md) and satisfies a feature‑weighted
[LLN](readable/jargon_lln.md).

### 5) [Full‑rank](readable/jargon_full_rank.md) design
**Assumption**: `PaperOLSFullRankAssumptions`.

**Meaning**: the attribute‑[distribution](readable/jargon_distribution.md)
[Gram matrix](readable/jargon_gram_matrix.md) of the paper feature map is invertible.

Subassumption:
- `gram_isUnit`: the Gram matrix is a unit (invertible).

**Intuition**: the [regression](readable/jargon_regression.md) is identifiable (no collinearity under
the design [distribution](readable/jargon_distribution.md)).

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
**Formal statement (LaTeX)**:
```tex
\[
\operatorname{attrGram}(\xi_{Attr}, \varphi_{Paper}) \text{ is invertible.}
\]
```
**English version**: the [Gram matrix](readable/jargon_gram_matrix.md) of the paper feature map
under the attribute law `xiAttr` is invertible.

### 6) Full main‑effects basis
**Assumption**: `FullMainEffectsTerms`.

**Meaning**: the paper [term](readable/jargon_term.md) basis can represent any additive
main‑effects surface.

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
**Formal statement (LaTeX)**:
```tex
\[
\forall \alpha_0,\; \forall \text{ main }(k,\cdot),\;
\exists \beta,\; \forall x,\;
g^{Lin}_{\varphi,\beta}(x) = \alpha_0 + \sum_{k\in K} \text{main}_k(x_k).
\]
```
**English version**: for any intercept `α0` and any collection of per‑attribute main
effects, there exist [parameters](readable/jargon_parameter.md) `β` so that the
[linear‑in‑terms](readable/jargon_linear_in_terms.md) model `gLin` exactly reproduces the additive
surface `α0 + Σ_k main k (x k)` for all [profiles](readable/jargon_profile.md) `x`.

### 7) No [interactions](readable/jargon_interaction.md)
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
**Formal statement (LaTeX)**:
```tex
\[
\exists \alpha_0,\; \exists \text{ main }(k,\cdot),\; \forall x,\;
g^\star(x) = \alpha_0 + \sum_{k\in K} \text{main}_k(x_k).
\]
```
**English version**: there exists an intercept and per‑attribute main effects so that the
true causal score `gStar` is exactly additive in attributes for every profile.

### 8) [Weighted](readable/jargon_weighting.md) evaluation moments
**Assumption**: `EvalWeightMatchesPopMoments` (for every block score and every `m`).

**Meaning**: the weighted evaluation [mean](readable/jargon_mean.md) and weighted
[second moment](readable/jargon_second_moment.md) match the [population](readable/jargon_population.md)
mean and second moment under `ν` for the score being evaluated.

Subassumptions:
- `measA0`: measurability of `Aeval 0`.
- `mean_eq`: weighted [mean](readable/jargon_mean.md) equals `attrMean ν`.
- `m2_eq`: weighted [second moment](readable/jargon_second_moment.md) equals `attrM2 ν`.

**Intuition**: after [reweighting](readable/jargon_weighting.md), the evaluation sample is
representative of the target [population](readable/jargon_population.md) for the block scores.

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
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&A_0 \text{ is measurable,} \\
&\frac{\int w(a)\, s(a)\, d\kappa}{\int w(a)\, d\kappa} = \operatorname{attrMean}_\nu(s), \\
&\frac{\int w(a)\, s(a)^2\, d\kappa}{\int w(a)\, d\kappa} = \operatorname{attrM2}_\nu(s),
\end{aligned}
\]
```
**English version**: for the evaluation sample, the weight‑normalized [mean](readable/jargon_mean.md)
and [second moment](readable/jargon_second_moment.md) of score `s` match the
[population](readable/jargon_population.md) mean and second moment under `ν`.

### 9) Weighted evaluation [boundedness](readable/jargon_boundedness.md) (with IID)
**Assumption**: `SplitEvalWeightAssumptionsBounded` (for every block score and every `m`).

**Meaning**:
Subassumptions:
- `hIID`: `EvalAttrIID` for the evaluation draws.
- `hMeasG` / `hBoundG`: [measurability](readable/jargon_measurable.md) and
  [boundedness](readable/jargon_boundedness.md) of `gHat g θhat m`.
- `hMeasW` / `hBoundW`: measurability and boundedness of the
  [weights](readable/jargon_weighting.md) `w`.
- `hW0`: nonzero weight [mean](readable/jargon_mean.md) (`designMeanZ ≠ 0`).

**Intuition**: boundedness of the score and weights lets us derive the score‑level
[integrability](readable/jargon_integrable.md) conditions needed for the weighted
[LLN](readable/jargon_lln.md), while [IID](readable/jargon_iid.md) is assumed directly.

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
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&A \text{ is IID under } \rho, \\
&g^{Hat}_m \text{ and } w \text{ are measurable and uniformly bounded,} \\
&\mathbb{E}_\rho[Z] \ne 0 \text{ for } Z = Z_{comp}(A,w).
\end{aligned}
\]
```
**English version**: the evaluation attributes are [IID](readable/jargon_iid.md); both the
fitted score `gHat` and weights `w` are [measurable](readable/jargon_measurable.md) and
uniformly [bounded](readable/jargon_boundedness.md); and the mean of the weight process is
nonzero.

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
**Formal statement (LaTeX)**:
```tex
\[
0 < \varepsilon.
\]
```
**English version**: the tolerance parameter `ε` is strictly positive.

## 1) Start with randomized assignment

We assume [randomized assignment](readable/jargon_randomization.md) for the training stream,
and [IID](readable/jargon_iid.md) for the evaluation stream:
- `ConjointRandomizationStream` for `Atrain`.
- [IID](readable/jargon_iid.md) for `Aeval`.

**Formal bridge**:
- `DesignAttrIID.of_randomization_stream` derives [IID](readable/jargon_iid.md) for the
  training design only.

## 2) Add [OLS](readable/jargon_ols.md) design‑side conditions

We assume the paper OLS design bundle and full‑rank condition:
- `PaperOLSDesignAssumptions`
- `PaperOLSFullRankAssumptions`

These ensure the [normal equations](readable/jargon_normal_equations.md) are well behaved and
identify coefficients.

## 3) Add the no‑interactions structure and full main‑effects basis

We assume:
- `NoInteractions`
- `FullMainEffectsTerms`

**Formal bridge**:
- `wellSpecified_of_noInteractions_of_fullMainEffects` derives
[well‑specification](readable/jargon_well_specified.md) of the paper
[linear model](readable/jargon_linear_model.md).

## 4) Build the OLS moment [convergence](readable/jargon_convergence.md) chain

Key steps (theorem nodes in order):
- `paper_ols_gramInv_tendsto_of_design_ae`: [Gram matrix](readable/jargon_gram_matrix.md) inverse
  converges [a.e.](readable/jargon_almost_everywhere.md) along training paths.
- `paper_ols_attr_moments_of_design_ae`: packages Gram/[cross moment](readable/jargon_cross_moment.md)
  limits as `OLSMomentAssumptionsOfAttr`.
- `paper_ols_normal_eq_of_wellSpecified`: [well‑specification](readable/jargon_well_specified.md)
  gives the population [normal equations](readable/jargon_normal_equations.md).
- `paper_ols_theta0_eq_of_normal_eq`: solves the normal equations for `theta0`.
- `olsThetaHat_tendsto_of_moment_assumptions` and `olsThetaHat_tendsto_of_moment_assumptions_id`:
  [consistency](readable/jargon_consistency.md) of the OLS [estimator](readable/jargon_estimator.md).
- `theta_tendsto_of_paper_ols_design_ae`: assembles the chain to give `thetaHat → theta0`
  [a.e.](readable/jargon_almost_everywhere.md).

**Intuition**: random design + [boundedness](readable/jargon_boundedness.md) give moment
[convergence](readable/jargon_convergence.md); well‑specification pins the limit to `theta0`;
therefore OLS converges. We then push this convergence through the
[plug‑in](readable/jargon_plug_in.md) functionals using [continuity](readable/jargon_continuity.md)
at `θ0`, yielding the needed moment convergence.

## 5) Derive plug‑in moment convergence from OLS

We derive the plug‑in assumptions ([mean](readable/jargon_mean.md) + [second moment](readable/jargon_second_moment.md)
under `ν`) from:
- `theta_tendsto_of_paper_ols_design_ae` (OLS consistency),
- boundedness/[measurability](readable/jargon_measurable.md) of the paper features
  (gives functional [continuity](readable/jargon_continuity.md) under `ν`).

Formally:
- `functionalContinuity_gBlockTerm_of_bounded` and
  `blockFunctionalContinuity_gBlockTerm_of_bounded` give continuity of block scores at `θ0`,
- `plugInMomentAssumptions_blocks_of_theta_tendsto` converts `θhat → θ0` into
  `PlugInMomentAssumptions` for each block score.

## 6) [Weighted](readable/jargon_weighting.md) evaluation (block SD targets)

We combine:
- `EvalWeightMatchesPopMoments` for each block score and each `m`,
- `SplitEvalWeightAssumptionsBounded` for each block score and each `m`.

This yields block‑level [sequential consistency](readable/jargon_sequential_consistency.md) of the
weighted [SD](readable/jargon_standard_deviation.md) [estimator](readable/jargon_estimator.md).

## 7) Target interpretation (block targets)

No additional external-validity step is required at the block level in this wrapper:
the target block SDs are defined directly from the model-implied block scores
`gBlockTerm` under `ν`.

## 8) End‑to‑end block wrapper

The final block‑level result is:
- `paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`.

It asserts that, under the assumptions listed at the top, the weighted evaluation SDs
for **each block component** [converge](readable/jargon_convergence.md) (sequentially) to the
true [population](readable/jargon_population.md) block SDs.

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
    {Person : Type*} [MeasurableSpace Person]
    (μpop : Measure Person) [ProbMeasureAssumptions μpop]
    (R : ℕ → Ω → Person)
    (gP : Person → Profile K V → ℝ)
    (hRespLLN :
      SubjectSamplingLLN
        (μexp := μexp) (ν := ν) (μpop := μpop)
        (R := R) (gP := gP) (Y := Y))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ θ0 : PaperTerm Main Inter → ℝ,
      (∀ᵐ ω ∂μexp,
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
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b))
      ∧
      (∀ᵐ x ∂ν,
        gPop (μpop := μpop) gP x
          =
        gTotal
          (B := B)
          (g := gBlockTerm (blk := blk) (β := θ0)
            (φ :=
              φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x)
```
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&\exists \theta_0,\; \forall^{\mu_{exp}\text{-a.e.}} \omega,\; \exists M,\;
\forall m \ge M,\; \forall b, \\
&\quad \Bigl(\forall^{\rho\text{-a.e.}} \omega',\;
\forall^{\text{eventually}} n,\;
\operatorname{totalErr}(\rho,A_{eval},\nu,w,g_{Block},\theta_0,\hat\theta,m,n,\omega') < \varepsilon\Bigr) \\
&\quad \land\;
\operatorname{attrSD}_\nu\!\bigl(g_{Block}(b,\theta_0)\bigr)
=
\operatorname{attrSD}_\nu\!\bigl(g_{BlockTerm}(b,\theta_0)\bigr), \\
&\quad \text{and } g_{Pop}(x) = g_{Total}(x) \text{ for } \nu\text{-a.e. } x.
\end{aligned}
\]
```
**English version**: there exists a coefficient vector `θ0` such that, for `μexp`‑almost
every training path `ω`, there is a cutoff `M` where for all `m ≥ M` and every block `b`,
the weighted evaluation error `totalErr` is eventually below `ε` along `ρ`‑almost every
evaluation path, and the [population](readable/jargon_population.md)
[SD](readable/jargon_standard_deviation.md) of the model block score at `θ0` equals the
population SD of the true block term. In addition, the population-mean score
`gPop` equals the block-sum score `gTotal (gBlockTerm θ0)` ν-a.e., tying the block
targets to experiment-subject sampling transport.
