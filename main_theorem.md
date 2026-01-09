# Main theorem narrative ([block](readable/jargon_block.md) [SD](readable/jargon_standard_deviation.md) only)

This document walks through the **[block](readable/jargon_block.md)‑level** end‑to‑end
[theorem](readable/jargon_theorem.md) chain.
The target is the [block](readable/jargon_block.md) components of the total score, not the total
score itself. The final wrapper is:
`paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`.
The implied ν_pop-a.e. equality `gStar = gPop` is derived from the two LLN limits
(uniqueness of limits), not assumed as a separate transport axiom.

## Target estimand (block SD)

**Words**: for each block `b`, the target is the [population](readable/jargon_population.md)
[SD](readable/jargon_standard_deviation.md) under `ν_pop` of the block contribution of the
population‑mean score function. This is a pure population quantity:
\[
\operatorname{SD}_{A\sim\nu_{pop}}\!\big(g_{pop}^{b}(A)\big),
\]
with no sampling assumptions required to define it. (IID enters only when analyzing the
estimator, not the estimand.)

**Lean name**: `paperBlockSD (ν_pop := ν_pop) blk β0 φ b`, i.e.
`attrSD ν_pop (paperTrueBlockScore blk β0 φ b)`.

**LaTeX (population formulation)**:
```tex
\[
\text{Let } g_{pop}(a) := \mathbb{E}_{I\sim\mu_{pop}}[g_P(I,a)]
\text{ and } A \sim \nu_{pop}.
\]
\[
g_{pop}^{b}(a) := \mathbb{E}_{I\sim\mu_{pop}}\!\left[g^{b}_P(I, a)\right],
\qquad
g_{pop}(a) = \sum_{b} g_{pop}^{b}(a),
\qquad \text{target} = \operatorname{SD}_{A\sim\nu_{pop}}\!\big(g_{pop}^{b}(A)\big).
\]
\[
\text{Equivalently: } \operatorname{SD}_{A\sim\nu_{pop}}\!\left(g_{pop}^{b}(A)\right)
\text{ with } g_{pop}(A) = \mathbb{E}_{I\sim\mu_{pop}}[g_P(I, A)].
\]
```

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
&(\forall i,\; U_i \text{ measurable}) \land f \text{ measurable} \\
&\land (\forall i,\; A_i(\omega) = f(U_i(\omega))) \\
&\land \text{Pairwise}\bigl((i\ne j)\Rightarrow \text{IndepFun}_{\mu_{exp}}(U_i,U_j)\bigr) \\
&\land (\forall i,\; \text{IdentDistrib}_{\mu_{exp}}(U_i,U_0)) \\
&\land (\forall i,x,\; \text{IndepFun}_{\mu_{exp}}(U_i, Y_x)).
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
&(\forall i,\; A_i \text{ measurable}) \\
&\land \text{Pairwise}\bigl((i\ne j)\Rightarrow \text{IndepFun}_{\kappa}(A_i,A_j)\bigr) \\
&\land (\forall i,\; \text{IdentDistrib}_{\kappa}(A_i,A_0)).
\end{aligned}
\]
```
**English version**: each evaluation draw `A i` is [measurable](readable/jargon_measurable.md);
any two distinct draws are [independent](readable/jargon_independent.md); and every draw has the
same [distribution](readable/jargon_distribution.md) as `A 0` under `κ`.

### 3) Experiment-subject sampling
**Assumptions**: `SubjectSamplingIID`, `SubjectScoreAssumptions`, `SubjectSamplingLLNStar`.

**Meaning** (subassumptions):
- `SubjectSamplingIID`: subjects are an IID sample from `μpop`.
- `SubjectScoreAssumptions`: subject-level scores are measurable and uniformly bounded under `μpop`.
- `SubjectSamplingLLNStar.lln_gStar`: subject-average scores converge to `gStar`.

**Intuition**: subject-level scores are well-behaved and subjects are IID from the population,
so a strong LLN yields convergence to `gPop`. Combined with the LLN-to-`gStar` assumption, the
implied `gStar = gPop` ν_pop-a.e. is derived from uniqueness of limits.

**Formal statement (Lean)**:
```lean
structure SubjectSamplingIID
    (μexp : Measure Ω) (μpop : Measure Person) (R : ℕ → Ω → Person) : Prop where
  measR : ∀ i, Measurable (R i)
  indepR : Pairwise (fun i j => IndepFun (R i) (R j) μexp)
  identR : ∀ i, Measure.map (R i) μexp = μpop

structure SubjectScoreAssumptions
    (μpop : Measure Person) (gP : Person → Attr → ℝ) : Prop where
  meas_gP : ∀ x, Measurable (fun p => gP p x)
  bound_gP : ∀ x, ∃ C, 0 ≤ C ∧ ∀ p, |gP p x| ≤ C

structure SubjectSamplingLLNStar
    (μexp : Measure Ω) (ν_pop : Measure Attr) (μpop : Measure Person)
    (R : ℕ → Ω → Person) (gP : Person → Attr → ℝ) (Y : Attr → Ω → ℝ) : Prop where
  lln_gStar :
    ∀ x, ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n => gHatSubject (R := R) (gP := gP) n x ω)
        atTop
        (nhds (gStar (μexp := μexp) (Y := Y) x))

```
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&\text{IID subject sampling: } R_i \text{ measurable, Pairwise}\bigl(\text{IndepFun}_{\mu_{exp}}(R_i,R_j)\bigr), \\
&\qquad\qquad\qquad\qquad \text{and } \operatorname{Measure.map}(R_i,\mu_{exp}) = \mu_{pop}. \\
&\text{Score regularity: } g_P(\cdot,x) \text{ is measurable and uniformly bounded under } \mu_{pop}. \\
&\forall x,\; \text{a.e.}_{\mu_{exp}}\; \lim_{n\to\infty}
\Big(\frac{1}{n}\sum_{i<n} g_P(R_i, x)\Big) = g^\star(x).
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
    (μexp : Measure Ω) [IsProbabilityMeasure μexp]
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
    (μexp : Measure Ω) [IsProbabilityMeasure μexp]
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

### 6) Main‑effects representable
**Assumption**: `MainEffectsRepresentable`.

**Meaning**: whenever the true causal score is additive, the paper
[term](readable/jargon_term.md) basis can represent that specific additive
main‑effects surface.

**Intuition**: if the world is additive, the model class can match the true additive surface
without needing to represent every possible additive surface.

**Formal statement (Lean)**:
```lean
def MainEffectsRepresentable
    (μexp : Measure Ω) (Y : Profile K V → Ω → ℝ)
    (φ : Term → Profile K V → ℝ) : Prop :=
  ∀ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    (∀ x : Profile K V, gStar (μexp := μexp) (Y := Y) x = α0 + ∑ k : K, main k (x k)) →
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
\Bigl( g^{Star}(x) = \alpha_0 + \sum_{k\in K} \text{main}_k(x_k) \Bigr)
\Rightarrow
\exists \beta,\; \forall x,\;
g^{Lin}_{\varphi,\beta}(x) = \alpha_0 + \sum_{k\in K} \text{main}_k(x_k).
\]
```
**English version**: if the true causal score equals an additive surface
`α0 + Σ_k main k (x k)`, then there exist [parameters](readable/jargon_parameter.md) `β`
so that the [linear‑in‑terms](readable/jargon_linear_in_terms.md) model `gLin` exactly
reproduces that surface for all [profiles](readable/jargon_profile.md) `x`.

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

### 8) Evaluation sample is IID from the population
**Assumption**: `EvalAttrLawEqPop`.

**Meaning**: the evaluation attribute distribution equals the target population law `ν_pop`.

Subassumptions:
- `measA`: measurability of each `Aeval i`.
- `indepA`: pairwise independence of evaluation draws under `ρ`.
- `identA`: each evaluation draw has law `ν_pop`.

**Intuition**: the evaluation sample is a simple random sample from the target population.

**Formal statement (Lean)**:
```lean
structure EvalAttrLawEqPop
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (ν_pop : Measure Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) ρ)
  identA : ∀ i, Measure.map (A i) ρ = ν_pop
```
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&(\forall i,\; A_i \text{ measurable}) \\
&\land \text{Pairwise}\bigl((i\ne j)\Rightarrow \text{IndepFun}_{\rho}(A_i,A_j)\bigr) \\
&\land (\forall i,\; \operatorname{Measure.map}(A_i,\rho) = \nu_{pop}).
\end{aligned}
\]
```
**English version**: the evaluation attributes are sampled IID from the population law `ν_pop`.

### 9) Evaluation [boundedness](readable/jargon_boundedness.md) (with IID)
**Assumption**: `SplitEvalAssumptionsBounded` (for every block score and every `m`).

**Meaning**:
Subassumptions:
- `hIID`: `EvalAttrIID` for the evaluation draws.
- `hMeasG` / `hBoundG`: [measurability](readable/jargon_measurable.md) and
  [boundedness](readable/jargon_boundedness.md) of `gHat g θhat m`.

**Intuition**: boundedness of the score lets us derive the score‑level
[integrability](readable/jargon_integrable.md) conditions needed for the
[LLN](readable/jargon_lln.md), while [IID](readable/jargon_iid.md) is assumed directly.

**Formal statement (Lean)**:
```lean
structure SplitEvalAssumptionsBounded
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hIID : EvalAttrIID (κ := ρ) A
  hMeasG : Measurable (gHat g θhat m)
  hBoundG : ∃ C, 0 ≤ C ∧ ∀ a, |gHat g θhat m a| ≤ C
```
**Formal statement (LaTeX)**:
```tex
\[
\begin{aligned}
&\text{EvalAttrIID}_{\rho}(A), \\
&g^{Hat}_m \text{ measurable and uniformly bounded: } \exists C,\; 0 \le C \land
\forall a,\; |g^{Hat}_m(a)| \le C.
\end{aligned}
\]
```
**English version**: the evaluation attributes are [IID](readable/jargon_iid.md); the fitted
score `gHat` is [measurable](readable/jargon_measurable.md) and uniformly
[bounded](readable/jargon_boundedness.md).

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

## 3) Add the no‑interactions structure and true‑surface representability

We assume:
- `NoInteractions`
- `MainEffectsRepresentable`

**Formal bridge**:
- `wellSpecified_of_noInteractions_of_mainEffectsRepresentable` derives
[well‑specification](readable/jargon_well_specified.md) of the paper
[linear model](readable/jargon_linear_model.md).

## 4) Build the OLS moment [convergence](readable/jargon_convergence.md) chain

Key steps (theorem nodes in order):
- `paper_ols_gramInv_tendsto_of_design_ae`: [Gram matrix](readable/jargon_gram_matrix.md) inverse
  converges [a.e.](readable/jargon_almost_everywhere.md) along training paths.
- `paper_ols_attr_moments_of_design_ae`: packages Gram/[cross moment](readable/jargon_cross_moment.md)
  limits and inverse‑Gram convergence a.e. under `kappaDesign`.
- `paper_ols_normal_eq_of_wellSpecified`: [well‑specification](readable/jargon_well_specified.md)
  gives the population [normal equations](readable/jargon_normal_equations.md).
- `paper_ols_theta0_eq_of_normal_eq`: solves the normal equations for `theta0`.
- `olsThetaHat_tendsto_of_attr_moments`:
  [consistency](readable/jargon_consistency.md) of the OLS [estimator](readable/jargon_estimator.md)
  from attribute‑distribution moments plus identification.
- `theta_tendsto_of_paper_ols_design_ae`: assembles the chain to give `thetaHat → theta0`
  [a.e.](readable/jargon_almost_everywhere.md).

**Intuition**: random design + [boundedness](readable/jargon_boundedness.md) give moment
[convergence](readable/jargon_convergence.md); well‑specification pins the limit to `theta0`;
therefore OLS converges. We then push this convergence through the
[plug‑in](readable/jargon_plug_in.md) functionals using [continuity](readable/jargon_continuity.md)
at `θ0`, yielding the needed moment convergence.

## 5) Derive plug‑in moment convergence from OLS

We derive the plug‑in assumptions ([mean](readable/jargon_mean.md) + [second moment](readable/jargon_second_moment.md)
under `ν_pop`) from:
- `theta_tendsto_of_paper_ols_design_ae` (OLS consistency),
- boundedness/[measurability](readable/jargon_measurable.md) of the paper features
  (gives functional [continuity](readable/jargon_continuity.md) under `ν_pop`).

Formally:
- `cont_mean_blocks_gBlockTerm_of_bounded` and
  `cont_m2_blocks_gBlockTerm_of_bounded` give continuity of block scores at `θ0`,
- `attrMean_tendsto_of_theta_tendsto` / `attrM2_tendsto_of_theta_tendsto` convert
  `θhat → θ0` into mean/second‑moment convergence for each block score.

## 6) Evaluation representativeness (block SD targets)

We combine:
- `EvalAttrLawEqPop` (evaluation attributes are an IID draw from `ν_pop`),
- `SplitEvalAssumptionsBounded` for each block score and each `m`.

This yields block‑level [sequential consistency](readable/jargon_sequential_consistency.md) of the
[SD](readable/jargon_standard_deviation.md) [estimator](readable/jargon_estimator.md) under SRS.

## 7) Target interpretation (block targets)

No additional external-validity step is required at the block level in this wrapper:
the target block SDs are defined directly from the model-implied block scores
`gBlockTerm` under `ν_pop`.

## 8) End‑to‑end block wrapper

The final block‑level result is:
- `paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`.

It asserts that, under the assumptions listed at the top, the evaluation SDs
for **each block component** [converge](readable/jargon_convergence.md) (sequentially) to the
true [population](readable/jargon_population.md) block SDs.

**Formal statement (Lean)**:
```lean
theorem paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization
    (Atrain : ℕ → Ω → Profile K V) (Yobs : ℕ → Ω → ℝ)
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Atrain) (Y := Y))
    (hLawEval : EvalAttrLawEqPop (ρ := ρ) (A := Aeval) (ν_pop := ν_pop))
    (hSplitBlocks :
      ∀ ω m b,
        SplitEvalAssumptionsBounded
          (ρ := ρ) (A := Aeval)
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
      MainEffectsRepresentable
        (K := K) (V := V) (Term := PaperTerm Main Inter)
        (μexp := μexp) (Y := Y)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)))
    (hNoInt : NoInteractions (K := K) (V := V) (μexp := μexp) (Y := Y))
    {Person : Type*} [MeasurableSpace Person]
    (μpop : Measure Person) [IsProbabilityMeasure μpop]
    (R : ℕ → Ω → Person)
    (gP : Person → Profile K V → ℝ)
    (hSubjectIID :
      SubjectSamplingIID (μexp := μexp) (μpop := μpop) (R := R))
    (hSubjectScore :
      SubjectScoreAssumptions (μpop := μpop) (gP := gP))
    (hSubjectLLNStar :
      SubjectSamplingLLNStar
        (μexp := μexp) (ν_pop := ν_pop) (μpop := μpop)
        (R := R) (gP := gP) (Y := Y))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ θ0 : PaperTerm Main Inter → ℝ,
      (∀ᵐ ω ∂μexp,
        ∃ M : ℕ,
          ∀ m ≥ M,
            ∀ b : B,
              (∀ᵐ ω' ∂ρ,
                ∀ᶠ n : ℕ in atTop,
                  totalErr ρ Aeval (ν_pop)
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
              attrSD (ν_pop)
                  (gBlock
                    (gB := fun b θ a =>
                      gBlockTerm (blk := blk) (β := θ)
                        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                    b θ0)
                =
                attrSD (ν_pop)
                  (gBlockTerm (blk := blk) (β := θ0)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b))
      ∧
      (∀ᵐ x ∂ν_pop,
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
&\hat\theta_{\omega}(n) :=
\operatorname{olsThetaHat}\!\bigl(A_k = A^{train}_k(\omega),\; Y_k = Y^{obs}_k(\omega),\; \varphi=\varphi_{Paper}\bigr), \\
&g_{Block}^{b}(\theta)(a) :=
g_{Block}\!\Bigl(g_B = (b,\theta,a)\mapsto
g_{BlockTerm}(\text{blk},\theta,\varphi_{Paper})(b,a)\Bigr)(b,\theta,a), \\
&g_{BlockTerm}^{b}(\theta)(a) :=
g_{BlockTerm}(\text{blk},\theta,\varphi_{Paper})(b,a).
\end{aligned}
\]
\[
\begin{aligned}
&\exists \theta_0:\text{PaperTerm}\to\mathbb{R},\;
\forall^{\mu_{exp}\text{-a.e.}} \omega,\; \exists M,\;
\forall m \ge M,\; \forall b, \\
&\quad \Bigl(\forall^{\rho\text{-a.e.}} \omega',\;
\forall^{\text{eventually}} n,\;
\operatorname{totalErr}\!\Bigl(\rho,A_{eval},\nu_{pop},
g_{Block}^{b},\theta_0,\hat\theta_{\omega},m,n,\omega'\Bigr) < \varepsilon\Bigr) \\
&\quad \land\;
\operatorname{attrSD}_{\nu_{pop}}\!\bigl(g_{Block}^{b}(\theta_0)\bigr)
=
\operatorname{attrSD}_{\nu_{pop}}\!\bigl(g_{BlockTerm}^{b}(\theta_0)\bigr), \\
&\quad \text{and } \forall^{\nu_{pop}\text{-a.e.}} x,\;
g_{Pop}(x) =
g_{Total}\!\Bigl(g_{BlockTerm}(\theta_0)\Bigr)(x),
\end{aligned}
\]
```
**English version**: there exists a coefficient vector `θ0` such that, for `μexp`‑almost
every training path `ω`, there is a cutoff `M` where for all `m ≥ M` and every block `b`,
the evaluation error `totalErr` is eventually below `ε` along `ρ`‑almost every
evaluation path, and the [population](readable/jargon_population.md)
[SD](readable/jargon_standard_deviation.md) of the model block score at `θ0` equals the
population SD of the true block term. In addition, the population-mean score
`gPop` equals the block-sum score `gTotal (gBlockTerm θ0)` ν_pop-a.e., tying the block
targets to experiment-subject sampling transport.
