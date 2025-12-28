import Mathlib

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

/-- Empirical mean: (1/n) • ∑_{i<n} Z i ω. -/
def meanHatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) • (Finset.sum (Finset.range n) fun i => Z i ω)

/-- Empirical second moment: (1/n) • ∑_{i<n} (Z i ω)^2. -/
def m2HatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) • (Finset.sum (Finset.range n) fun i => (Z i ω) ^ 2)

/-- Plug-in empirical variance proxy: m2Hat - (meanHat)^2. -/
def varHatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  m2HatZ (Z := Z) n ω - (meanHatZ (Z := Z) n ω) ^ 2

/-- Plug-in empirical SD proxy: √(varHat). -/
def sdHatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (varHatZ (Z := Z) n ω)

/-- Population mean: ∫ Z 0 dμ. -/
def popMeanZ (Z : ℕ → Ω → ℝ) : ℝ :=
  ∫ ω, Z 0 ω ∂μ

/-- Population second moment: ∫ (Z 0)^2 dμ. -/
def popM2Z (Z : ℕ → Ω → ℝ) : ℝ :=
  ∫ ω, (Z 0 ω) ^ 2 ∂μ

/-- Population variance proxy: E[Z^2] - (E[Z])^2. -/
def popVarZ (Z : ℕ → Ω → ℝ) : ℝ :=
  popM2Z (μ := μ) Z - (popMeanZ (μ := μ) Z) ^ 2

/-- Population SD proxy: √(popVar). -/
def popSDZ (Z : ℕ → Ω → ℝ) : ℝ :=
  Real.sqrt (popVarZ (μ := μ) Z)

/-- IID + moment assumptions for applying the strong law to Z and Z^2. -/
structure IIDAssumptions (Z : ℕ → Ω → ℝ) : Prop where
  intZ  : Integrable (Z 0) μ
  indep : Pairwise (fun i j => IndepFun (Z i) (Z j) μ)
  ident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ
  intZ2 : Integrable (fun ω => (Z 0 ω) ^ 2) μ

/-- Measurable squaring map on ℝ. -/
lemma measurable_sq : Measurable (fun x : ℝ => x ^ 2) := by
  simpa [pow_two] using (measurable_id.mul measurable_id)

/-- SLLN for the empirical mean. -/
lemma meanHatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [IsProbabilityMeasure μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => meanHatZ (Z := Z) n ω) atTop
        (nhds (popMeanZ (μ := μ) Z)) := by
  simpa [meanHatZ, popMeanZ] using
    (ProbabilityTheory.strong_law_ae (μ := μ) (X := Z) h.intZ h.indep h.ident)

/-- SLLN for the empirical second moment. -/
lemma m2HatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [IsProbabilityMeasure μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => m2HatZ (Z := Z) n ω) atTop
        (nhds (popM2Z (μ := μ) Z)) := by
  let Zsq : ℕ → Ω → ℝ := fun i ω => (Z i ω) ^ 2
  have hInt : Integrable (Zsq 0) μ := by
    simpa [Zsq] using h.intZ2
  have hInd : Pairwise (fun i j => IndepFun (Zsq i) (Zsq j) μ) := by
    intro i j hij
    have hij0 : IndepFun (Z i) (Z j) μ := h.indep hij
    have : IndepFun ((fun x : ℝ => x ^ 2) ∘ (Z i)) ((fun x : ℝ => x ^ 2) ∘ (Z j)) μ :=
      hij0.comp measurable_sq measurable_sq
    simpa [Zsq, Function.comp] using this
  have hId : ∀ i, IdentDistrib (Zsq i) (Zsq 0) μ μ := by
    intro i
    have hi : IdentDistrib (Z i) (Z 0) μ μ := h.ident i
    have : IdentDistrib ((fun x : ℝ => x ^ 2) ∘ (Z i)) ((fun x : ℝ => x ^ 2) ∘ (Z 0)) μ μ :=
      hi.comp measurable_sq
    simpa [Zsq, Function.comp] using this
  have hslln :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            ((n : ℝ)⁻¹) • (Finset.sum (Finset.range n) fun i => Zsq i ω))
          atTop
          (nhds (∫ ω, Zsq 0 ω ∂μ)) :=
    ProbabilityTheory.strong_law_ae (μ := μ) (X := Zsq) hInt hInd hId
  simpa [m2HatZ, popM2Z, Zsq] using hslln

/-- Convergence of varHat by combining mean and second-moment limits. -/
lemma varHatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [IsProbabilityMeasure μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => varHatZ (Z := Z) n ω) atTop
        (nhds (popVarZ (μ := μ) Z)) := by
  have hmean := meanHatZ_tendsto_ae (μ := μ) (Z := Z) h
  have hm2   := m2HatZ_tendsto_ae (μ := μ) (Z := Z) h
  refine (hmean.and hm2).mono ?_
  intro ω hω
  rcases hω with ⟨hmeanω, hm2ω⟩
  have hmean2 :
      Tendsto (fun n : ℕ => (meanHatZ (Z := Z) n ω) ^ 2) atTop
        (nhds ((popMeanZ (μ := μ) Z) ^ 2)) := by
    simpa [pow_two] using (hmeanω.mul hmeanω)
  have :
      Tendsto
        (fun n : ℕ =>
          m2HatZ (Z := Z) n ω - (meanHatZ (Z := Z) n ω) ^ 2)
        atTop
        (nhds (popM2Z (μ := μ) Z - (popMeanZ (μ := μ) Z) ^ 2)) :=
    hm2ω.sub hmean2
  simpa [varHatZ, popVarZ] using this

/-- Main theorem: sdHat → popSD almost surely. -/
theorem sdHatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [IsProbabilityMeasure μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => sdHatZ (Z := Z) n ω) atTop
        (nhds (popSDZ (μ := μ) Z)) := by
  have hvar := varHatZ_tendsto_ae (μ := μ) (Z := Z) h
  refine hvar.mono ?_
  intro ω hω
  have hsqrt :
      Tendsto Real.sqrt (nhds (popVarZ (μ := μ) Z))
        (nhds (Real.sqrt (popVarZ (μ := μ) Z))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  simpa [sdHatZ, popSDZ] using (hsqrt.comp hω)

end ConjointSD
