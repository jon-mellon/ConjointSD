import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

/-- Measurable squaring map on ℝ. -/
lemma measurable_sq : Measurable (fun x : ℝ => x ^ 2) := by
  simpa [pow_two] using (measurable_id.mul measurable_id)

/-- SLLN for the empirical mean. -/
lemma meanHatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [ProbMeasureAssumptions μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => meanHatZ (Z := Z) n ω) atTop
        (nhds (designMeanZ (μ := μ) Z)) := by
  simpa [meanHatZ, designMeanZ] using
    (ProbabilityTheory.strong_law_ae (μ := μ) (X := Z) h.intZ h.indep h.ident)

/-- SLLN for the empirical second moment. -/
lemma m2HatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [ProbMeasureAssumptions μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => m2HatZ (Z := Z) n ω) atTop
        (nhds (designM2Z (μ := μ) Z)) := by
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
  simpa [m2HatZ, designM2Z, Zsq] using hslln

/-- SLLN for empirical RMSE: √(m2Hat) → √(designM2). -/
lemma rmseHatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [ProbMeasureAssumptions μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => rmseHatZ (Z := Z) n ω) atTop
        (nhds (designRMSEZ (μ := μ) Z)) := by
  have hm2 := m2HatZ_tendsto_ae (μ := μ) (Z := Z) h
  refine hm2.mono ?_
  intro ω hm2ω
  have hsqrt :
      Tendsto Real.sqrt (nhds (designM2Z (μ := μ) Z))
        (nhds (Real.sqrt (designM2Z (μ := μ) Z))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  simpa [rmseHatZ, designRMSEZ] using (hsqrt.comp hm2ω)

/-- Convergence of varHat by combining mean and second-moment limits. -/
lemma varHatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [ProbMeasureAssumptions μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => varHatZ (Z := Z) n ω) atTop
        (nhds (designVarZ (μ := μ) Z)) := by
  have hmean := meanHatZ_tendsto_ae (μ := μ) (Z := Z) h
  have hm2   := m2HatZ_tendsto_ae (μ := μ) (Z := Z) h
  refine (hmean.and hm2).mono ?_
  intro ω hω
  rcases hω with ⟨hmeanω, hm2ω⟩
  have hmean2 :
      Tendsto (fun n : ℕ => (meanHatZ (Z := Z) n ω) ^ 2) atTop
        (nhds ((designMeanZ (μ := μ) Z) ^ 2)) := by
    simpa [pow_two] using (hmeanω.mul hmeanω)
  have :
      Tendsto
        (fun n : ℕ =>
          m2HatZ (Z := Z) n ω - (meanHatZ (Z := Z) n ω) ^ 2)
        atTop
        (nhds (designM2Z (μ := μ) Z - (designMeanZ (μ := μ) Z) ^ 2)) :=
    hm2ω.sub hmean2
  simpa [varHatZ, designVarZ] using this

/-- Main theorem: sdHat → designSD almost surely. -/
theorem sdHatZ_tendsto_ae (Z : ℕ → Ω → ℝ) [ProbMeasureAssumptions μ]
    (h : IIDAssumptions (μ := μ) Z) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => sdHatZ (Z := Z) n ω) atTop
        (nhds (designSDZ (μ := μ) Z)) := by
  have hvar := varHatZ_tendsto_ae (μ := μ) (Z := Z) h
  refine hvar.mono ?_
  intro ω hω
  have hsqrt :
      Tendsto Real.sqrt (nhds (designVarZ (μ := μ) Z))
        (nhds (Real.sqrt (designVarZ (μ := μ) Z))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  simpa [sdHatZ, designSDZ] using (hsqrt.comp hω)

end ConjointSD
