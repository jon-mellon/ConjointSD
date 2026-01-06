import ConjointSD.PredictedSD
import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]

/-!
Simplification: bounded scores give the integrability assumptions automatically.
-/

/-- Bounded measurable real functions are integrable under a finite measure. -/
lemma integrable_of_bounded
    (μexp : Measure Ω) [IsFiniteMeasure μexp] {f : Ω → ℝ}
    (hmeas : Measurable f) (hbound : ∃ C, 0 ≤ C ∧ ∀ ω, |f ω| ≤ C) :
    Integrable f μexp := by
  obtain ⟨C, hC0, hC⟩ := hbound
  refine Integrable.of_bound (hf := hmeas.aestronglyMeasurable) C ?_
  refine ae_of_all μexp ?_
  intro ω
  have hC' := hC ω
  simpa [Real.norm_eq_abs] using hC'

lemma meanHatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (hIID : DesignAttrIID (κ := μexp) A)
    (hMeas : Measurable g)
    (hBound : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => meanHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := g)))) := by
  let Z : ℕ → Ω → ℝ := Zcomp (A := A) (g := g)
  have hInd : Pairwise (fun i j => IndepFun (Z i) (Z j) μexp) := by
    intro i j hij
    have hijA : IndepFun (A i) (A j) μexp := hIID.indepA hij
    have : IndepFun (g ∘ (A i)) (g ∘ (A j)) μexp :=
      hijA.comp hMeas hMeas
    simpa [Z, Zcomp, Function.comp] using this
  have hId : ∀ i, IdentDistrib (Z i) (Z 0) μexp μexp := by
    intro i
    have hiA : IdentDistrib (A i) (A 0) μexp μexp := hIID.identA i
    have : IdentDistrib (g ∘ (A i)) (g ∘ (A 0)) μexp μexp :=
      hiA.comp hMeas
    simpa [Z, Zcomp, Function.comp] using this
  have hInt : Integrable (Z 0) μexp := by
    obtain ⟨C, hC0, hC⟩ := hBound
    have hmeasA0 : Measurable (A 0) := hIID.measA 0
    have hmeas_gA0 : Measurable (fun ω => g (A 0 ω)) := hMeas.comp hmeasA0
    have hbound_gA0 : ∃ C, 0 ≤ C ∧ ∀ ω, |g (A 0 ω)| ≤ C := by
      refine ⟨C, hC0, ?_⟩
      intro ω
      exact hC (A 0 ω)
    have hInt' : Integrable (fun ω => g (A 0 ω)) μexp :=
      integrable_of_bounded (μexp := μexp) hmeas_gA0 hbound_gA0
    simpa [Z, Zcomp] using hInt'
  simpa [meanHatZ, designMeanZ, Z] using
    (ProbabilityTheory.strong_law_ae (μ := μexp) (X := Z) hInt hInd hId)

lemma m2HatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (hIID : DesignAttrIID (κ := μexp) A)
    (hMeasG : Measurable g)
    (hBoundG : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => m2HatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designM2Z (κ := μexp) (Z := Zcomp (A := A) (g := g)))) := by
  obtain ⟨C, hC0, hC⟩ := hBoundG
  have hMeasSq : Measurable (fun a => (g a) ^ 2) := by
    simpa [pow_two] using (hMeasG.mul hMeasG)
  have hBoundSq : ∃ C', 0 ≤ C' ∧ ∀ a, |(g a) ^ 2| ≤ C' := by
    refine ⟨C ^ 2, by nlinarith, ?_⟩
    intro a
    have hmul : |g a| * |g a| ≤ C * C :=
      mul_le_mul (hC a) (hC a) (abs_nonneg _) hC0
    simpa [pow_two, abs_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hmeanSq :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n : ℕ =>
            meanHatZ (Z := Zcomp (A := A) (g := fun a => (g a) ^ 2)) n ω)
          atTop
          (nhds
            (designMeanZ (κ := μexp)
              (Z := Zcomp (A := A) (g := fun a => (g a) ^ 2)))) := by
    simpa [Zcomp] using
      meanHatZ_tendsto_ae_of_score
        (μexp := μexp) (A := A) (g := fun a => (g a) ^ 2)
        hIID hMeasSq hBoundSq
  refine hmeanSq.mono ?_
  intro ω hω
  simpa [m2HatZ, designM2Z, Zcomp] using hω

lemma varHatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (hIID : DesignAttrIID (κ := μexp) A)
    (hMeasG : Measurable g)
    (hBoundG : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => varHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designVarZ (κ := μexp) (Z := Zcomp (A := A) (g := g)))) := by
  have hmean :=
    meanHatZ_tendsto_ae_of_score
      (μexp := μexp) (A := A) (g := g) hIID hMeasG hBoundG
  have hm2 :=
    m2HatZ_tendsto_ae_of_score
      (μexp := μexp) (A := A) (g := g) hIID hMeasG hBoundG
  refine (hmean.and hm2).mono ?_
  intro ω hω
  rcases hω with ⟨hmeanω, hm2ω⟩
  have hmean2 :
      Tendsto
        (fun n : ℕ =>
          (meanHatZ (Z := Zcomp (A := A) (g := g)) n ω) ^ 2)
        atTop
        (nhds
          ((designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := g))) ^ 2)) := by
    simpa [pow_two] using (hmeanω.mul hmeanω)
  have :
      Tendsto
        (fun n : ℕ =>
          m2HatZ (Z := Zcomp (A := A) (g := g)) n ω
            - (meanHatZ (Z := Zcomp (A := A) (g := g)) n ω) ^ 2)
        atTop
        (nhds
          (designM2Z (κ := μexp) (Z := Zcomp (A := A) (g := g))
            - (designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := g))) ^ 2)) :=
    hm2ω.sub hmean2
  simpa [varHatZ, designVarZ] using this

theorem sdHatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (hIID : DesignAttrIID (κ := μexp) A)
    (hMeasG : Measurable g)
    (hBoundG : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ =>
          sdHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds
          (designSDZ (κ := μexp) (Z := Zcomp (A := A) (g := g)))) := by
  have hvar :=
    varHatZ_tendsto_ae_of_score
      (μexp := μexp) (A := A) (g := g) hIID hMeasG hBoundG
  refine hvar.mono ?_
  intro ω hω
  have hsqrt :
      Tendsto Real.sqrt
        (nhds (designVarZ (κ := μexp) (Z := Zcomp (A := A) (g := g))))
        (nhds (Real.sqrt
          (designVarZ (κ := μexp) (Z := Zcomp (A := A) (g := g))))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  simpa [sdHatZ, designSDZ] using (hsqrt.comp hω)

end ConjointSD
