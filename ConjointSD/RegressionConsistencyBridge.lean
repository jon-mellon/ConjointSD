/-
ConjointSD/RegressionConsistencyBridge.lean

Route 2 bridge: derive attribute-distribution moment convergence from
(i) parameter convergence `θhat → θ0` and (ii) continuity of the induced
functionals at `θ0`.
-/

import ConjointSD.EstimatedG
import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.Assumptions
import Mathlib.Topology.Basic

open Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/- Definitions live in ConjointSD.Defs / ConjointSD.Assumptions. -/

/-- Mean convergence under θhat → θ0 and continuity of the mean functional. -/
theorem attrMean_tendsto_of_theta_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (xiAttr := xiAttr) g θ0) :
    Tendsto
      (fun n => attrMean xiAttr (gHat g θhat n))
      atTop
      (nhds (attrMean xiAttr (g θ0))) := by
  simpa [gHat, attrMeanΘ] using (hcont.cont_mean.tendsto.comp hθ)

/- Second-moment convergence under θhat → θ0 and continuity of the m2 functional. -/
theorem attrM2_tendsto_of_theta_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (xiAttr := xiAttr) g θ0) :
    Tendsto
      (fun n => attrM2 xiAttr (gHat g θhat n))
      atTop
      (nhds (attrM2 xiAttr (g θ0))) := by
  simpa [gHat, attrM2Θ] using (hcont.cont_m2.tendsto.comp hθ)

/-!
## Deriving functional continuity for linear models
-/

section LinearContinuity

variable {Attr Term : Type*} [MeasurableSpace Attr] [Fintype Term]

lemma functionalContinuity_of_eq
    {Θ : Type*} [TopologicalSpace Θ]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    {g g' : Θ → Attr → ℝ} {θ0 : Θ}
    (hEq : ∀ θ a, g θ a = g' θ a)
    (h : FunctionalContinuityAssumptions (xiAttr := xiAttr) g θ0) :
    FunctionalContinuityAssumptions (xiAttr := xiAttr) g' θ0 := by
  refine ⟨?_, ?_⟩
  · have hmean :
        attrMeanΘ (xiAttr := xiAttr) g' = attrMeanΘ (xiAttr := xiAttr) g := by
          funext θ
          have hEqθ : g' θ = g θ := by
            funext a
            symm
            exact hEq θ a
          simp [attrMeanΘ, hEqθ]
    simpa [hmean] using h.cont_mean
  · have hm2 :
        attrM2Θ (xiAttr := xiAttr) g' = attrM2Θ (xiAttr := xiAttr) g := by
          funext θ
          have hEqθ : g' θ = g θ := by
            funext a
            symm
            exact hEq θ a
          simp [attrM2Θ, hEqθ]
    simpa [hm2] using h.cont_m2

omit [MeasurableSpace Attr] in
lemma bounded_mul_of_bounded
    {f g : Attr → ℝ}
    (hf : ∃ C, 0 ≤ C ∧ ∀ a, |f a| ≤ C)
    (hg : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ a, |f a * g a| ≤ C := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf
  obtain ⟨Cg, hCg0, hCg⟩ := hg
  refine ⟨Cf * Cg, mul_nonneg hCf0 hCg0, ?_⟩
  intro a
  have hmul :
      |f a| * |g a| ≤ Cf * Cg :=
    mul_le_mul (hCf a) (hCg a) (abs_nonneg _) hCf0
  simpa [abs_mul] using hmul

lemma attrMean_gLin_eq_sum
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (φ : Term → Attr → ℝ)
    (hMeas : ∀ t, Measurable (φ t))
    (hBound : ∀ t, ∃ C, 0 ≤ C ∧ ∀ a, |φ t a| ≤ C)
    (θ : Term → ℝ) :
    attrMean xiAttr (gLin (β := θ) (φ := φ))
      =
    ∑ t, θ t * attrMean xiAttr (φ t) := by
  classical
  have hInt : ∀ t, Integrable (fun a => θ t * φ t a) xiAttr := by
    intro t
    have hmeas :
        Measurable (fun a => θ t * φ t a) :=
      measurable_const.mul (hMeas t)
    obtain ⟨C, hC0, hC⟩ := hBound t
    have hbound :
        ∃ C', 0 ≤ C' ∧ ∀ a, |θ t * φ t a| ≤ C' := by
      refine ⟨|θ t| * C, mul_nonneg (abs_nonneg _) hC0, ?_⟩
      intro a
      have hmul : |θ t| * |φ t a| ≤ |θ t| * C :=
        mul_le_mul_of_nonneg_left (hC a) (abs_nonneg _)
      simpa [abs_mul] using hmul
    exact integrable_of_bounded (μexp := xiAttr) hmeas hbound
  have hInt' :
      ∀ t ∈ (Finset.univ : Finset Term),
        Integrable (fun a => θ t * φ t a) xiAttr := by
    intro t ht
    exact hInt t
  calc
    attrMean xiAttr (gLin (β := θ) (φ := φ))
        = ∫ a, ∑ t, θ t * φ t a ∂xiAttr := by
            simp [attrMean, gLin]
    _ = ∑ t, ∫ a, θ t * φ t a ∂xiAttr := by
          simpa using
            (integral_finset_sum
              (μ := xiAttr)
              (s := (Finset.univ : Finset Term))
              (f := fun t a => θ t * φ t a)
              hInt')
    _ = ∑ t, θ t * attrMean xiAttr (φ t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          have hInt :
              ∫ a, θ t * φ t a ∂xiAttr = θ t * ∫ a, φ t a ∂xiAttr := by
            simpa using
              (integral_const_mul (μ := xiAttr) (r := θ t) (f := φ t))
          simpa [attrMean] using hInt

lemma attrM2_gLin_eq_sum
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (φ : Term → Attr → ℝ)
    (hMeas : ∀ t, Measurable (φ t))
    (hBound : ∀ t, ∃ C, 0 ≤ C ∧ ∀ a, |φ t a| ≤ C)
    (θ : Term → ℝ) :
    attrM2 xiAttr (gLin (β := θ) (φ := φ))
      =
    ∑ i, ∑ j, θ i * θ j * attrMean xiAttr (fun a => φ i a * φ j a) := by
  classical
  have hInt : ∀ i j,
      Integrable (fun a => (θ i * φ i a) * (θ j * φ j a)) xiAttr := by
    intro i j
    have hmeas :
        Measurable (fun a => (θ i * φ i a) * (θ j * φ j a)) :=
      (measurable_const.mul (hMeas i)).mul (measurable_const.mul (hMeas j))
    obtain ⟨Ci, hCi0, hCi⟩ := hBound i
    obtain ⟨Cj, hCj0, hCj⟩ := hBound j
    have hbound_i :
        ∃ C, 0 ≤ C ∧ ∀ a, |θ i * φ i a| ≤ C := by
      refine ⟨|θ i| * Ci, mul_nonneg (abs_nonneg _) hCi0, ?_⟩
      intro a
      have hmul : |θ i| * |φ i a| ≤ |θ i| * Ci :=
        mul_le_mul_of_nonneg_left (hCi a) (abs_nonneg _)
      simpa [abs_mul] using hmul
    have hbound_j :
        ∃ C, 0 ≤ C ∧ ∀ a, |θ j * φ j a| ≤ C := by
      refine ⟨|θ j| * Cj, mul_nonneg (abs_nonneg _) hCj0, ?_⟩
      intro a
      have hmul : |θ j| * |φ j a| ≤ |θ j| * Cj :=
        mul_le_mul_of_nonneg_left (hCj a) (abs_nonneg _)
      simpa [abs_mul] using hmul
    have hbound :=
      bounded_mul_of_bounded (f := fun a => θ i * φ i a) (g := fun a => θ j * φ j a)
        hbound_i hbound_j
    exact integrable_of_bounded (μexp := xiAttr) hmeas hbound
  have hIntJ : ∀ i,
      Integrable (fun a => ∑ j, (θ i * φ i a) * (θ j * φ j a)) xiAttr := by
    intro i
    refine integrable_finset_sum (s := (Finset.univ : Finset Term)) ?_
    intro j hj
    exact hInt i j
  have hIntJ' :
      ∀ i ∈ (Finset.univ : Finset Term),
        Integrable (fun a => ∑ j, (θ i * φ i a) * (θ j * φ j a)) xiAttr := by
    intro i hi
    exact hIntJ i
  have hInt' :
      ∀ i ∈ (Finset.univ : Finset Term),
        ∀ j ∈ (Finset.univ : Finset Term),
          Integrable (fun a => (θ i * φ i a) * (θ j * φ j a)) xiAttr := by
    intro i hi j hj
    exact hInt i j
  calc
    attrM2 xiAttr (gLin (β := θ) (φ := φ))
        = ∫ a, (∑ i, θ i * φ i a) * (∑ j, θ j * φ j a) ∂xiAttr := by
            simp [attrM2, gLin, pow_two]
    _ = ∫ a, ∑ i, ∑ j, (θ i * φ i a) * (θ j * φ j a) ∂xiAttr := by
          simp [Fintype.sum_mul_sum]
    _ = ∑ i, ∫ a, ∑ j, (θ i * φ i a) * (θ j * φ j a) ∂xiAttr := by
          simpa using
            (integral_finset_sum
              (μ := xiAttr)
              (s := (Finset.univ : Finset Term))
              (f := fun i a => ∑ j, (θ i * φ i a) * (θ j * φ j a))
              hIntJ')
    _ = ∑ i, ∑ j, ∫ a, (θ i * φ i a) * (θ j * φ j a) ∂xiAttr := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using
            (integral_finset_sum
              (μ := xiAttr)
              (s := (Finset.univ : Finset Term))
              (f := fun j a => (θ i * φ i a) * (θ j * φ j a))
              (hInt' i hi))
    _ = ∑ i, ∑ j, θ i * θ j * attrMean xiAttr (fun a => φ i a * φ j a) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hmul :
              (fun a => (θ i * φ i a) * (θ j * φ j a))
                =
              (fun a => (θ i * θ j) * (φ i a * φ j a)) := by
            funext a
            ring
          have hInt :
              ∫ a, (θ i * θ j) * (φ i a * φ j a) ∂xiAttr
                =
              (θ i * θ j) * ∫ a, φ i a * φ j a ∂xiAttr := by
            simpa using
              (integral_const_mul (μ := xiAttr) (r := θ i * θ j)
                (f := fun a => φ i a * φ j a))
          have hInt' :
              ∫ a, (θ i * φ i a) * (θ j * φ j a) ∂xiAttr
                =
              (θ i * θ j) * ∫ a, φ i a * φ j a ∂xiAttr := by
            simpa [hmul] using hInt
          simpa [attrMean] using hInt'

lemma functionalContinuity_gLin_of_bounded
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (φ : Term → Attr → ℝ)
    (hMeas : ∀ t, Measurable (φ t))
    (hBound : ∀ t, ∃ C, 0 ≤ C ∧ ∀ a, |φ t a| ≤ C)
    (θ0 : Term → ℝ) :
    FunctionalContinuityAssumptions (xiAttr := xiAttr)
      (g := fun θ => gLin (β := θ) (φ := φ)) θ0 := by
  classical
  have hMeanCont :
      Continuous (fun θ : Term → ℝ => ∑ t, θ t * attrMean xiAttr (φ t)) := by
    refine continuous_finset_sum _ ?_
    intro t ht
    exact (continuous_apply t).mul continuous_const
  have hM2Cont :
      Continuous (fun θ : Term → ℝ =>
        ∑ i, ∑ j, θ i * θ j * attrMean xiAttr (fun a => φ i a * φ j a)) := by
    refine continuous_finset_sum _ ?_
    intro i hi
    refine continuous_finset_sum _ ?_
    intro j hj
    have hθ : Continuous (fun θ : Term → ℝ => θ i * θ j) :=
      (continuous_apply i).mul (continuous_apply j)
    exact hθ.mul continuous_const
  refine ⟨?_, ?_⟩
  · have hMeanContAt :
        ContinuousAt (fun θ : Term → ℝ => ∑ t, θ t * attrMean xiAttr (φ t)) θ0 :=
      hMeanCont.continuousAt
    have hMeanEq :
        (fun θ : Term → ℝ => attrMean xiAttr (gLin (β := θ) (φ := φ)))
          =
        (fun θ : Term → ℝ => ∑ t, θ t * attrMean xiAttr (φ t)) := by
      funext θ
      simpa using
        (attrMean_gLin_eq_sum (xiAttr := xiAttr) (φ := φ) hMeas hBound θ)
    have hMeanContAt' :
        ContinuousAt (fun θ : Term → ℝ => attrMean xiAttr (gLin (β := θ) (φ := φ))) θ0 := by
      simpa [hMeanEq] using hMeanContAt
    simpa [attrMeanΘ] using hMeanContAt'
  · have hM2ContAt :
        ContinuousAt
          (fun θ : Term → ℝ =>
            ∑ i, ∑ j, θ i * θ j * attrMean xiAttr (fun a => φ i a * φ j a)) θ0 :=
      hM2Cont.continuousAt
    have hM2Eq :
        (fun θ : Term → ℝ => attrM2 xiAttr (gLin (β := θ) (φ := φ)))
          =
        (fun θ : Term → ℝ =>
          ∑ i, ∑ j, θ i * θ j * attrMean xiAttr (fun a => φ i a * φ j a)) := by
      funext θ
      simpa using
        (attrM2_gLin_eq_sum (xiAttr := xiAttr) (φ := φ) hMeas hBound θ)
    have hM2ContAt' :
        ContinuousAt (fun θ : Term → ℝ => attrM2 xiAttr (gLin (β := θ) (φ := φ))) θ0 := by
      simpa [hM2Eq] using hM2ContAt
    simpa [attrM2Θ] using hM2ContAt'

end LinearContinuity

end ConjointSD
