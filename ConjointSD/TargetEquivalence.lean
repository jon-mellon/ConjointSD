/-
ConjointSD/TargetEquivalence.lean

If two score functions are equal ν_pop-a.e., then their attribute-distribution mean/second-moment/variance/SD
under ν_pop are equal. This is the basic tool to turn “consistency to g θ0” into “consistency to
the true estimand”, once you add a WellSpecified / transport bridge assumption.
-/

import Mathlib
import ConjointSD.Transport

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

section

variable {Attr : Type*} [MeasurableSpace Attr]
variable (ν_pop : Measure Attr)
variable {s t : Attr → ℝ}

/-- If s = t ν_pop-a.e., then their attribute-distribution means are equal. -/
theorem attrMean_congr_ae (h : ∀ᵐ a ∂ν_pop, s a = t a) :
    attrMean ν_pop s = attrMean ν_pop t := by
  have : (∫ a, s a ∂ν_pop) = (∫ a, t a ∂ν_pop) := by
    exact integral_congr_ae h
  simpa [attrMean] using this

/-- If s = t ν_pop-a.e., then their attribute-distribution second moments are equal. -/
theorem attrM2_congr_ae (h : ∀ᵐ a ∂ν_pop, s a = t a) :
    attrM2 ν_pop s = attrM2 ν_pop t := by
  have h2 : ∀ᵐ a ∂ν_pop, (s a) ^ 2 = (t a) ^ 2 := by
    refine h.mono ?_
    intro a ha
    simp [ha]
  have : (∫ a, (s a) ^ 2 ∂ν_pop) = (∫ a, (t a) ^ 2 ∂ν_pop) := by
    exact integral_congr_ae h2
  simpa [attrM2] using this

/-- If s = t ν_pop-a.e., then their attribute-distribution variances are equal. -/
theorem attrVar_congr_ae (h : ∀ᵐ a ∂ν_pop, s a = t a) :
    attrVar ν_pop s = attrVar ν_pop t := by
  have hm : attrMean ν_pop s = attrMean ν_pop t :=
    attrMean_congr_ae (ν_pop := ν_pop) (s := s) (t := t) h
  have hm2 : attrM2 ν_pop s = attrM2 ν_pop t :=
    attrM2_congr_ae (ν_pop := ν_pop) (s := s) (t := t) h
  simp [attrVar, hm, hm2]

/-- If s = t ν_pop-a.e., then their attribute-distribution SDs are equal. -/
theorem attrSD_congr_ae (h : ∀ᵐ a ∂ν_pop, s a = t a) :
    attrSD ν_pop s = attrSD ν_pop t := by
  have hv : attrVar ν_pop s = attrVar ν_pop t :=
    attrVar_congr_ae (ν_pop := ν_pop) (s := s) (t := t) h
  simp [attrSD, hv]

end

end ConjointSD
