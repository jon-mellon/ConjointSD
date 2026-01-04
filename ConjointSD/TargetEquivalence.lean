/-
ConjointSD/TargetEquivalence.lean

If two score functions are equal ν-a.e., then their attribute-distribution mean/second-moment/variance/SD
under ν are equal. This is the basic tool to turn “consistency to g θ0” into “consistency to
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
variable (ν : Measure Attr)
variable {s t : Attr → ℝ}

/-- If s = t ν-a.e., then their attribute-distribution means are equal. -/
theorem attrMean_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    attrMean ν s = attrMean ν t := by
  have : (∫ a, s a ∂ν) = (∫ a, t a ∂ν) := by
    exact integral_congr_ae h
  simpa [attrMean] using this

/-- If s = t ν-a.e., then their attribute-distribution second moments are equal. -/
theorem attrM2_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    attrM2 ν s = attrM2 ν t := by
  have h2 : ∀ᵐ a ∂ν, (s a) ^ 2 = (t a) ^ 2 := by
    refine h.mono ?_
    intro a ha
    simp [ha]
  have : (∫ a, (s a) ^ 2 ∂ν) = (∫ a, (t a) ^ 2 ∂ν) := by
    exact integral_congr_ae h2
  simpa [attrM2] using this

/-- If s = t ν-a.e., then their attribute-distribution variances are equal. -/
theorem attrVar_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    attrVar ν s = attrVar ν t := by
  have hm : attrMean ν s = attrMean ν t :=
    attrMean_congr_ae (ν := ν) (s := s) (t := t) h
  have hm2 : attrM2 ν s = attrM2 ν t :=
    attrM2_congr_ae (ν := ν) (s := s) (t := t) h
  simp [attrVar, hm, hm2]

/-- If s = t ν-a.e., then their attribute-distribution SDs are equal. -/
theorem attrSD_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    attrSD ν s = attrSD ν t := by
  have hv : attrVar ν s = attrVar ν t :=
    attrVar_congr_ae (ν := ν) (s := s) (t := t) h
  simp [attrSD, hv]

end

end ConjointSD
