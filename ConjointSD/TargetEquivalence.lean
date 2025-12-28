/-
ConjointSD/TargetEquivalence.lean

If two score functions are equal ν-a.e., then their population mean/second-moment/variance/SD
under ν are equal. This is the basic tool to turn “consistency to g θ0” into “consistency to
the true estimand”, once you add a WellSpecified / InvarianceAE assumption.
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

/-- If s = t ν-a.e., then their population means are equal. -/
theorem popMeanAttr_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    popMeanAttr ν s = popMeanAttr ν t := by
  have : (∫ a, s a ∂ν) = (∫ a, t a ∂ν) := by
    exact integral_congr_ae h
  simpa [popMeanAttr] using this

/-- If s = t ν-a.e., then their population second moments are equal. -/
theorem popM2Attr_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    popM2Attr ν s = popM2Attr ν t := by
  have h2 : ∀ᵐ a ∂ν, (s a) ^ 2 = (t a) ^ 2 := by
    refine h.mono ?_
    intro a ha
    simp [ha]
  have : (∫ a, (s a) ^ 2 ∂ν) = (∫ a, (t a) ^ 2 ∂ν) := by
    exact integral_congr_ae h2
  simpa [popM2Attr] using this

/-- If s = t ν-a.e., then their population variances are equal. -/
theorem popVarAttr_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    popVarAttr ν s = popVarAttr ν t := by
  have hm : popMeanAttr ν s = popMeanAttr ν t :=
    popMeanAttr_congr_ae (ν := ν) (s := s) (t := t) h
  have hm2 : popM2Attr ν s = popM2Attr ν t :=
    popM2Attr_congr_ae (ν := ν) (s := s) (t := t) h
  simp [popVarAttr, hm, hm2]

/-- If s = t ν-a.e., then their population SDs are equal. -/
theorem popSDAttr_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    popSDAttr ν s = popSDAttr ν t := by
  have hv : popVarAttr ν s = popVarAttr ν t :=
    popVarAttr_congr_ae (ν := ν) (s := s) (t := t) h
  simp [popSDAttr, hv]

end

end ConjointSD
