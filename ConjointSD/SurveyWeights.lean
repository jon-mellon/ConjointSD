import ConjointSD.Assumptions

open Filter MeasureTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

/-!
# Survey weights and finite-population targets

This file adds weighted population estimands (means/moments/SD) and basic finite-population
targets. These can be plugged into the existing consistency/identification lemmas by
substituting the target functional.
-/

variable {Attr : Type*} [MeasurableSpace Attr]

/-!
## Weighted population estimands

Given a base population measure `ν` and a nonnegative weight function `w`,
define weighted mean/moments as normalized weighted integrals.
-/

/-- Weighted population mean under base measure `ν` with weights `w`. -/
def weightMeanAttr (ν : Measure Attr) (w s : Attr → ℝ) : ℝ :=
  (∫ a, w a * s a ∂ν) / (∫ a, w a ∂ν)

/-- Weighted population second moment under base measure `ν` with weights `w`. -/
def weightM2Attr (ν : Measure Attr) (w s : Attr → ℝ) : ℝ :=
  (∫ a, w a * (s a) ^ 2 ∂ν) / (∫ a, w a ∂ν)

/-- Weighted population variance under base measure `ν` with weights `w`. -/
def weightVarAttr (ν : Measure Attr) (w s : Attr → ℝ) : ℝ :=
  weightM2Attr (ν := ν) w s - (weightMeanAttr (ν := ν) w s) ^ 2

/-- Weighted population SD under base measure `ν` with weights `w`. -/
def weightSDAttr (ν : Measure Attr) (w s : Attr → ℝ) : ℝ :=
  Real.sqrt (weightVarAttr (ν := ν) w s)

lemma weightMeanAttr_one
    (ν : Measure Attr) [IsProbabilityMeasure ν] (s : Attr → ℝ) :
    weightMeanAttr (ν := ν) (w := fun _ => (1 : ℝ)) s = popMeanAttr ν s := by
  simp [weightMeanAttr, popMeanAttr]

lemma weightM2Attr_one
    (ν : Measure Attr) [IsProbabilityMeasure ν] (s : Attr → ℝ) :
    weightM2Attr (ν := ν) (w := fun _ => (1 : ℝ)) s = popM2Attr ν s := by
  simp [weightM2Attr, popM2Attr]

lemma weightVarAttr_one
    (ν : Measure Attr) [IsProbabilityMeasure ν] (s : Attr → ℝ) :
    weightVarAttr (ν := ν) (w := fun _ => (1 : ℝ)) s = popVarAttr ν s := by
  simp [weightVarAttr, popVarAttr, weightMeanAttr_one, weightM2Attr_one]

lemma weightSDAttr_one
    (ν : Measure Attr) [IsProbabilityMeasure ν] (s : Attr → ℝ) :
    weightSDAttr (ν := ν) (w := fun _ => (1 : ℝ)) s = popSDAttr ν s := by
  simp [weightSDAttr, popSDAttr, weightVarAttr_one]

/-!
## Finite-population targets

These are deterministic targets for a finite population `S`.
-/

/-- Finite-population mean over a finite set `S`. -/
def finitePopMean (S : Finset Attr) (s : Attr → ℝ) : ℝ :=
  (S.card : ℝ)⁻¹ * Finset.sum S (fun a => s a)

/-- Finite-population second moment over a finite set `S`. -/
def finitePopM2 (S : Finset Attr) (s : Attr → ℝ) : ℝ :=
  (S.card : ℝ)⁻¹ * Finset.sum S (fun a => (s a) ^ 2)

/-- Finite-population variance over a finite set `S`. -/
def finitePopVar (S : Finset Attr) (s : Attr → ℝ) : ℝ :=
  finitePopM2 S s - (finitePopMean S s) ^ 2

/-- Finite-population SD over a finite set `S`. -/
def finitePopSD (S : Finset Attr) (s : Attr → ℝ) : ℝ :=
  Real.sqrt (finitePopVar S s)

end ConjointSD
