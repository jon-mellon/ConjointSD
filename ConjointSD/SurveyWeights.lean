import ConjointSD.Assumptions

open Filter MeasureTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

/-!
# Survey weights and finite-population targets

This file adds weighted attribute-distribution estimands (means/moments/SD) for the
target human population and basic finite-population targets. These can be plugged into
the existing consistency/identification lemmas by substituting the target functional.
-/

variable {Attr : Type*} [MeasurableSpace Attr]

/-!
## Weighted attribute-distribution estimands

Given an attribute distribution `ν` for the target human population and a
nonnegative weight function `w`,
define weighted mean/moments as normalized weighted integrals.
-/

/-- Weighted attribute-distribution mean under `ν` with weights `w`. -/
def weightMeanAttr (ν : Measure Attr) (w s : Attr → ℝ) : ℝ :=
  (∫ a, w a * s a ∂ν) / (∫ a, w a ∂ν)

/-- Weighted attribute-distribution second moment under `ν` with weights `w`. -/
def weightM2Attr (ν : Measure Attr) (w s : Attr → ℝ) : ℝ :=
  (∫ a, w a * (s a) ^ 2 ∂ν) / (∫ a, w a ∂ν)

/-- Weighted attribute-distribution variance under `ν` with weights `w`. -/
def weightVarAttr (ν : Measure Attr) (w s : Attr → ℝ) : ℝ :=
  weightM2Attr (ν := ν) w s - (weightMeanAttr (ν := ν) w s) ^ 2

/-- Weighted attribute-distribution SD under `ν` with weights `w`. -/
def weightSDAttr (ν : Measure Attr) (w s : Attr → ℝ) : ℝ :=
  Real.sqrt (weightVarAttr (ν := ν) w s)

lemma weightMeanAttr_one
    (ν : Measure Attr) [ProbMeasureAssumptions ν] (s : Attr → ℝ) :
    weightMeanAttr (ν := ν) (w := fun _ => (1 : ℝ)) s = attrMean ν s := by
  simp [weightMeanAttr, attrMean]

lemma weightM2Attr_one
    (ν : Measure Attr) [ProbMeasureAssumptions ν] (s : Attr → ℝ) :
    weightM2Attr (ν := ν) (w := fun _ => (1 : ℝ)) s = attrM2 ν s := by
  simp [weightM2Attr, attrM2]

lemma weightVarAttr_one
    (ν : Measure Attr) [ProbMeasureAssumptions ν] (s : Attr → ℝ) :
    weightVarAttr (ν := ν) (w := fun _ => (1 : ℝ)) s = attrVar ν s := by
  simp [weightVarAttr, attrVar, weightMeanAttr_one, weightM2Attr_one]

lemma weightSDAttr_one
    (ν : Measure Attr) [ProbMeasureAssumptions ν] (s : Attr → ℝ) :
    weightSDAttr (ν := ν) (w := fun _ => (1 : ℝ)) s = attrSD ν s := by
  simp [weightSDAttr, attrSD, weightVarAttr_one]

lemma weightVarAttr_eq_attrVar_of_moments
    (ν : Measure Attr) (w s : Attr → ℝ)
    (h : WeightMatchesAttrMoments (ν := ν) (w := w) (s := s)) :
    weightVarAttr (ν := ν) w s = attrVar ν s := by
  have hmean : weightMeanAttr (ν := ν) (w := w) s = attrMean ν s := by
    simpa [weightMeanAttr] using h.mean_eq
  have hm2 : weightM2Attr (ν := ν) (w := w) s = attrM2 ν s := by
    simpa [weightM2Attr] using h.m2_eq
  simp [weightVarAttr, attrVar, hmean, hm2]

lemma weightSDAttr_eq_attrSD_of_moments
    (ν : Measure Attr) (w s : Attr → ℝ)
    (h : WeightMatchesAttrMoments (ν := ν) (w := w) (s := s)) :
    weightSDAttr (ν := ν) w s = attrSD ν s := by
  simp [weightSDAttr, attrSD, weightVarAttr_eq_attrVar_of_moments (ν := ν) (w := w) (s := s) h]

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
