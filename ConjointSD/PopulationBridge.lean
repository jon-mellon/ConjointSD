/-
ConjointSD/PopulationBridge.lean

Bridge between:
- population functionals under an attribute distribution `ν : Measure Attr`
  (popMeanAttr/popM2Attr/popVarAttr/popSDAttr), and
- functionals on the population probability space `μ : Measure Ω` for the induced
  score process `Zcomp (A := A) (g := g)` (popMeanZ/popM2Z/popVarZ/popSDZ).

Assumption: `A 0` has law `ν` under `μ`, i.e. `Measure.map (A 0) μ = ν`.

Implementation note:
In this mathlib version, `MeasureTheory.integral_map` uses the argument name `φ` for the map.
It also expects:
- `AEMeasurable φ μ`, and
- `AEStronglyMeasurable f (Measure.map φ μ)` for the integrand.

We derive the latter from `Measurable` via `.aemeasurable.aestronglyMeasurable`.
-/

import ConjointSD.Transport
import ConjointSD.SDDecompositionFromConjoint

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]
variable (A : ℕ → Ω → Attr)
variable (ν : Measure Attr)

/--
Bridge for means: if `A 0 ∼ ν`, then the mean of `g(A 0)` under `μ` equals the mean of `g`
under `ν`.
-/
theorem popMeanZ_Zcomp_eq_popMeanAttr
    (g : Attr → ℝ)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hg : Measurable g) :
    popMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    popMeanAttr ν g := by
  have hg_str : AEStronglyMeasurable g (Measure.map (A 0) μ) :=
    hg.aemeasurable.aestronglyMeasurable
  have hmap :
      (∫ a, g a ∂Measure.map (A 0) μ) = (∫ ω, g (A 0 ω) ∂μ) := by
    -- change-of-variables for pushforward measures
    simpa using
      (MeasureTheory.integral_map (μ := μ) (f := g) (φ := A 0)
        hMap.measA0.aemeasurable hg_str)
  calc
    popMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g))
        = (∫ ω, g (A 0 ω) ∂μ) := by
            simp [popMeanZ, Zcomp]
    _   = (∫ a, g a ∂Measure.map (A 0) μ) := by
            simp [hmap]
    _   = (∫ a, g a ∂ν) := by
            simp [hMap.map_eq]
    _   = popMeanAttr ν g := by
            simp [popMeanAttr]

/--
Bridge for second moments: if `A 0 ∼ ν`, then `E[(g(A 0))^2]` under `μ` equals `E[(g)^2]`
under `ν`.
-/
theorem popM2Z_Zcomp_eq_popM2Attr
    (g : Attr → ℝ)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hg : Measurable g) :
    popM2Z (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    popM2Attr ν g := by
  -- square via multiplication (avoids any separate pow measurability concerns)
  let g2 : Attr → ℝ := fun a => g a * g a
  have hg2 : Measurable g2 := by
    simpa [g2] using (hg.mul hg)
  have hg2_str : AEStronglyMeasurable g2 (Measure.map (A 0) μ) :=
    hg2.aemeasurable.aestronglyMeasurable
  have hmap :
      (∫ a, g2 a ∂Measure.map (A 0) μ) = (∫ ω, g2 (A 0 ω) ∂μ) := by
    simpa using
      (MeasureTheory.integral_map (μ := μ) (f := g2) (φ := A 0)
        hMap.measA0.aemeasurable hg2_str)
  calc
    popM2Z (μ := μ) (Z := Zcomp (A := A) (g := g))
        = (∫ ω, (g (A 0 ω)) ^ 2 ∂μ) := by
            simp [popM2Z, Zcomp]
    _   = (∫ ω, g2 (A 0 ω) ∂μ) := by
            simp [g2, pow_two]
    _   = (∫ a, g2 a ∂Measure.map (A 0) μ) := by
            simp [hmap]
    _   = (∫ a, g2 a ∂ν) := by
            simp [hMap.map_eq]
    _   = (∫ a, (g a) ^ 2 ∂ν) := by
            simp [g2, pow_two]
    _   = popM2Attr ν g := by
            simp [popM2Attr]

/-- Bridge for variances (proxy form): follows from the mean and second-moment bridges. -/
theorem popVarZ_Zcomp_eq_popVarAttr
    (g : Attr → ℝ)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hg : Measurable g) :
    popVarZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    popVarAttr ν g := by
  have hmean :
      popMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g)) = popMeanAttr ν g :=
    popMeanZ_Zcomp_eq_popMeanAttr (μ := μ) (A := A) (ν := ν) (g := g) hMap hg
  have hm2 :
      popM2Z (μ := μ) (Z := Zcomp (A := A) (g := g)) = popM2Attr ν g :=
    popM2Z_Zcomp_eq_popM2Attr (μ := μ) (A := A) (ν := ν) (g := g) hMap hg
  simp [popVarZ, popVarAttr, hmean, hm2]

/-- Bridge for SDs: follows from the variance bridge. -/
theorem popSDZ_Zcomp_eq_popSDAttr
    (g : Attr → ℝ)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hg : Measurable g) :
    popSDZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    popSDAttr ν g := by
  have hvar :
      popVarZ (μ := μ) (Z := Zcomp (A := A) (g := g)) = popVarAttr ν g :=
    popVarZ_Zcomp_eq_popVarAttr (μ := μ) (A := A) (ν := ν) (g := g) hMap hg
  simp [popSDZ, popSDAttr, hvar]

end

end ConjointSD
