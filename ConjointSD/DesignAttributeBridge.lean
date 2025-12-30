/-
ConjointSD/DesignAttributeBridge.lean

Bridge between:
- attribute-distribution functionals under `ν : Measure Attr`
  (attrMean/attrM2/attrVar/attrSD), and
- functionals under the experimental design distribution `μ : Measure Ω` for
  the induced score process `Zcomp (A := A) (g := g)`
  (designMeanZ/designM2Z/designVarZ/designSDZ).

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
Bridge for means: if `A 0 ∼ ν`, then the mean of `g(A 0)` under the experimental
design distribution `μ` equals the mean of `g` under the attribute distribution `ν`.
-/
theorem designMeanZ_Zcomp_eq_attrMean
    (g : Attr → ℝ)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hg : Measurable g) :
    designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    attrMean ν g := by
  have hg_str : AEStronglyMeasurable g (Measure.map (A 0) μ) :=
    hg.aemeasurable.aestronglyMeasurable
  have hmap :
      (∫ a, g a ∂Measure.map (A 0) μ) = (∫ ω, g (A 0 ω) ∂μ) := by
    -- change-of-variables for pushforward measures
    simpa using
      (MeasureTheory.integral_map (μ := μ) (f := g) (φ := A 0)
        hMap.measA0.aemeasurable hg_str)
  calc
    designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g))
        = (∫ ω, g (A 0 ω) ∂μ) := by
            simp [designMeanZ, Zcomp]
    _   = (∫ a, g a ∂Measure.map (A 0) μ) := by
            simp [hmap]
    _   = (∫ a, g a ∂ν) := by
            simp [hMap.map_eq]
    _   = attrMean ν g := by
            simp [attrMean]

/--
Bridge for second moments: if `A 0 ∼ ν`, then `E[(g(A 0))^2]` under the
experimental design distribution `μ` equals `E[(g)^2]` under the attribute
distribution `ν`.
-/
theorem designM2Z_Zcomp_eq_attrM2
    (g : Attr → ℝ)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hg : Measurable g) :
    designM2Z (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    attrM2 ν g := by
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
    designM2Z (μ := μ) (Z := Zcomp (A := A) (g := g))
        = (∫ ω, (g (A 0 ω)) ^ 2 ∂μ) := by
            simp [designM2Z, Zcomp]
    _   = (∫ ω, g2 (A 0 ω) ∂μ) := by
            simp [g2, pow_two]
    _   = (∫ a, g2 a ∂Measure.map (A 0) μ) := by
            simp [hmap]
    _   = (∫ a, g2 a ∂ν) := by
            simp [hMap.map_eq]
    _   = (∫ a, (g a) ^ 2 ∂ν) := by
            simp [g2, pow_two]
    _   = attrM2 ν g := by
            simp [attrM2]

/-- Bridge for variances (proxy form): follows from the mean and second-moment bridges. -/
theorem designVarZ_Zcomp_eq_attrVar
    (g : Attr → ℝ)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hg : Measurable g) :
    designVarZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    attrVar ν g := by
  have hmean :
      designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g)) = attrMean ν g :=
    designMeanZ_Zcomp_eq_attrMean (μ := μ) (A := A) (ν := ν) (g := g) hMap hg
  have hm2 :
      designM2Z (μ := μ) (Z := Zcomp (A := A) (g := g)) = attrM2 ν g :=
    designM2Z_Zcomp_eq_attrM2 (μ := μ) (A := A) (ν := ν) (g := g) hMap hg
  simp [designVarZ, attrVar, hmean, hm2]

/-- Bridge for SDs: follows from the variance bridge. -/
theorem designSDZ_Zcomp_eq_attrSD
    (g : Attr → ℝ)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hg : Measurable g) :
    designSDZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    attrSD ν g := by
  have hvar :
      designVarZ (μ := μ) (Z := Zcomp (A := A) (g := g)) = attrVar ν g :=
    designVarZ_Zcomp_eq_attrVar (μ := μ) (A := A) (ν := ν) (g := g) hMap hg
  simp [designSDZ, attrSD, hvar]

end

end ConjointSD
