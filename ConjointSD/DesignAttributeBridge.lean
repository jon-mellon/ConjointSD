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

-- Pushforward of a probability measure is a probability measure when the map is measurable.
instance probMeasureAssumptions_map_of_measurable
    {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    {A : ℕ → Ω → Attr} {hA0 : Measurable (A 0)} :
    ProbMeasureAssumptions (Measure.map (A 0) μ) :=
  ⟨Measure.isProbabilityMeasure_map hA0.aemeasurable⟩

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]
variable (A : ℕ → Ω → Attr)

/--
Bridge for means: if `A 0 ∼ ν`, then the mean of `g(A 0)` under the experimental
design distribution `μ` equals the mean of `g` under the attribute distribution `ν`.
-/
theorem designMeanZ_Zcomp_eq_attrMean
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    attrMean (Measure.map (A 0) μ) g := by
  have hg_str : AEStronglyMeasurable g (Measure.map (A 0) μ) :=
    hg.aemeasurable.aestronglyMeasurable
  have hmap :
      (∫ a, g a ∂Measure.map (A 0) μ) = (∫ ω, g (A 0 ω) ∂μ) := by
    -- change-of-variables for pushforward measures
    simpa using
      (MeasureTheory.integral_map (μ := μ) (f := g) (φ := A 0)
        hA0.aemeasurable hg_str)
  calc
    designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g))
        = (∫ ω, g (A 0 ω) ∂μ) := by
            simp [designMeanZ, Zcomp]
    _   = (∫ a, g a ∂Measure.map (A 0) μ) := by
            simp [hmap]
    _   = attrMean (Measure.map (A 0) μ) g := by
            simp [attrMean]

/--
Bridge for second moments: if `A 0 ∼ ν`, then `E[(g(A 0))^2]` under the
experimental design distribution `μ` equals `E[(g)^2]` under the attribute
distribution `ν`.
-/
theorem designM2Z_Zcomp_eq_attrM2
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designM2Z (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    attrM2 (Measure.map (A 0) μ) g := by
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
        hA0.aemeasurable hg2_str)
  calc
    designM2Z (μ := μ) (Z := Zcomp (A := A) (g := g))
        = (∫ ω, (g (A 0 ω)) ^ 2 ∂μ) := by
            simp [designM2Z, Zcomp]
    _   = (∫ ω, g2 (A 0 ω) ∂μ) := by
            simp [g2, pow_two]
    _   = (∫ a, g2 a ∂Measure.map (A 0) μ) := by
            simp [hmap]
    _   = (∫ a, (g a) ^ 2 ∂Measure.map (A 0) μ) := by
            simp [g2, pow_two]
    _   = attrM2 (Measure.map (A 0) μ) g := by
            simp [attrM2]

/-- Bridge for variances (proxy form): follows from the mean and second-moment bridges. -/
theorem designVarZ_Zcomp_eq_attrVar
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designVarZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    attrVar (Measure.map (A 0) μ) g := by
  have hmean :
      designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := g)) =
        attrMean (Measure.map (A 0) μ) g :=
    designMeanZ_Zcomp_eq_attrMean (μ := μ) (A := A) (g := g) hA0 hg
  have hm2 :
      designM2Z (μ := μ) (Z := Zcomp (A := A) (g := g)) =
        attrM2 (Measure.map (A 0) μ) g :=
    designM2Z_Zcomp_eq_attrM2 (μ := μ) (A := A) (g := g) hA0 hg
  simp [designVarZ, attrVar, hmean, hm2]

/-- Bridge for SDs: follows from the variance bridge. -/
theorem designSDZ_Zcomp_eq_attrSD
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designSDZ (μ := μ) (Z := Zcomp (A := A) (g := g))
      =
    attrSD (Measure.map (A 0) μ) g := by
  have hvar :
      designVarZ (μ := μ) (Z := Zcomp (A := A) (g := g)) =
        attrVar (Measure.map (A 0) μ) g :=
    designVarZ_Zcomp_eq_attrVar (μ := μ) (A := A) (g := g) hA0 hg
  simp [designSDZ, attrSD, hvar]

end

end ConjointSD
