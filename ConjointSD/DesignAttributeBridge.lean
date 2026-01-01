/-
ConjointSD/DesignAttributeBridge.lean

Bridge between:
- attribute-distribution functionals under the pushforward attribute law
  `kappaDesign (κ := κ) (A := A)` (attrMean/attrM2/attrVar/attrSD), and
- functionals under the sample law `κ : Measure Ω` for
  the induced score process `Zcomp (A := A) (g := g)`
  (designMeanZ/designM2Z/designVarZ/designSDZ).

We work with the pushforward attribute law `kappaDesign (κ := κ) (A := A)` induced by the
sample law `κ`.

Implementation note:
In this mathlib version, `MeasureTheory.integral_map` uses the argument name `φ` for the map.
It also expects:
- `AEMeasurable φ κ`, and
- `AEStronglyMeasurable f (Measure.map φ κ)` for the integrand.

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
    (κ : Measure Ω) [ProbMeasureAssumptions κ]
    {A : ℕ → Ω → Attr} {hA0 : Measurable (A 0)} :
    ProbMeasureAssumptions (kappaDesign (κ := κ) (A := A)) :=
  ⟨Measure.isProbabilityMeasure_map hA0.aemeasurable⟩

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (κ : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]
variable (A : ℕ → Ω → Attr)

/--
Bridge for means: the mean of `g(A 0)` under the sample law `κ`
equals the mean of `g` under the pushforward attribute distribution `kappaDesign`.
-/
theorem designMeanZ_Zcomp_eq_attrMean
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designMeanZ (κ := κ) (Z := Zcomp (A := A) (g := g))
      =
    attrMean (kappaDesign (κ := κ) (A := A)) g := by
  have hg_str : AEStronglyMeasurable g (kappaDesign (κ := κ) (A := A)) :=
    hg.aemeasurable.aestronglyMeasurable
  have hmap :
      (∫ a, g a ∂kappaDesign (κ := κ) (A := A)) = (∫ ω, g (A 0 ω) ∂κ) := by
    -- change-of-variables for pushforward measures
    simpa using
      (MeasureTheory.integral_map (μ := κ) (f := g) (φ := A 0)
        hA0.aemeasurable hg_str)
  calc
    designMeanZ (κ := κ) (Z := Zcomp (A := A) (g := g))
        = (∫ ω, g (A 0 ω) ∂κ) := by
            simp [designMeanZ, Zcomp]
    _   = (∫ a, g a ∂kappaDesign (κ := κ) (A := A)) := by
            simp [hmap]
    _   = attrMean (kappaDesign (κ := κ) (A := A)) g := by
            simp [attrMean]

/--
Bridge for second moments: `E[(g(A 0))^2]` under the sample law `κ`
equals `E[(g)^2]` under the pushforward attribute distribution `kappaDesign`.
-/
theorem designM2Z_Zcomp_eq_attrM2
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designM2Z (κ := κ) (Z := Zcomp (A := A) (g := g))
      =
    attrM2 (kappaDesign (κ := κ) (A := A)) g := by
  -- square via multiplication (avoids any separate pow measurability concerns)
  let g2 : Attr → ℝ := fun a => g a * g a
  have hg2 : Measurable g2 := by
    simpa [g2] using (hg.mul hg)
  have hg2_str : AEStronglyMeasurable g2 (kappaDesign (κ := κ) (A := A)) :=
    hg2.aemeasurable.aestronglyMeasurable
  have hmap :
      (∫ a, g2 a ∂kappaDesign (κ := κ) (A := A)) = (∫ ω, g2 (A 0 ω) ∂κ) := by
    simpa using
      (MeasureTheory.integral_map (μ := κ) (f := g2) (φ := A 0)
        hA0.aemeasurable hg2_str)
  calc
    designM2Z (κ := κ) (Z := Zcomp (A := A) (g := g))
        = (∫ ω, (g (A 0 ω)) ^ 2 ∂κ) := by
            simp [designM2Z, Zcomp]
    _   = (∫ ω, g2 (A 0 ω) ∂κ) := by
            simp [g2, pow_two]
    _   = (∫ a, g2 a ∂kappaDesign (κ := κ) (A := A)) := by
            simp [hmap]
    _   = (∫ a, (g a) ^ 2 ∂kappaDesign (κ := κ) (A := A)) := by
            simp [g2, pow_two]
    _   = attrM2 (kappaDesign (κ := κ) (A := A)) g := by
            simp [attrM2]

/-- Bridge for variances (proxy form): follows from the mean and second-moment bridges. -/
theorem designVarZ_Zcomp_eq_attrVar
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designVarZ (κ := κ) (Z := Zcomp (A := A) (g := g))
      =
    attrVar (kappaDesign (κ := κ) (A := A)) g := by
  have hmean :
      designMeanZ (κ := κ) (Z := Zcomp (A := A) (g := g)) =
        attrMean (kappaDesign (κ := κ) (A := A)) g :=
    designMeanZ_Zcomp_eq_attrMean (κ := κ) (A := A) (g := g) hA0 hg
  have hm2 :
      designM2Z (κ := κ) (Z := Zcomp (A := A) (g := g)) =
        attrM2 (kappaDesign (κ := κ) (A := A)) g :=
    designM2Z_Zcomp_eq_attrM2 (κ := κ) (A := A) (g := g) hA0 hg
  simp [designVarZ, attrVar, hmean, hm2]

/-- Bridge for SDs: follows from the variance bridge. -/
theorem designSDZ_Zcomp_eq_attrSD
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designSDZ (κ := κ) (Z := Zcomp (A := A) (g := g))
      =
    attrSD (kappaDesign (κ := κ) (A := A)) g := by
  have hvar :
      designVarZ (κ := κ) (Z := Zcomp (A := A) (g := g)) =
        attrVar (kappaDesign (κ := κ) (A := A)) g :=
    designVarZ_Zcomp_eq_attrVar (κ := κ) (A := A) (g := g) hA0 hg
  simp [designSDZ, attrSD, hvar]

end

end ConjointSD
