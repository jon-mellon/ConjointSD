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
    (κ : Measure Ω) [IsProbabilityMeasure κ]
    {A : ℕ → Ω → Attr} {hA0 : Measurable (A 0)} :
    IsProbabilityMeasure (kappaDesign (κ := κ) (A := A)) :=
  by
    simpa [kappaDesign] using Measure.isProbabilityMeasure_map hA0.aemeasurable

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
Bridge for second moments: the second moment of `g(A 0)` under the sample law `κ`
equals the second moment of `g` under the pushforward attribute distribution.
-/
theorem designM2Z_Zcomp_eq_attrM2
    (g : Attr → ℝ)
    (hA0 : Measurable (A 0))
    (hg : Measurable g) :
    designM2Z (κ := κ) (Z := Zcomp (A := A) (g := g))
      =
    attrM2 (kappaDesign (κ := κ) (A := A)) g := by
  have hMeasSq : Measurable (fun a => (g a) ^ 2) := by
    simpa [pow_two] using (hg.mul hg)
  have hMeanSq :
      designMeanZ (κ := κ) (Z := Zcomp (A := A) (g := fun a => (g a) ^ 2))
        =
      attrMean (kappaDesign (κ := κ) (A := A)) (fun a => (g a) ^ 2) :=
    designMeanZ_Zcomp_eq_attrMean (κ := κ) (A := A) (g := fun a => (g a) ^ 2) hA0 hMeasSq
  simpa [designM2Z, attrM2, designMeanZ, Zcomp, attrMean] using hMeanSq

end

end ConjointSD
