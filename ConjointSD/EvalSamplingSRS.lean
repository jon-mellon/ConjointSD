import Mathlib
import ConjointSD.Assumptions

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]

theorem evalWeightMatchesPopMoments_of_law_eq
    {ρ : Measure Ω} [ProbMeasureAssumptions ρ]
    {A : ℕ → Ω → Attr} {ν : Measure Attr}
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (w : Attr → ℝ) (s : Attr → ℝ)
    (hW : w = fun _ => (1 : ℝ)) :
    EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν) (w := w) (s := s) := by
  haveI : IsProbabilityMeasure (kappaDesign (κ := ρ) (A := A)) :=
    Measure.isProbabilityMeasure_map hLaw.measA0.aemeasurable
  have hkappa : kappaDesign (κ := ρ) (A := A) = ν := by
    simpa [kappaDesign] using hLaw.map_eq
  haveI : IsProbabilityMeasure ν := by
    simpa [hkappa] using
      (inferInstance : IsProbabilityMeasure (kappaDesign (κ := ρ) (A := A)))
  refine
    { measA0 := hLaw.measA0
      mean_eq := ?_
      m2_eq := ?_ }
  · simp [hW, attrMean, hkappa, div_eq_mul_inv, mul_comm]
  · simp [hW, attrM2, hkappa, div_eq_mul_inv, mul_comm]

end

end ConjointSD
