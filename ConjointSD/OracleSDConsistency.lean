/-
ConjointSD/OracleSDConsistency.lean

Restate the existing SLLN-based SD consistency theorem so that the limit is expressed
as `popSDAttr ν g` (paper-facing object) rather than `popSDZ ...` (probability-space object).

This wires:
- SDDecompositionFromConjoint (sdHatZ → popSDZ)
to
- PopulationBridge / Transport (popSDZ = popSDAttr ν g under law(A0)=ν).
-/

import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.PopulationBridge

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

variable {Attr : Type*} [MeasurableSpace Attr]
variable (A : ℕ → Ω → Attr)
variable (ν : Measure Attr)

/--
If `A i` are i.i.d.-type draws and `g` is fixed (oracle score),
and `A 0` has law `ν`, then the empirical SD of `g(A i)` converges a.s. to `popSDAttr ν g`.
-/
theorem sd_component_consistent_to_popSDAttr
    (g : Attr → ℝ)
    (hScore : ScoreAssumptions (μ := μ) (A := A) g)
    (hA0 : Measurable (A 0))
    (hLaw : Measure.map (A 0) μ = ν) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (popSDAttr ν g)) := by
  -- existing result: sdHatZ → popSDZ (on Ω)
  have hSDZ :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g)) n ω)
          atTop
          (nhds (popSDZ (μ := μ) (Z := Zcomp (A := A) (g := g)))) :=
    sd_component_consistent (μ := μ) (A := A) (g := g) hScore
  -- rewrite the limit using PopulationBridge
  have hEq :
      popSDZ (μ := μ) (Z := Zcomp (A := A) (g := g)) = popSDAttr ν g :=
    popSDZ_Zcomp_eq_popSDAttr (μ := μ) (A := A) (ν := ν)
      (g := g) (hA0 := hA0) (hg := hScore.meas_g) (hLaw := hLaw)
  simpa [hEq] using hSDZ

end

end ConjointSD
