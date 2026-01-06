/-
ConjointSD/SampleSplitting.lean

Evaluation-stage convergence for sample-splitting arguments.

For a fixed training index `m`, treat `gHat g θhat m` as a fixed (“oracle”) score
function and apply the oracle SD consistency theorem.
-/

import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.DesignAttributeBridge
import ConjointSD.EstimatedG
import ConjointSD.Assumptions

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/--
For fixed training index `m`, the empirical SD of `gHat g θhat m (A i)` converges a.s.
    to the population SD.
-/
theorem sdHat_fixed_m_tendsto_ae_attrSD
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptionsBounded
      (ρ := ρ) (A := A) (g := g) (θhat := θhat) m)
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν)) :
    ∀ᵐ ω ∂ρ,
      Tendsto
        (fun n : ℕ =>
          sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
        atTop
        (nhds (attrSD ν (gHat g θhat m))) := by
  have hSDZ :
      ∀ᵐ ω ∂ρ,
        Tendsto
          (fun n : ℕ =>
            sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
          atTop
          (nhds (designSDZ (κ := ρ)
            (Z := Zcomp (A := A) (g := gHat g θhat m)))) := by
    have hPop : DesignAttrIID (κ := ρ) A :=
      { measA := h.hIID.measA, indepA := h.hIID.indepA, identA := h.hIID.identA }
    exact sdHatZ_tendsto_ae_of_score
      (μexp := ρ) (A := A) (g := gHat g θhat m)
      hPop h.hMeasG h.hBoundG
  have hMean :
      designMeanZ (κ := ρ)
        (Z := Zcomp (A := A) (g := gHat g θhat m)) =
      attrMean ν (gHat g θhat m) := by
    simpa [kappaDesign, hLaw.map_eq] using
      (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A) (g := gHat g θhat m)
        (hA0 := hLaw.measA0) (hg := h.hMeasG))
  have hM2 :
      designM2Z (κ := ρ)
        (Z := Zcomp (A := A) (g := gHat g θhat m)) =
      attrM2 ν (gHat g θhat m) := by
    simpa [kappaDesign, hLaw.map_eq] using
      (designM2Z_Zcomp_eq_attrM2 (κ := ρ) (A := A) (g := gHat g θhat m)
        (hA0 := hLaw.measA0) (hg := h.hMeasG))
  have hEq :
      designSDZ (κ := ρ)
        (Z := Zcomp (A := A) (g := gHat g θhat m)) =
      attrSD ν (gHat g θhat m) := by
    simp [designSDZ, designVarZ, attrSD, attrVar, hMean, hM2]
  refine hSDZ.mono ?_
  intro ω hω
  simpa [hEq] using hω

end

end ConjointSD
