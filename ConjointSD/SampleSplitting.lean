/-
ConjointSD/SampleSplitting.lean

Evaluation-stage convergence for sample-splitting arguments.

For a fixed training index `m`, treat `gHat g θhat m` as a fixed (“oracle”) score
function and apply the oracle SD consistency theorem.
-/

import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.PopulationBridge
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

lemma splitEvalAssumptions_of_bounded
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := g) (θhat := θhat) m) :
    SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m := by
  have hScore :
      ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m) :=
    scoreAssumptions_of_bounded
      (μ := μ) (A := A) (g := gHat g θhat m)
      (hPop := h.hPop) (hMeas := h.hMeas) (hBound := h.hBound)
  exact ⟨hScore⟩

/--
For fixed training index `m`, the empirical SD of `gHat g θhat m (A i)` converges a.s.
to the population SD under the evaluation attribute law `law(A 0)`.
-/
theorem sdHat_fixed_m_tendsto_ae_popSDAttr
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
        atTop
        (nhds (popSDAttr (Measure.map (A 0) μ) (gHat g θhat m))) := by
  have hSDZ :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
          atTop
          (nhds (popSDZ (μ := μ) (Z := Zcomp (A := A) (g := gHat g θhat m)))) :=
    sd_component_consistent (μ := μ) (A := A) (g := gHat g θhat m) h.hScore
  have hEq :
      popSDZ (μ := μ) (Z := Zcomp (A := A) (g := gHat g θhat m)) =
        popSDAttr (Measure.map (A 0) μ) (gHat g θhat m) :=
    popSDZ_Zcomp_eq_popSDAttr (μ := μ) (A := A) (ν := Measure.map (A 0) μ)
      (g := gHat g θhat m)
      (hMap := { measA0 := h.hScore.popiid.measA 0, map_eq := rfl })
      (hg := h.hScore.meas_g)
  simpa [hEq] using hSDZ

end

end ConjointSD
