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

lemma splitEvalAssumptions_of_bounded
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (hPop : DesignAttrIID (μ := μ) A)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := g) (θhat := θhat) m) :
    SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m := by
  have hScore :
      ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m) :=
    scoreAssumptions_of_bounded
      (μ := μ) (A := A) (g := gHat g θhat m)
      (hPop := hPop) (hMeas := h.hMeas) (hBound := h.hBound)
  exact ⟨hScore⟩

lemma splitEvalAssumptions_of_bounded_of_stream
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ)
    (hStream : ConjointRandomizationStream (μ := μ) (A := A) (Y := Y))
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := g) (θhat := θhat) m) :
    SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m := by
  have hPop : DesignAttrIID (μ := μ) A :=
    DesignAttrIID.of_randomization_stream (μ := μ) (A := A) (Y := Y) hStream
  exact splitEvalAssumptions_of_bounded
    (μ := μ) (A := A) (hPop := hPop) (g := g) (θhat := θhat) (m := m) h

/--
For fixed training index `m`, the empirical SD of `gHat g θhat m (A i)` converges a.s.
    to the attribute-distribution SD under the evaluation attribute law `law(A 0)`.
-/
theorem sdHat_fixed_m_tendsto_ae_attrSD
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m)
    (hMom : EvalAttrMoments (μ := μ) (A := A) (ν := ν)
      (s := gHat g θhat m)) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
        atTop
        (nhds (attrSD ν (gHat g θhat m))) := by
  have hSDZ :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
          atTop
          (nhds (designSDZ (μ := μ) (Z := Zcomp (A := A) (g := gHat g θhat m)))) :=
    sd_component_consistent (μ := μ) (A := A) (g := gHat g θhat m) h.hScore
  have hEq :
      designSDZ (μ := μ) (Z := Zcomp (A := A) (g := gHat g θhat m)) =
        attrSD ν (gHat g θhat m) :=
    by
      have hDesign :
          designSDZ (μ := μ) (Z := Zcomp (A := A) (g := gHat g θhat m)) =
            attrSD (Measure.map (A 0) μ) (gHat g θhat m) := by
        simpa using
          (designSDZ_Zcomp_eq_attrSD (μ := μ) (A := A) (g := gHat g θhat m)
            (hA0 := hMom.measA0) (hg := h.hScore.meas_g))
      have hMomEq :
          attrSD (Measure.map (A 0) μ) (gHat g θhat m) =
            attrSD ν (gHat g θhat m) := by
        exact attrSD_eq_of_moments (s := gHat g θhat m) hMom.mean_eq hMom.m2_eq
      simpa [hMomEq] using hDesign
  simpa [hEq] using hSDZ

end

end ConjointSD
