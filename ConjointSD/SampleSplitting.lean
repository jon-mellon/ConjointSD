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
    to the population SD under weighted evaluation moments.
-/
theorem sdHat_fixed_m_tendsto_ae_attrSD
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr)
    (w : Attr → ℝ)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalWeightAssumptions (μ := μ) (A := A) (w := w) (g := g) (θhat := θhat) m)
    (hMom : EvalWeightMatchesAttrMoments (μ := μ) (A := A) (ν := ν)
      (w := w) (s := gHat g θhat m)) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
            (W := Wcomp (A := A) (w := w)) n ω)
        atTop
        (nhds (attrSD ν (gHat g θhat m))) := by
  have hSDZ :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) n ω)
          atTop
          (nhds (designSDZW (μ := μ)
            (Z := Zcomp (A := A) (g := gHat g θhat m))
            (W := Wcomp (A := A) (w := w)))) := by
    have hW :
        IIDAssumptions (μ := μ) (Wcomp (A := A) (w := w)) :=
      iidAssumptions_Zcomp (μ := μ) (A := A) (g := w) h.hWeight
    have hWZ :
        IIDAssumptions (μ := μ)
          (fun i ω => Wcomp (A := A) (w := w) i ω
            * Zcomp (A := A) (g := gHat g θhat m) i ω) :=
      iidAssumptions_Zcomp (μ := μ) (A := A)
        (g := fun a => w a * gHat g θhat m a) h.hWeightScore
    have hWZ2 :
        IIDAssumptions (μ := μ)
          (fun i ω => Wcomp (A := A) (w := w) i ω
            * (Zcomp (A := A) (g := gHat g θhat m) i ω) ^ 2) :=
      iidAssumptions_Zcomp (μ := μ) (A := A)
        (g := fun a => w a * (gHat g θhat m a) ^ 2) h.hWeightScoreSq
    exact sdHatZW_tendsto_ae
      (μ := μ)
      (Z := Zcomp (A := A) (g := gHat g θhat m))
      (W := Wcomp (A := A) (w := w))
      hWZ hWZ2 hW h.hW0
  have hEq :
      designSDZW (μ := μ)
        (Z := Zcomp (A := A) (g := gHat g θhat m))
        (W := Wcomp (A := A) (w := w)) =
        attrSD ν (gHat g θhat m) :=
    by
      have hMeanW :
          designMeanZ (μ := μ) (Z := Wcomp (A := A) (w := w)) =
            attrMean (Measure.map (A 0) μ) w := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (μ := μ) (A := A) (g := w)
            (hA0 := hMom.measA0) (hg := h.hWeight.meas_g))
      have hMeanWZ :
          designMeanZ (μ := μ)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω
                  * Zcomp (A := A) (g := gHat g θhat m) i ω) =
            attrMean (Measure.map (A 0) μ) (fun a => w a * gHat g θhat m a) := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (μ := μ) (A := A)
            (g := fun a => w a * gHat g θhat m a)
            (hA0 := hMom.measA0) (hg := h.hWeightScore.meas_g))
      have hM2WZ :
          designMeanZ (μ := μ)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω
                  * (Zcomp (A := A) (g := gHat g θhat m) i ω) ^ 2) =
            attrMean (Measure.map (A 0) μ) (fun a => w a * (gHat g θhat m a) ^ 2) := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (μ := μ) (A := A)
            (g := fun a => w a * (gHat g θhat m a) ^ 2)
            (hA0 := hMom.measA0) (hg := h.hWeightScoreSq.meas_g))
      have hMean :
          designMeanZW (μ := μ)
              (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) =
            attrMean ν (gHat g θhat m) := by
        simp [designMeanZW, hMeanW, hMeanWZ, hMom.mean_eq, attrMean]
      have hM2 :
          designM2ZW (μ := μ)
              (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) =
            attrM2 ν (gHat g θhat m) := by
        simpa [designM2ZW, hMeanW, hM2WZ, attrMean, attrM2] using hMom.m2_eq
      simp [designSDZW, designVarZW, attrSD, attrVar, hMean, hM2]
  simpa [hEq] using hSDZ

end

end ConjointSD
