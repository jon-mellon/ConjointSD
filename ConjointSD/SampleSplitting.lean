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
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
    (A : ℕ → Ω → Attr)
    (hPop : EvalAttrIID (κ := ρ) A)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptionsBounded (ρ := ρ) (A := A) (g := g) (θhat := θhat) m) :
    SplitEvalAssumptions (ρ := ρ) (A := A) (g := g) (θhat := θhat) m := by
  have hPop' : DesignAttrIID (κ := ρ) A :=
    { measA := hPop.measA, indepA := hPop.indepA, identA := hPop.identA }
  have hScore :
      ScoreAssumptions (κ := ρ) (A := A) (g := gHat g θhat m) :=
    scoreAssumptions_of_bounded
      (μexp := ρ) (A := A) (g := gHat g θhat m)
      (hPop := hPop') (hMeas := h.hMeas) (hBound := h.hBound)
  exact ⟨hPop, hScore⟩

lemma splitEvalAssumptions_of_bounded_of_stream
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ)
    (hStream : ConjointRandomizationStream (μexp := ρ) (A := A) (Y := Y))
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptionsBounded (ρ := ρ) (A := A) (g := g) (θhat := θhat) m) :
    SplitEvalAssumptions (ρ := ρ) (A := A) (g := g) (θhat := θhat) m := by
  have hPopDesign : DesignAttrIID (κ := ρ) A :=
    DesignAttrIID.of_randomization_stream (μexp := ρ) (A := A) (Y := Y) hStream
  have hPop : EvalAttrIID (κ := ρ) A :=
    { measA := hPopDesign.measA, indepA := hPopDesign.indepA, identA := hPopDesign.identA }
  exact splitEvalAssumptions_of_bounded
    (ρ := ρ) (A := A) (hPop := hPop) (g := g) (θhat := θhat) (m := m) h

lemma splitEvalWeightAssumptions_of_stream
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ)
    (hStream : ConjointRandomizationStream (μexp := ρ) (A := A) (Y := Y))
    (w : Attr → ℝ) (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalWeightAssumptionsNoIID
      (ρ := ρ) (A := A) (w := w) (g := g) (θhat := θhat) m) :
    SplitEvalWeightAssumptions
      (ρ := ρ) (A := A) (w := w) (g := g) (θhat := θhat) m := by
  have hPopDesign : DesignAttrIID (κ := ρ) A :=
    DesignAttrIID.of_randomization_stream (μexp := ρ) (A := A) (Y := Y) hStream
  have hPop : EvalAttrIID (κ := ρ) A :=
    { measA := hPopDesign.measA, indepA := hPopDesign.indepA, identA := hPopDesign.identA }
  exact
    { hIID := hPop
      hScore := h.hScore
      hWeight := h.hWeight
      hWeightScore := h.hWeightScore
      hWeightScoreSq := h.hWeightScoreSq
      hW0 := h.hW0 }

/--
For fixed training index `m`, the empirical SD of `gHat g θhat m (A i)` converges a.s.
    to the population SD under weighted evaluation moments.
-/
theorem sdHat_fixed_m_tendsto_ae_attrSD
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr)
    (w : Attr → ℝ)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w) (g := g) (θhat := θhat) m)
    (hMom : EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
      (w := w) (s := gHat g θhat m)) :
    ∀ᵐ ω ∂ρ,
      Tendsto
        (fun n : ℕ =>
          sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
            (W := Wcomp (A := A) (w := w)) n ω)
        atTop
        (nhds (attrSD ν (gHat g θhat m))) := by
  have hSDZ :
      ∀ᵐ ω ∂ρ,
        Tendsto
          (fun n : ℕ =>
            sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) n ω)
          atTop
          (nhds (designSDZW (κ := ρ)
            (Z := Zcomp (A := A) (g := gHat g θhat m))
            (W := Wcomp (A := A) (w := w)))) := by
    have hPop : DesignAttrIID (κ := ρ) A :=
      { measA := h.hIID.measA, indepA := h.hIID.indepA, identA := h.hIID.identA }
    exact sdHatZW_tendsto_ae_of_score
      (μexp := ρ) (A := A) (w := w) (g := gHat g θhat m) hPop
      (hWZ := h.hWeightScore) (hWZ2 := h.hWeightScoreSq) (hW := h.hWeight)
      (hW0 := h.hW0)
  have hEq :
      designSDZW (κ := ρ)
        (Z := Zcomp (A := A) (g := gHat g θhat m))
        (W := Wcomp (A := A) (w := w)) =
        attrSD ν (gHat g θhat m) :=
    by
      have hMeanW :
          designMeanZ (κ := ρ) (Z := Wcomp (A := A) (w := w)) =
            attrMean (kappaDesign (κ := ρ) (A := A)) w := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A) (g := w)
            (hA0 := hMom.measA0) (hg := h.hWeight.meas_g))
      have hMeanWZ :
          designMeanZ (κ := ρ)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω
                  * Zcomp (A := A) (g := gHat g θhat m) i ω) =
            attrMean (kappaDesign (κ := ρ) (A := A)) (fun a => w a * gHat g θhat m a) := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A)
            (g := fun a => w a * gHat g θhat m a)
            (hA0 := hMom.measA0) (hg := h.hWeightScore.meas_g))
      have hM2WZ :
          designMeanZ (κ := ρ)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω
                  * (Zcomp (A := A) (g := gHat g θhat m) i ω) ^ 2) =
            attrMean (kappaDesign (κ := ρ) (A := A)) (fun a => w a * (gHat g θhat m a) ^ 2) := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A)
            (g := fun a => w a * (gHat g θhat m a) ^ 2)
            (hA0 := hMom.measA0) (hg := h.hWeightScoreSq.meas_g))
      have hMean :
          designMeanZW (κ := ρ)
              (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) =
            attrMean ν (gHat g θhat m) := by
        simp [designMeanZW, hMeanW, hMeanWZ, hMom.mean_eq, attrMean]
      have hM2 :
          designM2ZW (κ := ρ)
              (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) =
            attrM2 ν (gHat g θhat m) := by
        simpa [designM2ZW, hMeanW, hM2WZ, attrMean, attrM2] using hMom.m2_eq
      simp [designSDZW, designVarZW, attrSD, attrVar, hMean, hM2]
  simpa [hEq] using hSDZ

end

end ConjointSD
