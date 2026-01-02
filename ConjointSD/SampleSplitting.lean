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

lemma splitEvalWeightAssumptions_of_bounded
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
    (A : ℕ → Ω → Attr)
    (w : Attr → ℝ) (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalWeightAssumptionsBounded
      (ρ := ρ) (A := A) (w := w) (g := g) (θhat := θhat) m) :
    SplitEvalWeightAssumptions
      (ρ := ρ) (A := A) (w := w) (g := g) (θhat := θhat) m := by
  have hPop : DesignAttrIID (κ := ρ) A :=
    { measA := h.hIID.measA, indepA := h.hIID.indepA, identA := h.hIID.identA }
  have hScore :
      ScoreAssumptions (κ := ρ) (A := A) (g := gHat g θhat m) :=
    scoreAssumptions_of_bounded
      (μexp := ρ) (A := A) (g := gHat g θhat m)
      (hPop := hPop) (hMeas := h.hMeasG) (hBound := h.hBoundG)
  have hWeight :
      ScoreAssumptions (κ := ρ) (A := A) (g := w) :=
    scoreAssumptions_of_bounded
      (μexp := ρ) (A := A) (g := w)
      (hPop := hPop) (hMeas := h.hMeasW) (hBound := h.hBoundW)
  obtain ⟨Cw, hCw0, hCw⟩ := h.hBoundW
  obtain ⟨Cg, hCg0, hCg⟩ := h.hBoundG
  have hMeasWG : Measurable (fun a => w a * gHat g θhat m a) :=
    h.hMeasW.mul h.hMeasG
  have hBoundWG :
      ∃ C, 0 ≤ C ∧ ∀ a, |w a * gHat g θhat m a| ≤ C := by
    refine ⟨Cw * Cg, mul_nonneg hCw0 hCg0, ?_⟩
    intro a
    have hmul : |w a| * |gHat g θhat m a| ≤ Cw * Cg :=
      mul_le_mul (hCw a) (hCg a) (abs_nonneg _) hCw0
    simpa [abs_mul] using hmul
  have hWeightScore :
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * gHat g θhat m a) :=
    scoreAssumptions_of_bounded
      (μexp := ρ) (A := A) (g := fun a => w a * gHat g θhat m a)
      (hPop := hPop) (hMeas := hMeasWG) (hBound := hBoundWG)
  have hMeasSq : Measurable (fun a => (gHat g θhat m a) ^ 2) := by
    simpa [pow_two] using (h.hMeasG.mul h.hMeasG)
  have hMeasWSq : Measurable (fun a => w a * (gHat g θhat m a) ^ 2) :=
    h.hMeasW.mul hMeasSq
  have hBoundSq' : ∀ a, |(gHat g θhat m a) ^ 2| ≤ Cg ^ 2 := by
    intro a
    have hmul : |gHat g θhat m a| * |gHat g θhat m a| ≤ Cg * Cg :=
      mul_le_mul (hCg a) (hCg a) (abs_nonneg _) hCg0
    simpa [pow_two, abs_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hBoundWSq :
      ∃ C, 0 ≤ C ∧ ∀ a, |w a * (gHat g θhat m a) ^ 2| ≤ C := by
    refine ⟨Cw * Cg ^ 2, mul_nonneg hCw0 (by nlinarith), ?_⟩
    intro a
    have hmul : |w a| * |(gHat g θhat m a) ^ 2| ≤ Cw * Cg ^ 2 :=
      mul_le_mul (hCw a) (hBoundSq' a) (abs_nonneg _) hCw0
    simpa [abs_mul] using hmul
  have hWeightScoreSq :
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * (gHat g θhat m a) ^ 2) :=
    scoreAssumptions_of_bounded
      (μexp := ρ) (A := A) (g := fun a => w a * (gHat g θhat m a) ^ 2)
      (hPop := hPop) (hMeas := hMeasWSq) (hBound := hBoundWSq)
  exact
    { hIID := h.hIID
      hScore := hScore
      hWeight := hWeight
      hWeightScore := hWeightScore
      hWeightScoreSq := hWeightScoreSq
      hW0 := h.hW0 }

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
    (h : SplitEvalWeightAssumptionsBounded
      (ρ := ρ) (A := A) (w := w) (g := g) (θhat := θhat) m)
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
      (μexp := ρ) (A := A) (w := w) (g := gHat g θhat m)
      hPop h.hMeasW h.hBoundW h.hMeasG h.hBoundG h.hW0
  have hEq :
      designSDZW (κ := ρ)
        (Z := Zcomp (A := A) (g := gHat g θhat m))
        (W := Wcomp (A := A) (w := w)) =
        attrSD ν (gHat g θhat m) :=
    by
      have hMeasWG : Measurable (fun a => w a * gHat g θhat m a) :=
        h.hMeasW.mul h.hMeasG
      have hMeasSq : Measurable (fun a => (gHat g θhat m a) ^ 2) := by
        simpa [pow_two] using (h.hMeasG.mul h.hMeasG)
      have hMeasWSq : Measurable (fun a => w a * (gHat g θhat m a) ^ 2) :=
        h.hMeasW.mul hMeasSq
      have hMeanW :
          designMeanZ (κ := ρ) (Z := Wcomp (A := A) (w := w)) =
            attrMean (kappaDesign (κ := ρ) (A := A)) w := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A) (g := w)
            (hA0 := hMom.measA0) (hg := h.hMeasW))
      have hMeanWZ :
          designMeanZ (κ := ρ)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω
                  * Zcomp (A := A) (g := gHat g θhat m) i ω) =
            attrMean (kappaDesign (κ := ρ) (A := A)) (fun a => w a * gHat g θhat m a) := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A)
            (g := fun a => w a * gHat g θhat m a)
            (hA0 := hMom.measA0) (hg := hMeasWG))
      have hM2WZ :
          designMeanZ (κ := ρ)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω
                  * (Zcomp (A := A) (g := gHat g θhat m) i ω) ^ 2) =
            attrMean (kappaDesign (κ := ρ) (A := A)) (fun a => w a * (gHat g θhat m a) ^ 2) := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A)
            (g := fun a => w a * (gHat g θhat m a) ^ 2)
            (hA0 := hMom.measA0) (hg := hMeasWSq))
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
