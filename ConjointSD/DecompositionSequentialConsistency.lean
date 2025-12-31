/-
ConjointSD/DecompositionSequentialConsistency.lean

Route 1 (assumption-bundling) sequential consistency for an SD decomposition.

Provides:
1) Per-block sequential consistency with a single M working for all b : B (finite).
2) Total-score sequential consistency for the summed score.
-/

import Mathlib
import ConjointSD.SequentialConsistency
import ConjointSD.SampleSplitting
import ConjointSD.EstimatedG
import ConjointSD.Transport

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*} [TopologicalSpace Θ]
variable {B : Type*} [Fintype B]

/-- A block score family parameterized by θ. -/
def gBlock (gB : B → Θ → Attr → ℝ) (b : B) : Θ → Attr → ℝ :=
  fun θ a => gB b θ a

/-- Total score (sum over blocks) parameterized by θ. -/
def gTotalΘ (gB : B → Θ → Attr → ℝ) : Θ → Attr → ℝ :=
  fun θ a => ∑ b : B, gB b θ a

/-- Per-block sequential consistency with a single `M` working for all `b : B` (finite B). -/
theorem sequential_consistency_blocks_ae
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (w : Attr → ℝ)
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m b,
      SplitEvalWeightAssumptions (μ := μ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hMom : ∀ m b,
      EvalWeightMatchesAttrMoments (μ := μ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν w (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  classical
  have hEach :
      ∀ b : B,
        ∃ Mb : ℕ,
          ∀ m ≥ Mb,
            (∀ᵐ ω ∂μ,
              ∀ᶠ n : ℕ in atTop,
                totalErr μ A ν w
                  (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
    intro b
    simpa [gBlock] using
      (sequential_consistency_ae
        (μ := μ) (A := A) (ν := ν) (w := w)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat)
        (hSplit := fun m => hSplit m b)
        (hMom := fun m => hMom m b)
        (hθ := hθ) (hCont := hCont b)
        (ε := ε) (hε := hε))
  choose Mb hMb using hEach
  let M : ℕ := (Finset.univ : Finset B).sup Mb
  refine ⟨M, ?_⟩
  intro m hm b
  have hMb_le_M : Mb b ≤ M := by
    have hb : b ∈ (Finset.univ : Finset B) := by simp
    exact Finset.le_sup hb
  have hMb_le_m : Mb b ≤ m := le_trans hMb_le_M hm
  -- Now apply the block-specific conclusion.
  exact hMb b m hMb_le_m

/-- Total-score sequential consistency for the summed score `gTotalΘ`. -/
theorem sequential_consistency_total_ae
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (w : Attr → ℝ)
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (μ := μ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hMom : ∀ m,
      EvalWeightMatchesAttrMoments (μ := μ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν w (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  simpa [gTotalΘ] using
    (sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (w := w)
      (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplitTotal)
      (hMom := hMom)
      (hθ := hθ) (hCont := hContTotal)
      (ε := ε) (hε := hε))

theorem sequential_consistency_blocks_ae_of_bounded
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (w : Attr → ℝ)
    (hPop : DesignAttrIID (μ := μ) A)
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m b,
      SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hWeight : ScoreAssumptions (μ := μ) (A := A) (g := w))
    (hWeightScore : ∀ m b,
      ScoreAssumptions (μ := μ) (A := A)
        (g := fun a => w a * gHat (gBlock (gB := gB) b) θhat m a))
    (hWeightScoreSq : ∀ m b,
      ScoreAssumptions (μ := μ) (A := A)
        (g := fun a => w a * (gHat (gBlock (gB := gB) b) θhat m a) ^ 2))
    (hW0 : designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := w)) ≠ 0)
    (hMom : ∀ m b,
      EvalWeightMatchesAttrMoments (μ := μ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  have hSplit' :
      ∀ m b,
        SplitEvalWeightAssumptions (μ := μ) (A := A) (w := w)
          (g := gBlock (gB := gB) b) (θhat := θhat) m :=
    fun m b =>
      { hScore :=
          (splitEvalAssumptions_of_bounded
            (μ := μ) (A := A) (hPop := hPop)
            (g := gBlock (gB := gB) b) (θhat := θhat) (m := m) (hSplit m b)).hScore
        hWeight := hWeight
        hWeightScore := hWeightScore m b
        hWeightScoreSq := hWeightScoreSq m b
        hW0 := hW0 }
  exact
    sequential_consistency_blocks_ae
      (μ := μ) (A := A) (ν := ν) (w := w)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit') (hMom := hMom) (hθ := hθ) (hCont := hCont) (ε := ε) (hε := hε)

theorem sequential_consistency_total_ae_of_bounded
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (w : Attr → ℝ)
    (hPop : DesignAttrIID (μ := μ) A)
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hWeight : ScoreAssumptions (μ := μ) (A := A) (g := w))
    (hWeightScore : ∀ m,
      ScoreAssumptions (μ := μ) (A := A)
        (g := fun a => w a * gHat (gTotalΘ (gB := gB)) θhat m a))
    (hWeightScoreSq : ∀ m,
      ScoreAssumptions (μ := μ) (A := A)
        (g := fun a => w a * (gHat (gTotalΘ (gB := gB)) θhat m a) ^ 2))
    (hW0 : designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := w)) ≠ 0)
    (hMom : ∀ m,
      EvalWeightMatchesAttrMoments (μ := μ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  have hSplitTotal' :
      ∀ m,
        SplitEvalWeightAssumptions (μ := μ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m :=
    fun m =>
      { hScore :=
          (splitEvalAssumptions_of_bounded
            (μ := μ) (A := A) (hPop := hPop)
            (g := gTotalΘ (gB := gB)) (θhat := θhat) (m := m) (hSplitTotal m)).hScore
        hWeight := hWeight
        hWeightScore := hWeightScore m
        hWeightScoreSq := hWeightScoreSq m
        hW0 := hW0 }
  exact
    sequential_consistency_total_ae
      (μ := μ) (A := A) (ν := ν) (w := w)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal') (hMom := hMom) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)

end

end ConjointSD
