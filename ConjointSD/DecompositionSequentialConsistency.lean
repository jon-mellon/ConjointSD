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
variable {Θ : Type*}
variable {B : Type*} [Fintype B]

/-- A block score family parameterized by θ. -/
def gBlock (gB : B → Θ → Attr → ℝ) (b : B) : Θ → Attr → ℝ :=
  fun θ a => gB b θ a

/-- Total score (sum over blocks) parameterized by θ. -/
def gTotalΘ (gB : B → Θ → Attr → ℝ) : Θ → Attr → ℝ :=
  fun θ a => ∑ b : B, gB b θ a

/-- Per-block sequential consistency with a single `M` working for all `b : B` (finite B). -/
theorem sequential_consistency_blocks_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (hLaw : Measure.map (A 0) μ = ν)
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m b,
      SplitEvalAssumptions (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hG : ∀ b,
      GEstimationAssumptions (ν := ν) (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  classical
  have hEach :
      ∀ b : B,
        ∃ Mb : ℕ,
          ∀ m ≥ Mb,
            (∀ᵐ ω ∂μ,
              ∀ᶠ n : ℕ in atTop,
                totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
    intro b
    simpa [gBlock] using
      (sequential_consistency_ae
        (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat)
        (hSplit := fun m => hSplit m b)
        (hG := hG b)
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
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (hLaw : Measure.map (A 0) μ = ν)
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hGTotal :
      GEstimationAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  simpa [gTotalΘ] using
    (sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
      (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplitTotal)
      (hG := hGTotal)
      (ε := ε) (hε := hε))

theorem sequential_consistency_blocks_ae_of_bounded
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (hLaw : Measure.map (A 0) μ = ν)
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m b,
      SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hG : ∀ b,
      GEstimationAssumptions (ν := ν) (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  have hSplit' :
      ∀ m b,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m :=
    fun m b =>
      splitEvalAssumptions_of_bounded
        (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) (m := m) (hSplit m b)
  exact
    sequential_consistency_blocks_ae
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit') (hG := hG) (ε := ε) (hε := hε)

theorem sequential_consistency_total_ae_of_bounded
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (hLaw : Measure.map (A 0) μ = ν)
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hGTotal :
      GEstimationAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  have hSplitTotal' :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m :=
    fun m =>
      splitEvalAssumptions_of_bounded
        (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) (m := m) (hSplitTotal m)
  exact
    sequential_consistency_total_ae
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal') (hGTotal := hGTotal) (ε := ε) (hε := hε)

end

end ConjointSD
