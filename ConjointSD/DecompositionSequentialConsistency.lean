/-
ConjointSD/DecompositionSequentialConsistency.lean

Route 1 (assumption-bundling) sequential consistency for an SD decomposition.

Provides:
1) Per-block sequential consistency with a single M working for all b : B (finite).
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
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (A : ℕ → Ω → Attr)
    (ν_pop : Measure Attr) [IsProbabilityMeasure ν_pop]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m b,
      SplitEvalAssumptionsBounded (ρ := ρ) (A := A)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν_pop := ν_pop))
    (hMean : ∀ b : B,
      Tendsto (fun m => attrMean ν_pop (gHat (gBlock (gB := gB) b) θhat m)) atTop
        (nhds (attrMean ν_pop (gBlock (gB := gB) b θ0))))
    (hM2 : ∀ b : B,
      Tendsto (fun m => attrM2 ν_pop (gHat (gBlock (gB := gB) b) θhat m)) atTop
        (nhds (attrM2 ν_pop (gBlock (gB := gB) b θ0))))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
              (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A ν_pop (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  classical
  have hEach :
      ∀ b : B,
        ∃ Mb : ℕ,
          ∀ m ≥ Mb,
            (∀ᵐ ω ∂ρ,
              ∀ᶠ n : ℕ in atTop,
                totalErr ρ A ν_pop
                  (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
    intro b
    simpa [gBlock] using
      (sequential_consistency_ae
        (ρ := ρ) (A := A) (ν_pop := ν_pop)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat)
        (hSplit := fun m => hSplit m b)
        (hLaw := hLaw)
        (hMean := hMean b)
        (hM2 := hM2 b)
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

end

end ConjointSD
