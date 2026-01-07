import Mathlib
import ConjointSD.PaperWrappers
import ConjointSD.ApproxTargetEquivalence
import ConjointSD.ApproxAssumptions

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

section SDSequentialConsistency

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}
variable {B : Type*} [Fintype B]

variable (ρ : Measure Ω) [IsProbabilityMeasure ρ]
variable (A : ℕ → Ω → Attr)
variable (ν_pop : Measure Attr) [IsProbabilityMeasure ν_pop]

variable (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

/-!
## 4b) Approximate targets: carry an explicit misspecification bound
-/

/--
Blocks: sequential consistency + ν_pop-a.e. ε-approximation yields convergence with an SD bound.
-/
theorem paper_sd_blocks_sequential_consistency_to_approx_target_ae
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν_pop := ν_pop))
    (hSplitBounded : ∀ m b,
      SplitEvalAssumptionsBounded (ρ := ρ) (A := A)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hMean : ∀ b : B,
      Tendsto (fun m => attrMean ν_pop (gHat (gBlock (gB := gB) b) θhat m)) atTop
        (nhds (attrMean ν_pop (gBlock (gB := gB) b θ0))))
    (hM2 : ∀ b : B,
      Tendsto (fun m => attrM2 ν_pop (gHat (gBlock (gB := gB) b) θhat m)) atTop
        (nhds (attrM2 ν_pop (gBlock (gB := gB) b θ0))))
    (gTrueB : B → Attr → ℝ)
    (C δ : ℝ)
    (hApprox :
      ∀ b : B,
        ApproxInvarianceAE (ν_pop := ν_pop)
          (s := gBlock (gB := gB) b θ0) (t := gTrueB b) δ)
    (hBoundS :
      ∀ b : B, BoundedAE (ν_pop := ν_pop)
        (s := gBlock (gB := gB) b θ0) C)
    (hBoundT :
      ∀ b : B, BoundedAE (ν_pop := ν_pop) (s := gTrueB b) C)
    (hMomS :
      ∀ b : B, AttrMomentAssumptions (ν_pop := ν_pop)
        (s := gBlock (gB := gB) b θ0))
    (hMomT :
      ∀ b : B, AttrMomentAssumptions (ν_pop := ν_pop) (s := gTrueB b))
    (hVarS :
      ∀ b : B, 0 ≤ attrVar (ν_pop) (gBlock (gB := gB) b θ0))
    (hVarT : ∀ b : B, 0 ≤ attrVar (ν_pop) (gTrueB b))
    (hδ : 0 ≤ δ)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A (ν_pop)
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε)
          ∧
          |attrSD (ν_pop) (gBlock (gB := gB) b θ0)
              - attrSD (ν_pop) (gTrueB b)|
            ≤ Real.sqrt (4 * C * δ) := by
  rcases paper_sd_blocks_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν_pop := ν_pop) (hLaw := hLaw)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitBounded := hSplitBounded) (hMean := hMean) (hM2 := hM2)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  have hCons := hM m hm b
  have hEq :
      |attrSD (ν_pop) (gBlock (gB := gB) b θ0)
          - attrSD (ν_pop) (gTrueB b)|
        ≤ Real.sqrt (4 * C * δ) :=
    attrSD_diff_le_of_approx_ae
      (ν_pop := ν_pop) (s := gBlock (gB := gB) b θ0) (t := gTrueB b)
      (hs := hMomS b) (ht := hMomT b)
      (hBoundS := hBoundS b) (hBoundT := hBoundT b)
      (hApprox := hApprox b) (hε := hδ)
      (hVarS := hVarS b) (hVarT := hVarT b)
  exact ⟨hCons, hEq⟩

end SDSequentialConsistency

end ConjointSD
