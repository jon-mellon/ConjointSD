import Mathlib
import ConjointSD.PaperWrappers
import ConjointSD.ApproxTargetEquivalence
import ConjointSD.ApproxModelBridge
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

variable (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
variable (A : ℕ → Ω → Attr)
variable (ν : Measure Attr) [ProbMeasureAssumptions ν]
variable (w : Attr → ℝ)
variable (w : Attr → ℝ)

variable (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

/-!
## 4b) Approximate targets: carry an explicit misspecification bound
-/

/--
Blocks: sequential consistency + ν-a.e. ε-approximation yields convergence with an SD bound.
-/
theorem paper_sd_blocks_sequential_consistency_to_approx_target_ae
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (hSplitBounded : ∀ m b,
      SplitEvalWeightAssumptionsBounded (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hPlug : ∀ b : B,
      PlugInMomentAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
    (gTrueB : B → Attr → ℝ)
    (C δ : ℝ)
    (hApprox :
      ∀ b : B,
        ApproxInvarianceAE (ν := ν)
          (s := gBlock (gB := gB) b θ0) (t := gTrueB b) δ)
    (hBoundS :
      ∀ b : B, BoundedAE (ν := ν)
        (s := gBlock (gB := gB) b θ0) C)
    (hBoundT :
      ∀ b : B, BoundedAE (ν := ν) (s := gTrueB b) C)
    (hMomS :
      ∀ b : B, AttrMomentAssumptions (ν := ν)
        (s := gBlock (gB := gB) b θ0))
    (hMomT :
      ∀ b : B, AttrMomentAssumptions (ν := ν) (s := gTrueB b))
    (hVarS :
      ∀ b : B, 0 ≤ attrVar (ν) (gBlock (gB := gB) b θ0))
    (hVarT : ∀ b : B, 0 ≤ attrVar (ν) (gTrueB b))
    (hδ : 0 ≤ δ)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A (ν) w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε)
          ∧
          |attrSD (ν) (gBlock (gB := gB) b θ0)
              - attrSD (ν) (gTrueB b)|
            ≤ Real.sqrt (4 * C * δ) := by
  rcases paper_sd_blocks_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hLaw := hLaw) (hW := hW)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitBounded := hSplitBounded) (hPlug := hPlug)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  have hCons := hM m hm b
  have hEq :
      |attrSD (ν) (gBlock (gB := gB) b θ0)
          - attrSD (ν) (gTrueB b)|
        ≤ Real.sqrt (4 * C * δ) :=
    attrSD_diff_le_of_approx_ae
      (ν := ν) (s := gBlock (gB := gB) b θ0) (t := gTrueB b)
      (hs := hMomS b) (ht := hMomT b)
      (hBoundS := hBoundS b) (hBoundT := hBoundT b)
      (hApprox := hApprox b) (hε := hδ)
      (hVarS := hVarS b) (hVarT := hVarT b)
  exact ⟨hCons, hEq⟩

/- Total-score: sequential consistency + ν-a.e. ε-approximation yields convergence with
an SD bound. -/
theorem paper_sd_total_sequential_consistency_to_approx_target_ae
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (hSplitTotalBounded :
      ∀ m,
        SplitEvalWeightAssumptionsBounded (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
    (gTrue : Attr → ℝ)
    (C δ : ℝ)
    (hApprox :
      ApproxInvarianceAE (ν := ν)
        (s := gTotalΘ (gB := gB) θ0) (t := gTrue) δ)
    (hBoundS : BoundedAE (ν := ν) (s := gTotalΘ (gB := gB) θ0) C)
    (hBoundT : BoundedAE (ν := ν) (s := gTrue) C)
    (hMomS :
      AttrMomentAssumptions (ν := ν) (s := gTotalΘ (gB := gB) θ0))
    (hMomT : AttrMomentAssumptions (ν := ν) (s := gTrue))
    (hVarS : 0 ≤ attrVar (ν) (gTotalΘ (gB := gB) θ0))
    (hVarT : 0 ≤ attrVar (ν) gTrue)
    (hδ : 0 ≤ δ)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        |attrSD (ν) (gTotalΘ (gB := gB) θ0)
            - attrSD (ν) gTrue|
          ≤ Real.sqrt (4 * C * δ) := by
  rcases paper_sd_total_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hLaw := hLaw) (hW := hW)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotalBounded := hSplitTotalBounded) (hPlugTotal := hPlugTotal)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hCons := hM m hm
  have hEq :
      |attrSD (ν) (gTotalΘ (gB := gB) θ0)
          - attrSD (ν) gTrue|
        ≤ Real.sqrt (4 * C * δ) :=
    attrSD_diff_le_of_approx_ae
      (ν := ν) (s := gTotalΘ (gB := gB) θ0) (t := gTrue)
      (hs := hMomS) (ht := hMomT)
      (hBoundS := hBoundS) (hBoundT := hBoundT)
      (hApprox := hApprox) (hε := hδ)
      (hVarS := hVarS) (hVarT := hVarT)
  exact ⟨hCons, hEq⟩

/-!
## 4c) Link well-specification to the true causal estimand `gStar`
-/

/-!
Approximate link: use an ε-approximate well-specification assumption to bound the SD target
error relative to `gStar`.
-/

theorem paper_sd_total_sequential_consistency_to_gStar_approx_ae_of_ApproxWellSpecifiedAE
    {Term : Type*} [Fintype Term] [DecidableEq B]
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hTotalModel :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x)
    (hspec :
      ApproxWellSpecifiedAE (ν := ν) (μexp := μexp) (Y := Y) (β := β) (φ := φ) δ)
    (hSplitTotalBounded :
      ∀ m,
        SplitEvalWeightAssumptionsBounded (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
    (C : ℝ)
    (hBoundS :
      BoundedAE (ν := ν) (s := gTotalΘ (gB := gB) θ0) C)
    (hBoundT :
      BoundedAE (ν := ν) (s := gStar (μexp := μexp) (Y := Y)) C)
    (hMomS :
      AttrMomentAssumptions (ν := ν) (s := gTotalΘ (gB := gB) θ0))
    (hMomT :
      AttrMomentAssumptions (ν := ν) (s := gStar (μexp := μexp) (Y := Y)))
    (hVarS : 0 ≤ attrVar (ν) (gTotalΘ (gB := gB) θ0))
    (hVarT : 0 ≤ attrVar (ν) (gStar (μexp := μexp) (Y := Y)))
    (hδ : 0 ≤ δ)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        |attrSD (ν) (gTotalΘ (gB := gB) θ0)
            - attrSD (ν) (gStar (μexp := μexp) (Y := Y))|
          ≤ Real.sqrt (4 * C * δ) := by
  have hApprox :
      ApproxInvarianceAE
        (ν := ν)
        (s := gTotalΘ (gB := gB) θ0)
        (t := gStar (μexp := μexp) (Y := Y))
        δ := by
    have hBlocks :
        ∀ᵐ x ∂ν,
          |gStar (μexp := μexp) (Y := Y) x
            - gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x|
          ≤ δ :=
      gStar_approx_sum_blocks_of_ApproxWellSpecifiedAE
        (ν := ν) (μexp := μexp) (Y := Y) (blk := blk) (β := β) (φ := φ)
        (ε := δ) hspec
    refine hBlocks.mono ?_
    intro x hx
    simpa [abs_sub_comm, hTotalModel x] using hx
  rcases
    paper_sd_total_sequential_consistency_to_approx_target_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hLaw := hLaw) (hW := hW)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotalBounded := hSplitTotalBounded) (hPlugTotal := hPlugTotal)
      (gTrue := gStar (μexp := μexp) (Y := Y))
      (C := C) (δ := δ) (hApprox := hApprox)
      (hBoundS := hBoundS) (hBoundT := hBoundT)
      (hMomS := hMomS) (hMomT := hMomT)
      (hVarS := hVarS) (hVarT := hVarT)
      (hδ := hδ) (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  exact hM m hm

/--
Two-stage approximate link: a flexible oracle score approximates `gStar`, and the model
approximates the oracle. The SD target error is bounded by the combined approximation.
-/
theorem paper_sd_total_sequential_consistency_to_gStar_approx_ae_of_ApproxOracleAE
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (Y : Attr → Ω → ℝ)
    (gFlex : Attr → ℝ)
    (δModel δOracle : ℝ)
    (hApprox :
      ApproxOracleAE (ν := ν)
        (gModel := gTotalΘ (gB := gB) θ0) (gFlex := gFlex) (gStar := gStar (μexp := μexp) (Y := Y))
        δModel δOracle)
    (hSplitTotalBounded :
      ∀ m,
        SplitEvalWeightAssumptionsBounded (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
    (C : ℝ)
    (hBoundS :
      BoundedAE (ν := ν) (s := gTotalΘ (gB := gB) θ0) C)
    (hBoundT :
      BoundedAE (ν := ν) (s := gStar (μexp := μexp) (Y := Y)) C)
    (hMomS :
      AttrMomentAssumptions (ν := ν) (s := gTotalΘ (gB := gB) θ0))
    (hMomT :
      AttrMomentAssumptions (ν := ν) (s := gStar (μexp := μexp) (Y := Y)))
    (hVarS : 0 ≤ attrVar (ν) (gTotalΘ (gB := gB) θ0))
    (hVarT : 0 ≤ attrVar (ν) (gStar (μexp := μexp) (Y := Y)))
    (hδModel : 0 ≤ δModel)
    (hδOracle : 0 ≤ δOracle)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        |attrSD (ν) (gTotalΘ (gB := gB) θ0)
            - attrSD (ν) (gStar (μexp := μexp) (Y := Y))|
          ≤ Real.sqrt (4 * C * (δModel + δOracle)) := by
  rcases hApprox with ⟨hApproxModel, hApproxOracle⟩
  have hApproxCombined :
      ApproxInvarianceAE
        (ν := ν)
        (s := gTotalΘ (gB := gB) θ0)
        (t := gStar (μexp := μexp) (Y := Y))
        (δModel + δOracle) := by
    exact
      approxInvarianceAE_triangle
        (ν := ν)
        (s := gTotalΘ (gB := gB) θ0) (t := gFlex) (u := gStar (μexp := μexp) (Y := Y))
        (ε₁ := δModel) (ε₂ := δOracle)
        hApproxModel hApproxOracle
  have hδ : 0 ≤ δModel + δOracle := add_nonneg hδModel hδOracle
  rcases
    paper_sd_total_sequential_consistency_to_approx_target_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hLaw := hLaw) (hW := hW)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotalBounded := hSplitTotalBounded) (hPlugTotal := hPlugTotal)
      (gTrue := gStar (μexp := μexp) (Y := Y))
      (C := C) (δ := δModel + δOracle) (hApprox := hApproxCombined)
      (hBoundS := hBoundS) (hBoundT := hBoundT)
      (hMomS := hMomS) (hMomT := hMomT)
      (hVarS := hVarS) (hVarT := hVarT)
      (hδ := hδ) (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  exact hM m hm

end SDSequentialConsistency

end ConjointSD
