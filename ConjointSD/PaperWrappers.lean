/-
ConjointSD/PaperWrappers.lean

A “paper-facing” wrapper layer that exposes the main checked implications in vocabulary
closest to the manuscript:

1) Conjoint identification (conditional means identify potential-outcome means; AMCE as
   difference of observed conditional means).

2) Regression / term model bridge to block decomposition (well-specification implies the
   causal estimand decomposes as a sum of block scores).

3) Route-2 sequential consistency for SDs (via θhat → θ0 + continuity at θ0):
   - per-block SDs are sequentially consistent (single M for all blocks, finite B),
   - total-score SD is sequentially consistent,
   - combined statement (blocks + total) with a single M.

4) “Convergence to the true estimand” is obtained by adding an explicit target-equality
   assumption (typically InvarianceAE / well-specification), plus AE-congruence lemmas
   showing population SDs match when score functions match ν-a.e.
-/

import Mathlib
import ConjointSD.ConjointIdentification
import ConjointSD.StatusConjointDesign
import ConjointSD.ModelBridge
import ConjointSD.Transport
import ConjointSD.DecompositionSequentialConsistency
import ConjointSD.TargetEquivalence
import ConjointSD.DeriveGEstimationAssumptions
import ConjointSD.WellSpecifiedFromNoInteractions

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/-!
## 1) Conjoint identification wrappers
-/

section Identification

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {Attr : Type*} [MeasurableSpace Attr]
variable (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)

/-- Identification: observed conditional mean among `X = x0` equals the potential-outcome mean. -/
theorem paper_identifies_potMean_from_condMean
    (h : ConjointIdAssumptions (μ := μ) X Y Yobs)
    (x0 : Attr) :
    condMean (μ := μ) Yobs (eventX (X := X) x0) = potMean (μ := μ) Y x0 :=
  identified_potMean_from_condMean (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) h x0

/-- Identification: AMCE equals a difference of observed conditional means. -/
theorem paper_identifies_amce_from_condMeans
    (h : ConjointIdAssumptions (μ := μ) X Y Yobs)
    (x x' : Attr) :
    (condMean (μ := μ) Yobs (eventX (X := X) x')
      - condMean (μ := μ) Yobs (eventX (X := X) x))
      =
    amce (μ := μ) Y x x' :=
  identified_amce_from_condMeans (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) h x x'

end Identification

/-!
## 1b) Status-conjoint identification wrappers
-/

section StatusIdentification

variable {Respondent : Type u} [MeasurableSpace Respondent]
variable (μResp : Measure Respondent) [IsProbabilityMeasure μResp]
variable (Yresp : StatusProfile → Respondent → TaskSlot → ℝ)

/-- Identification for the concrete status conjoint: conditional mean equals potential mean. -/
theorem paper_identifies_potMean_from_condMean_status
    (hmeas :
      ∀ p, Measurable (fun rt : Respondent × TaskSlot => Yresp p rt.fst rt.snd))
    (hmeasObs : Measurable (statusYobs (Yresp := Yresp)))
    (hbound : ∀ p r t, |Yresp p r t| ≤ 100)
    (x0 : StatusProfile) :
    condMean (μ := μStatus (μResp := μResp))
      (statusYobs (Yresp := Yresp)) (eventX (X := statusX) x0)
        =
    potMean (μ := μStatus (μResp := μResp)) (statusY (Yresp := Yresp)) x0 := by
  have h :=
    status_id_assumptions (μResp := μResp) (Yresp := Yresp) hmeas hmeasObs hbound
  exact
    paper_identifies_potMean_from_condMean
      (μ := μStatus (μResp := μResp))
      (X := statusX) (Y := statusY (Yresp := Yresp))
      (Yobs := statusYobs (Yresp := Yresp)) h x0

/-- Identification for the status conjoint: AMCE equals a difference of conditional means. -/
theorem paper_identifies_amce_from_condMeans_status
    (hmeas :
      ∀ p, Measurable (fun rt : Respondent × TaskSlot => Yresp p rt.fst rt.snd))
    (hmeasObs : Measurable (statusYobs (Yresp := Yresp)))
    (hbound : ∀ p r t, |Yresp p r t| ≤ 100)
    (x x' : StatusProfile) :
    (condMean (μ := μStatus (μResp := μResp))
        (statusYobs (Yresp := Yresp)) (eventX (X := statusX) x')
      -
      condMean (μ := μStatus (μResp := μResp))
        (statusYobs (Yresp := Yresp)) (eventX (X := statusX) x))
      =
    amce (μ := μStatus (μResp := μResp)) (statusY (Yresp := Yresp)) x x' := by
  have h :=
    status_id_assumptions (μResp := μResp) (Yresp := Yresp) hmeas hmeasObs hbound
  exact
    paper_identifies_amce_from_condMeans
      (μ := μStatus (μResp := μResp))
      (X := statusX) (Y := statusY (Yresp := Yresp))
      (Yobs := statusYobs (Yresp := Yresp)) h x x'

end StatusIdentification

/-!
## 2) Regression/terms-to-block decomposition wrapper
-/

section ModelToBlocks

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*}
variable {B : Type*} [Fintype B]
variable {Term : Type*} [Fintype Term] [DecidableEq B]

variable (μ : Measure Ω)
variable (Y : Attr → Ω → ℝ)
variable (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)

/--
If the causal estimand is well-specified by a linear-in-terms model, it decomposes
as the sum of block scores induced by `blk`.
-/
theorem paper_gStar_eq_sum_blocks_of_WellSpecified
    (hspec : WellSpecified (μ := μ) (Y := Y) (β := β) (φ := φ)) :
    gStar (μ := μ) (Y := Y)
      =
    gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
  gStar_eq_sum_blocks_of_WellSpecified
    (μ := μ) (Y := Y) (blk := blk) (β := β) (φ := φ) hspec

end ModelToBlocks

/-!
## 3) Route-2 sequential SD consistency wrappers (blocks + total)
-/

section SDSequentialConsistency

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*} [TopologicalSpace Θ]
variable {B : Type*} [Fintype B]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (A : ℕ → Ω → Attr)

variable (ν : Measure Attr) [IsProbabilityMeasure ν]

variable (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

/-- Paper-facing: per-block SDs are sequentially consistent (single `M` works for all blocks). -/
theorem paper_sd_blocks_sequential_consistency_ae
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplit : ∀ m b,
      SplitEvalAssumptions (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B, FunctionalContinuityAssumptions (ν := ν) (g := gBlock (gB := gB) b) θ0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  have hG :
      ∀ b : B,
        GEstimationAssumptions (ν := ν) (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat) :=
    fun b =>
      derive_hG (ν := ν) (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat) hθ (hCont b)
  exact
    sequential_consistency_blocks_ae
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hG := hG)
      (ε := ε) (hε := hε)

theorem paper_sd_blocks_sequential_consistency_ae_of_bounded
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplit : ∀ m b,
      SplitEvalAssumptionsBounded
        (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B, FunctionalContinuityAssumptions (ν := ν) (g := gBlock (gB := gB) b) θ0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  have hG :
      ∀ b : B,
        GEstimationAssumptions (ν := ν) (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat) :=
    fun b =>
      derive_hG (ν := ν) (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat) hθ (hCont b)
  exact
    sequential_consistency_blocks_ae_of_bounded
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hG := hG)
      (ε := ε) (hε := hε)

/-- Paper-facing: total-score SD is sequentially consistent. -/
theorem paper_sd_total_sequential_consistency_ae
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  have hGTotal :
      GEstimationAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat) :=
    derive_hG (ν := ν) (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat) hθ hContTotal
  exact
    sequential_consistency_total_ae
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hGTotal := hGTotal)
      (ε := ε) (hε := hε)

theorem paper_sd_total_sequential_consistency_ae_of_bounded
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptionsBounded
          (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  have hGTotal :
      GEstimationAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat) :=
    derive_hG (ν := ν) (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat) hθ hContTotal
  exact
    sequential_consistency_total_ae_of_bounded
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hGTotal := hGTotal)
      (ε := ε) (hε := hε)

/--
Combined paper-facing statement: for any ε>0, a single `M` works so that for all `m ≥ M`,
(1) all block SD errors are < ε eventually in `n` (a.e. ω), and
(2) the total-score SD error is < ε eventually in `n` (a.e. ω).
-/
theorem paper_sd_blocks_and_total_sequential_consistency_ae
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplit : ∀ m b,
      SplitEvalAssumptions (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B, FunctionalContinuityAssumptions (ν := ν) (g := gBlock (gB := gB) b) θ0)
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε))
        ∧
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  rcases paper_sd_blocks_sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplit := hSplit) (hθ := hθ) (hCont := hCont) (ε := ε) (hε := hε)
      with ⟨Mb, hMb⟩
  rcases paper_sd_total_sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)
      with ⟨Mt, hMt⟩
  let M : ℕ := Nat.max Mb Mt
  refine ⟨M, ?_⟩
  intro m hm
  have hmb : m ≥ Mb := le_trans (Nat.le_max_left Mb Mt) hm
  have hmt : m ≥ Mt := le_trans (Nat.le_max_right Mb Mt) hm
  refine ⟨?_, ?_⟩
  · intro b
    exact hMb m hmb b
  · exact hMt m hmt

theorem paper_sd_blocks_and_total_sequential_consistency_ae_of_bounded
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplit : ∀ m b,
      SplitEvalAssumptionsBounded
        (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptionsBounded
          (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B, FunctionalContinuityAssumptions (ν := ν) (g := gBlock (gB := gB) b) θ0)
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε))
        ∧
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  rcases paper_sd_blocks_sequential_consistency_ae_of_bounded
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplit := hSplit) (hθ := hθ) (hCont := hCont) (ε := ε) (hε := hε)
      with ⟨Mb, hMb⟩
  rcases paper_sd_total_sequential_consistency_ae_of_bounded
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)
      with ⟨Mt, hMt⟩
  let M : ℕ := Nat.max Mb Mt
  refine ⟨M, ?_⟩
  intro m hm
  have hmb : m ≥ Mb := le_trans (Nat.le_max_left Mb Mt) hm
  have hmt : m ≥ Mt := le_trans (Nat.le_max_right Mb Mt) hm
  refine ⟨?_, ?_⟩
  · intro b
    exact hMb m hmb b
  · exact hMt m hmt

/-!
## 4) Turn “converges to popSDAttr ν (g θ0)” into “converges to the true SD target”
by assuming ν-a.e. equality to a declared true score function and using congruence lemmas.
-/

/--
Blocks: sequential consistency + ν-a.e. target equality packages convergence to the true block SD.
-/
theorem paper_sd_blocks_sequential_consistency_to_true_target_ae
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplit : ∀ m b,
      SplitEvalAssumptions (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B, FunctionalContinuityAssumptions (ν := ν) (g := gBlock (gB := gB) b) θ0)
    (gTrueB : B → Attr → ℝ)
    (hTrueB : ∀ b : B, InvarianceAE (ν := ν) (gBlock (gB := gB) b θ0) (gTrueB b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε)
          ∧
          popSDAttr ν (gBlock (gB := gB) b θ0) = popSDAttr ν (gTrueB b) := by
  rcases paper_sd_blocks_sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplit := hSplit) (hθ := hθ) (hCont := hCont) (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  have hCons := hM m hm b
  have hEq :
      popSDAttr ν (gBlock (gB := gB) b θ0) = popSDAttr ν (gTrueB b) :=
    popSDAttr_congr_ae (ν := ν) (s := gBlock (gB := gB) b θ0) (t := gTrueB b) (hTrueB b)
  exact ⟨hCons, hEq⟩

/-!
## 4b) Approximate targets: carry an explicit misspecification bound
-/

/--
Blocks: sequential consistency + ν-a.e. ε-approximation yields convergence with an SD bound.
-/
theorem paper_sd_blocks_sequential_consistency_to_approx_target_ae
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplit : ∀ m b,
      SplitEvalAssumptions (μ := μ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B, FunctionalContinuityAssumptions (ν := ν) (g := gBlock (gB := gB) b) θ0)
    (gTrueB : B → Attr → ℝ)
    (C δ : ℝ)
    (hApprox :
      ∀ b : B,
        ApproxInvarianceAE (ν := ν) (s := gBlock (gB := gB) b θ0) (t := gTrueB b) δ)
    (hBoundS :
      ∀ b : B, BoundedAE (ν := ν) (s := gBlock (gB := gB) b θ0) C)
    (hBoundT :
      ∀ b : B, BoundedAE (ν := ν) (s := gTrueB b) C)
    (hMomS :
      ∀ b : B, PopulationMomentAssumptions (ν := ν) (s := gBlock (gB := gB) b θ0))
    (hMomT : ∀ b : B, PopulationMomentAssumptions (ν := ν) (s := gTrueB b))
    (hVarS : ∀ b : B, 0 ≤ popVarAttr ν (gBlock (gB := gB) b θ0))
    (hVarT : ∀ b : B, 0 ≤ popVarAttr ν (gTrueB b))
    (hδ : 0 ≤ δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂μ,
            ∀ᶠ n : ℕ in atTop,
              totalErr μ A ν (gBlock (gB := gB) b) θ0 θhat m n ω < ε)
          ∧
          |popSDAttr ν (gBlock (gB := gB) b θ0) - popSDAttr ν (gTrueB b)|
            ≤ Real.sqrt (4 * C * δ) := by
  rcases paper_sd_blocks_sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplit := hSplit) (hθ := hθ) (hCont := hCont)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  have hCons := hM m hm b
  have hEq :
      |popSDAttr ν (gBlock (gB := gB) b θ0) - popSDAttr ν (gTrueB b)|
        ≤ Real.sqrt (4 * C * δ) :=
    popSDAttr_diff_le_of_approx_ae
      (ν := ν) (s := gBlock (gB := gB) b θ0) (t := gTrueB b)
      (hs := hMomS b) (ht := hMomT b)
      (hBoundS := hBoundS b) (hBoundT := hBoundT b)
      (hApprox := hApprox b) (hε := hδ)
      (hVarS := hVarS b) (hVarT := hVarT b)
  exact ⟨hCons, hEq⟩

/- Total-score: sequential consistency + ν-a.e. ε-approximation yields convergence with
an SD bound. -/
theorem paper_sd_total_sequential_consistency_to_approx_target_ae
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (gTrue : Attr → ℝ)
    (C δ : ℝ)
    (hApprox :
      ApproxInvarianceAE (ν := ν) (s := gTotalΘ (gB := gB) θ0) (t := gTrue) δ)
    (hBoundS : BoundedAE (ν := ν) (s := gTotalΘ (gB := gB) θ0) C)
    (hBoundT : BoundedAE (ν := ν) (s := gTrue) C)
    (hMomS : PopulationMomentAssumptions (ν := ν) (s := gTotalΘ (gB := gB) θ0))
    (hMomT : PopulationMomentAssumptions (ν := ν) (s := gTrue))
    (hVarS : 0 ≤ popVarAttr ν (gTotalΘ (gB := gB) θ0))
    (hVarT : 0 ≤ popVarAttr ν gTrue)
    (hδ : 0 ≤ δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        |popSDAttr ν (gTotalΘ (gB := gB) θ0) - popSDAttr ν gTrue|
          ≤ Real.sqrt (4 * C * δ) := by
  rcases paper_sd_total_sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hCons := hM m hm
  have hEq :
      |popSDAttr ν (gTotalΘ (gB := gB) θ0) - popSDAttr ν gTrue|
        ≤ Real.sqrt (4 * C * δ) :=
    popSDAttr_diff_le_of_approx_ae
      (ν := ν) (s := gTotalΘ (gB := gB) θ0) (t := gTrue)
      (hs := hMomS) (ht := hMomT)
      (hBoundS := hBoundS) (hBoundT := hBoundT)
      (hApprox := hApprox) (hε := hδ)
      (hVarS := hVarS) (hVarT := hVarT)
  exact ⟨hCons, hEq⟩

/--
Total-score: sequential consistency + ν-a.e. target equality packages convergence to the true SD.
-/
theorem paper_sd_total_sequential_consistency_to_true_target_ae
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (gTrue : Attr → ℝ)
    (hTrue : InvarianceAE (ν := ν) (gTotalΘ (gB := gB) θ0) gTrue)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        popSDAttr ν (gTotalΘ (gB := gB) θ0) = popSDAttr ν gTrue := by
  rcases paper_sd_total_sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hCons := hM m hm
  have hEq :
      popSDAttr ν (gTotalΘ (gB := gB) θ0) = popSDAttr ν gTrue :=
    popSDAttr_congr_ae (ν := ν) (s := gTotalΘ (gB := gB) θ0) (t := gTrue) hTrue
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
    (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hTotalModel :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x)
    (hspec :
      ApproxWellSpecifiedAE (ν := ν) (μ := μ) (Y := Y) (β := β) (φ := φ) δ)
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (C : ℝ)
    (hBoundS : BoundedAE (ν := ν) (s := gTotalΘ (gB := gB) θ0) C)
    (hBoundT : BoundedAE (ν := ν) (s := gStar (μ := μ) (Y := Y)) C)
    (hMomS : PopulationMomentAssumptions (ν := ν) (s := gTotalΘ (gB := gB) θ0))
    (hMomT : PopulationMomentAssumptions (ν := ν) (s := gStar (μ := μ) (Y := Y)))
    (hVarS : 0 ≤ popVarAttr ν (gTotalΘ (gB := gB) θ0))
    (hVarT : 0 ≤ popVarAttr ν (gStar (μ := μ) (Y := Y)))
    (hδ : 0 ≤ δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        |popSDAttr ν (gTotalΘ (gB := gB) θ0)
            - popSDAttr ν (gStar (μ := μ) (Y := Y))|
          ≤ Real.sqrt (4 * C * δ) := by
  have hApprox :
      ApproxInvarianceAE
        (ν := ν)
        (s := gTotalΘ (gB := gB) θ0)
        (t := gStar (μ := μ) (Y := Y))
        δ := by
    have hBlocks :
        ∀ᵐ x ∂ν,
          |gStar (μ := μ) (Y := Y) x
            - gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x|
          ≤ δ :=
      gStar_approx_sum_blocks_of_ApproxWellSpecifiedAE
        (ν := ν) (μ := μ) (Y := Y) (blk := blk) (β := β) (φ := φ)
        (ε := δ) hspec
    refine hBlocks.mono ?_
    intro x hx
    simpa [abs_sub_comm, hTotalModel x] using hx
  exact
    paper_sd_total_sequential_consistency_to_approx_target_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (gTrue := gStar (μ := μ) (Y := Y))
      (C := C) (δ := δ) (hApprox := hApprox)
      (hBoundS := hBoundS) (hBoundT := hBoundT)
      (hMomS := hMomS) (hMomT := hMomT)
      (hVarS := hVarS) (hVarT := hVarT)
      (hδ := hδ) (ε := ε) (hε := hε)

/--
Two-stage approximate link: a flexible oracle score approximates `gStar`, and the model
approximates the oracle. The SD target error is bounded by the combined approximation.
-/
theorem paper_sd_total_sequential_consistency_to_gStar_approx_ae_of_ApproxOracleAE
    (Y : Attr → Ω → ℝ)
    (gFlex : Attr → ℝ)
    (δModel δOracle : ℝ)
    (hApprox :
      ApproxOracleAE (ν := ν)
        (gModel := gTotalΘ (gB := gB) θ0) (gFlex := gFlex) (gStar := gStar (μ := μ) (Y := Y))
        δModel δOracle)
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (C : ℝ)
    (hBoundS : BoundedAE (ν := ν) (s := gTotalΘ (gB := gB) θ0) C)
    (hBoundT : BoundedAE (ν := ν) (s := gStar (μ := μ) (Y := Y)) C)
    (hMomS : PopulationMomentAssumptions (ν := ν) (s := gTotalΘ (gB := gB) θ0))
    (hMomT : PopulationMomentAssumptions (ν := ν) (s := gStar (μ := μ) (Y := Y)))
    (hVarS : 0 ≤ popVarAttr ν (gTotalΘ (gB := gB) θ0))
    (hVarT : 0 ≤ popVarAttr ν (gStar (μ := μ) (Y := Y)))
    (hδModel : 0 ≤ δModel)
    (hδOracle : 0 ≤ δOracle)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        |popSDAttr ν (gTotalΘ (gB := gB) θ0)
            - popSDAttr ν (gStar (μ := μ) (Y := Y))|
          ≤ Real.sqrt (4 * C * (δModel + δOracle)) := by
  rcases hApprox with ⟨hApproxModel, hApproxOracle⟩
  have hApproxCombined :
      ApproxInvarianceAE
        (ν := ν)
        (s := gTotalΘ (gB := gB) θ0)
        (t := gStar (μ := μ) (Y := Y))
        (δModel + δOracle) := by
    exact
      approxInvarianceAE_triangle
        (ν := ν) (s := gTotalΘ (gB := gB) θ0) (t := gFlex) (u := gStar (μ := μ) (Y := Y))
        (ε₁ := δModel) (ε₂ := δOracle)
        hApproxModel hApproxOracle
  have hδ : 0 ≤ δModel + δOracle := add_nonneg hδModel hδOracle
  exact
    paper_sd_total_sequential_consistency_to_approx_target_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (gTrue := gStar (μ := μ) (Y := Y))
      (C := C) (δ := δModel + δOracle) (hApprox := hApproxCombined)
      (hBoundS := hBoundS) (hBoundT := hBoundT)
      (hMomS := hMomS) (hMomT := hMomT)
      (hVarS := hVarS) (hVarT := hVarT)
      (hδ := hδ) (ε := ε) (hε := hε)

/--
If the model-based total score at `θ0` equals the block-sum from a linear model and that
linear model is well-specified for `gStar`, then sequential consistency targets `gStar`.

This is the explicit bridge from well-specification (or “no interactions” via
`wellSpecified_of_noInteractions`) into the SD-consistency chain.
-/
theorem paper_sd_total_sequential_consistency_to_gStar_ae_of_WellSpecified
    {Term : Type*} [Fintype Term] [DecidableEq B]
    (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hTotalModel :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x)
    (hspec : WellSpecified (μ := μ) (Y := Y) (β := β) (φ := φ))
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        popSDAttr ν (gTotalΘ (gB := gB) θ0) = popSDAttr ν (gStar (μ := μ) (Y := Y)) := by
  have hBlocks :
      gStar (μ := μ) (Y := Y)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gStar_eq_sum_blocks_of_WellSpecified
      (μ := μ) (Y := Y) (blk := blk) (β := β) (φ := φ) hspec
  have hStar :
      InvarianceAE
        (ν := ν)
        (gTotalΘ (gB := gB) θ0)
        (gStar (μ := μ) (Y := Y)) := by
    refine ae_of_all _ ?_
    intro x
    have hBlocksx :
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x
          =
        gStar (μ := μ) (Y := Y) x := by
      simpa using congrArg (fun f => f x) hBlocks.symm
    simpa [hBlocksx] using hTotalModel x
  rcases paper_sd_total_sequential_consistency_to_true_target_ae
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (gTrue := gStar (μ := μ) (Y := Y)) (hTrue := hStar) (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  exact ⟨M, hM⟩

end SDSequentialConsistency

section SDSequentialConsistencyNoTopo

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*} [TopologicalSpace Θ]
variable {B : Type*} [Fintype B]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (A : ℕ → Ω → Attr)

variable (ν : Measure Attr) [IsProbabilityMeasure ν]

variable (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

omit [TopologicalSpace Θ] in
theorem paper_sd_total_sequential_consistency_ae_of_hGTotal
    (hLaw : Measure.map (A 0) μ = ν)
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
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) :=
  sequential_consistency_total_ae
    (μ := μ) (A := A) (ν := ν) (hLaw := hLaw)
    (gB := gB) (θ0 := θ0) (θhat := θhat)
    (hSplitTotal := hSplitTotal) (hGTotal := hGTotal)
    (ε := ε) (hε := hε)

omit [TopologicalSpace Θ] in
theorem paper_sd_total_sequential_consistency_to_true_target_ae_of_hGTotal
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hGTotal :
      GEstimationAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
    (gTrue : Attr → ℝ)
    (hTrue : InvarianceAE (ν := ν) (gTotalΘ (gB := gB) θ0) gTrue)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        popSDAttr ν (gTotalΘ (gB := gB) θ0) = popSDAttr ν gTrue := by
  rcases paper_sd_total_sequential_consistency_ae_of_hGTotal
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hGTotal := hGTotal)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hCons := hM m hm
  have hEq :
      popSDAttr ν (gTotalΘ (gB := gB) θ0) = popSDAttr ν gTrue :=
    popSDAttr_congr_ae (ν := ν) (s := gTotalΘ (gB := gB) θ0) (t := gTrue) hTrue
  exact ⟨hCons, hEq⟩

omit [TopologicalSpace Θ] in
theorem paper_sd_total_sequential_consistency_to_gStar_ae_of_WellSpecified_of_hGTotal
    {Term : Type*} [Fintype Term] [DecidableEq B]
    (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hTotalModel :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x)
    (hspec : WellSpecified (μ := μ) (Y := Y) (β := β) (φ := φ))
    (hLaw : Measure.map (A 0) μ = ν)
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
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        popSDAttr ν (gTotalΘ (gB := gB) θ0) = popSDAttr ν (gStar (μ := μ) (Y := Y)) := by
  have hBlocks :
      gStar (μ := μ) (Y := Y)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gStar_eq_sum_blocks_of_WellSpecified
      (μ := μ) (Y := Y) (blk := blk) (β := β) (φ := φ) hspec
  have hStar :
      InvarianceAE
        (ν := ν)
        (gTotalΘ (gB := gB) θ0)
        (gStar (μ := μ) (Y := Y)) := by
    refine ae_of_all _ ?_
    intro x
    have hBlocksx :
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x
          =
        gStar (μ := μ) (Y := Y) x := by
      simpa using congrArg (fun f => f x) hBlocks.symm
    simpa [hBlocksx] using hTotalModel x
  rcases paper_sd_total_sequential_consistency_to_true_target_ae_of_hGTotal
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hGTotal := hGTotal)
      (gTrue := gStar (μ := μ) (Y := Y)) (hTrue := hStar)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  exact ⟨M, hM⟩

end SDSequentialConsistencyNoTopo

/-!
## 4d) No-interactions corollary (via `wellSpecified_of_noInteractions`)
-/

section NoInteractionsCorollary

variable {Ω : Type*} [MeasurableSpace Ω]
variable {K : Type*} {V : K → Type*} [Fintype K]
variable [∀ k : K, MeasurableSpace (V k)]
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {Θ : Type*} [TopologicalSpace Θ]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (A : ℕ → Ω → Profile K V)
variable (ν : Measure (Profile K V)) [IsProbabilityMeasure ν]

variable (gB : B → Θ → Profile K V → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

/--
No-interactions corollary: if `gStar` is additive in attributes, then we can
derive well-specification and plug it into the `gStar` consistency bridge.

`hTotalModel` encodes how the estimation model’s total score at `θ0` matches the
linear-in-terms total score induced by the additive structure.
-/
theorem paper_sd_total_sequential_consistency_to_gStar_ae_of_NoInteractions
    (Y : Profile K V → Ω → ℝ)
    (blk : Term K → B)
    (hNoInt : NoInteractions (K := K) (V := V) (μ := μ) (Y := Y))
    (hTotalModel :
      ∀ (μ0 : ℝ) (main : ∀ k : K, V k → ℝ),
        (∀ x, gStar (μ := μ) (Y := Y) x = μ0 + ∑ k : K, main k (x k)) →
        ∀ x,
          gTotalΘ (gB := gB) θ0 x
            =
          gTotal
            (B := B)
            (g := gBlockTerm
              (blk := blk)
              (β := βMain (K := K) μ0)
              (φ := φMain (K := K) (V := V) main))
            x)
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions (μ := μ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (ν := ν) (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        popSDAttr ν (gTotalΘ (gB := gB) θ0) = popSDAttr ν (gStar (μ := μ) (Y := Y)) := by
  rcases hNoInt with ⟨μ0, main, hadd⟩
  have hspec :
      WellSpecified (Ω := Ω) (Attr := Profile K V) (Term := Term K)
        (μ := μ) (Y := Y) (β := βMain (K := K) μ0) (φ := φMain (K := K) (V := V) main) := by
    intro x
    have hlin :
        gLin (Attr := Profile K V) (Term := Term K)
            (β := βMain (K := K) μ0)
            (φ := φMain (K := K) (V := V) main) x
          =
        μ0 + ∑ k : K, main k (x k) :=
      gLin_eq_additive (K := K) (V := V) μ0 main x
    calc
      gLin (Attr := Profile K V) (Term := Term K)
          (β := βMain (K := K) μ0)
          (φ := φMain (K := K) (V := V) main) x
          =
        μ0 + ∑ k : K, main k (x k) := hlin
      _ = gStar (μ := μ) (Y := Y) x := by
        simpa using (hadd x).symm
  have hTotalModel' :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal
          (B := B)
          (g := gBlockTerm
            (blk := blk)
            (β := βMain (K := K) μ0)
            (φ := φMain (K := K) (V := V) main))
          x :=
    hTotalModel μ0 main hadd
  exact
    paper_sd_total_sequential_consistency_to_gStar_ae_of_WellSpecified
      (μ := μ) (A := A) (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (Y := Y) (blk := blk) (β := βMain (K := K) μ0) (φ := φMain (K := K) (V := V) main)
      (hTotalModel := hTotalModel') (hspec := hspec)
      (hLaw := hLaw) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)

end NoInteractionsCorollary

end ConjointSD
