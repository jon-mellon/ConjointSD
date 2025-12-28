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
import ConjointSD.ModelBridge
import ConjointSD.Transport
import ConjointSD.DecompositionSequentialConsistency
import ConjointSD.TargetEquivalence
import ConjointSD.DeriveGEstimationAssumptions

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

end SDSequentialConsistency

end ConjointSD
