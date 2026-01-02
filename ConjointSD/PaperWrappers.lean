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
   showing target human population SDs match when score functions match ν-a.e.
-/

import Mathlib
import ConjointSD.ConjointIdentification
import ConjointSD.StatusConjointDesign
import ConjointSD.ModelBridge
import ConjointSD.Assumptions
import ConjointSD.Transport
import ConjointSD.DecompositionSequentialConsistency
import ConjointSD.TargetEquivalence
import ConjointSD.PaperOLSConsistency
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
variable (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
variable {Attr : Type*} [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
variable (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)

/-- Identification: observed conditional mean among `X = x0` equals the potential-outcome mean. -/
theorem paper_identifies_potMean_from_condMean
    (h : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (x0 : Attr)
    (hpos : μexp (eventX (X := X) x0) ≠ 0) :
    condMean (κ := μexp) Yobs (eventX (X := X) x0) = potMean (κ := μexp) Y x0 :=
  identified_potMean_from_condMean (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) h x0 hpos

/-- Identification: AMCE equals a difference of observed conditional means. -/
theorem paper_identifies_amce_from_condMeans
    (h : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (hpos : ∀ x, μexp (eventX (X := X) x) ≠ 0)
    (x x' : Attr) :
    (condMean (κ := μexp) Yobs (eventX (X := X) x')
      - condMean (κ := μexp) Yobs (eventX (X := X) x))
      =
    amce (κ := μexp) Y x x' :=
  identified_amce_from_condMeans (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) h hpos x x'

end Identification

/-!
## 1b) Status-conjoint identification wrappers
-/

section StatusIdentification

variable {Respondent : Type u} [MeasurableSpace Respondent]
variable (μResp : Measure Respondent) [ProbMeasureAssumptions μResp]
variable (Yresp : StatusProfile → Respondent → TaskSlot → ℝ)

/-- Identification for the concrete status conjoint: conditional mean equals potential mean. -/
theorem paper_identifies_potMean_from_condMean_status
    (hmeas :
      ∀ p, Measurable (fun rt : Respondent × TaskSlot => Yresp p rt.fst rt.snd))
    (hmeasObs : Measurable (statusYobs (Yresp := Yresp)))
    (hbound : ∀ p r t, |Yresp p r t| ≤ 100)
    (x0 : StatusProfile) :
    condMean (κ := μStatus (μResp := μResp))
      (statusYobs (Yresp := Yresp)) (eventX (X := statusX) x0)
        =
    potMean (κ := μStatus (μResp := μResp)) (statusY (Yresp := Yresp)) x0 := by
  have h :=
    status_id_randomized (μResp := μResp) (Yresp := Yresp) hmeas hmeasObs hbound
  have hpos := status_event_pos (μResp := μResp)
  exact
    paper_identifies_potMean_from_condMean
      (μexp := μStatus (μResp := μResp))
      (X := statusX) (Y := statusY (Yresp := Yresp))
      (Yobs := statusYobs (Yresp := Yresp)) h x0 (hpos x0)

/-- Identification for the status conjoint: AMCE equals a difference of conditional means. -/
theorem paper_identifies_amce_from_condMeans_status
    (hmeas :
      ∀ p, Measurable (fun rt : Respondent × TaskSlot => Yresp p rt.fst rt.snd))
    (hmeasObs : Measurable (statusYobs (Yresp := Yresp)))
    (hbound : ∀ p r t, |Yresp p r t| ≤ 100)
    (x x' : StatusProfile) :
    (condMean (κ := μStatus (μResp := μResp))
        (statusYobs (Yresp := Yresp)) (eventX (X := statusX) x')
      -
      condMean (κ := μStatus (μResp := μResp))
        (statusYobs (Yresp := Yresp)) (eventX (X := statusX) x))
      =
    amce (κ := μStatus (μResp := μResp)) (statusY (Yresp := Yresp)) x x' := by
  have h :=
    status_id_randomized (μResp := μResp) (Yresp := Yresp) hmeas hmeasObs hbound
  have hpos := status_event_pos (μResp := μResp)
  exact
    paper_identifies_amce_from_condMeans
      (μexp := μStatus (μResp := μResp))
      (X := statusX) (Y := statusY (Yresp := Yresp))
      (Yobs := statusYobs (Yresp := Yresp)) h hpos x x'

end StatusIdentification

/-!
## 2) Regression/terms-to-block decomposition wrapper
-/

section ModelToBlocks

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*}
variable {B : Type*} [Fintype B]
variable {Term : Type*} [Fintype Term] [DecidableEq B]

variable (μexp : Measure Ω)
variable (Y : Attr → Ω → ℝ)
variable (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)

/--
If the causal estimand is well-specified by a linear-in-terms model, it decomposes
as the sum of block scores induced by `blk`.
-/
theorem paper_gStar_eq_sum_blocks_of_WellSpecified
    (hspec : WellSpecified (μexp := μexp) (Y := Y) (β := β) (φ := φ)) :
    gStar (μexp := μexp) (Y := Y)
      =
    gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
  gStar_eq_sum_blocks_of_WellSpecified
    (μexp := μexp) (Y := Y) (blk := blk) (β := β) (φ := φ) hspec

end ModelToBlocks

/-!
## 3) Route-2 sequential SD consistency wrappers (blocks + total)
-/

section SDSequentialConsistency

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*} [TopologicalSpace Θ]
variable {B : Type*} [Fintype B]

variable (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
variable (A : ℕ → Ω → Attr)
variable (ν : Measure Attr) [ProbMeasureAssumptions ν]
variable (w : Attr → ℝ)
variable (w : Attr → ℝ)

variable (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

/-- Paper-facing: per-block SDs are sequentially consistent (single `M` works for all blocks). -/
theorem paper_sd_blocks_sequential_consistency_ae
    (hMom : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hSplit : ∀ m b,
      SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gBlock (gB := gB) b) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A ν w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  exact
    sequential_consistency_blocks_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hMom := hMom) (hθ := hθ) (hCont := hCont)
      (ε := ε) (hε := hε)

theorem paper_sd_blocks_sequential_consistency_ae_of_bounded
    (hPop : DesignAttrIID (κ := ρ) A)
    (hMom : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hSplit : ∀ m b,
      SplitEvalAssumptionsBounded
        (ρ := ρ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hWeight : ScoreAssumptions (κ := ρ) (A := A) (g := w))
    (hWeightScore : ∀ m b,
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * gHat (gBlock (gB := gB) b) θhat m a))
    (hWeightScoreSq : ∀ m b,
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * (gHat (gBlock (gB := gB) b) θhat m a) ^ 2))
    (hW0 : designMeanZ (κ := ρ) (Z := Zcomp (A := A) (g := w)) ≠ 0)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gBlock (gB := gB) b) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A ν w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  exact
    sequential_consistency_blocks_ae_of_bounded
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hPop := hPop)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hWeight := hWeight) (hWeightScore := hWeightScore)
      (hWeightScoreSq := hWeightScoreSq) (hW0 := hW0)
      (hMom := hMom) (hθ := hθ) (hCont := hCont)
      (ε := ε) (hε := hε)

/-- Paper-facing: total-score SD is sequentially consistent. -/
theorem paper_sd_total_sequential_consistency_ae
    (hMom : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A ν w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  exact
    sequential_consistency_total_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hMom := hMom) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)

theorem paper_sd_total_sequential_consistency_ae_of_bounded
    (hPop : DesignAttrIID (κ := ρ) A)
    (hMom : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptionsBounded
          (ρ := ρ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hWeight : ScoreAssumptions (κ := ρ) (A := A) (g := w))
    (hWeightScore : ∀ m,
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * gHat (gTotalΘ (gB := gB)) θhat m a))
    (hWeightScoreSq : ∀ m,
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * (gHat (gTotalΘ (gB := gB)) θhat m a) ^ 2))
    (hW0 : designMeanZ (κ := ρ) (Z := Zcomp (A := A) (g := w)) ≠ 0)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A ν w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  exact
    sequential_consistency_total_ae_of_bounded
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hPop := hPop)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hWeight := hWeight)
      (hWeightScore := hWeightScore) (hWeightScoreSq := hWeightScoreSq) (hW0 := hW0)
      (hMom := hMom) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)

/--
Combined paper-facing statement: for any ε>0, a single `M` works so that for all `m ≥ M`,
(1) all block SD errors are < ε eventually in `n` (a.e. ω), and
(2) the total-score SD error is < ε eventually in `n` (a.e. ω).
-/
theorem paper_sd_blocks_and_total_sequential_consistency_ae
    (hMomBlocks : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hMomTotal : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplit : ∀ m b,
      SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gBlock (gB := gB) b) θ0)
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A ν w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε))
        ∧
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A ν w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  rcases paper_sd_blocks_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomBlocks)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hθ := hθ) (hCont := hCont) (ε := ε) (hε := hε)
      with ⟨Mb, hMb⟩
  rcases paper_sd_total_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomTotal)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
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
    (hPop : DesignAttrIID (κ := ρ) A)
    (hMomBlocks : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hMomTotal : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplit : ∀ m b,
      SplitEvalAssumptionsBounded
        (ρ := ρ) (A := A) (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptionsBounded
          (ρ := ρ) (A := A) (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hWeight : ScoreAssumptions (κ := ρ) (A := A) (g := w))
    (hWeightScore : ∀ m b,
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * gHat (gBlock (gB := gB) b) θhat m a))
    (hWeightScoreSq : ∀ m b,
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * (gHat (gBlock (gB := gB) b) θhat m a) ^ 2))
    (hWeightTotal : ∀ m,
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * gHat (gTotalΘ (gB := gB)) θhat m a))
    (hWeightTotalSq : ∀ m,
      ScoreAssumptions (κ := ρ) (A := A)
        (g := fun a => w a * (gHat (gTotalΘ (gB := gB)) θhat m a) ^ 2))
    (hW0 : designMeanZ (κ := ρ) (Z := Zcomp (A := A) (g := w)) ≠ 0)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gBlock (gB := gB) b) θ0)
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A ν w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε))
        ∧
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A ν w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  rcases paper_sd_blocks_sequential_consistency_ae_of_bounded
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomBlocks)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hPop := hPop) (hSplit := hSplit) (hWeight := hWeight)
      (hWeightScore := hWeightScore) (hWeightScoreSq := hWeightScoreSq) (hW0 := hW0)
      (hθ := hθ) (hCont := hCont) (ε := ε) (hε := hε)
      with ⟨Mb, hMb⟩
  rcases paper_sd_total_sequential_consistency_ae_of_bounded
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomTotal)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hPop := hPop) (hSplitTotal := hSplitTotal) (hWeight := hWeight)
      (hWeightScore := hWeightTotal) (hWeightScoreSq := hWeightTotalSq) (hW0 := hW0)
      (hθ := hθ) (hContTotal := hContTotal)
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
## 4) Turn “converges to attrSD ν (g θ0)” into “converges to the true SD target”
by assuming ν-a.e. equality to a declared true score function and using congruence lemmas.
-/

/--
Blocks: sequential consistency + ν-a.e. target equality packages convergence to the true block SD.
-/
theorem paper_sd_blocks_sequential_consistency_to_true_target_ae
    (hMom : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hSplit : ∀ m b,
      SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gBlock (gB := gB) b) θ0)
    (gTrueB : B → Attr → ℝ)
    (hTrueB :
      ∀ b : B,
        InvarianceAE (ν := ν)
          (gBlock (gB := gB) b θ0) (gTrueB b))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A (ν) w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε)
          ∧
          attrSD (ν) (gBlock (gB := gB) b θ0)
            = attrSD (ν) (gTrueB b) := by
  rcases paper_sd_blocks_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMom)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hθ := hθ) (hCont := hCont) (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  have hCons := hM m hm b
  have hEq :
      attrSD (ν) (gBlock (gB := gB) b θ0)
        = attrSD (ν) (gTrueB b) :=
    attrSD_congr_ae
      (ν := ν)
      (s := gBlock (gB := gB) b θ0) (t := gTrueB b) (hTrueB b)
  exact ⟨hCons, hEq⟩

/-!
## 4b) Approximate targets: carry an explicit misspecification bound
-/

/--
Blocks: sequential consistency + ν-a.e. ε-approximation yields convergence with an SD bound.
-/
theorem paper_sd_blocks_sequential_consistency_to_approx_target_ae
    (hMom : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hSplit : ∀ m b,
      SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gBlock (gB := gB) b) θ0)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMom)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hθ := hθ) (hCont := hCont)
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
    (hMom : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMom)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
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

/--
Total-score: sequential consistency + ν-a.e. target equality packages convergence to the true SD.
-/
theorem paper_sd_total_sequential_consistency_to_true_target_ae
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (gTrue : Attr → ℝ)
    (hTrue :
      InvarianceAE (ν := ν) (gTotalΘ (gB := gB) θ0) gTrue)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        attrSD (ν) (gTotalΘ (gB := gB) θ0)
          = attrSD (ν) gTrue := by
  rcases paper_sd_total_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomEval)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hCons := hM m hm
  have hEq :
      attrSD (ν) (gTotalΘ (gB := gB) θ0)
        = attrSD (ν) gTrue :=
    attrSD_congr_ae
      (ν := ν) (s := gTotalΘ (gB := gB) θ0) (t := gTrue) hTrue
  exact ⟨hCons, hEq⟩

theorem paper_sd_total_sequential_consistency_to_gPot_ae_of_identification
    [MeasurableSingletonClass Attr]
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (hId : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (hpos : ∀ x, μexp (eventX (X := X) x) ≠ 0)
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (hExp :
      InvarianceAE
        (ν := ν)
        (gTotalΘ (gB := gB) θ0)
        (gExp (μexp := μexp) (X := X) (Yobs := Yobs)))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        attrSD (ν) (gTotalΘ (gB := gB) θ0)
          =
        attrSD (ν) (gPot (μexp := μexp) (Y := Y)) := by
  rcases paper_sd_total_sequential_consistency_to_true_target_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMomEval := hMomEval)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (gTrue := gExp (μexp := μexp) (X := X) (Yobs := Yobs))
      (hTrue := hExp) (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  rcases hM m hm with ⟨hCons, hEqExp⟩
  have hEq : gExp (μexp := μexp) (X := X) (Yobs := Yobs) = gPot (μexp := μexp) (Y := Y) :=
    gExp_eq_gPot (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) hId hpos
  have hEqAE :
      ∀ᵐ a ∂ν,
        gExp (μexp := μexp) (X := X) (Yobs := Yobs) a
          =
        gPot (μexp := μexp) (Y := Y) a := by
    refine ae_of_all _ ?_
    intro a
    simpa [hEq]
  have hEqPot :
      attrSD (ν) (gExp (μexp := μexp) (X := X) (Yobs := Yobs))
        =
      attrSD (ν) (gPot (μexp := μexp) (Y := Y)) :=
    attrSD_congr_ae (ν := ν)
      (s := gExp (μexp := μexp) (X := X) (Yobs := Yobs))
      (t := gPot (μexp := μexp) (Y := Y)) hEqAE
  exact ⟨hCons, hEqExp.trans hEqPot⟩

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
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hTotalModel :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x)
    (hspec :
      ApproxWellSpecifiedAE (ν := ν) (μexp := μexp) (Y := Y) (β := β) (φ := φ) δ)
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomEval)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
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
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (Y : Attr → Ω → ℝ)
    (gFlex : Attr → ℝ)
    (δModel δOracle : ℝ)
    (hApprox :
      ApproxOracleAE (ν := ν)
        (gModel := gTotalΘ (gB := gB) θ0) (gFlex := gFlex) (gStar := gStar (μexp := μexp) (Y := Y))
        δModel δOracle)
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomEval)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
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

/--
If the model-based total score at `θ0` equals the block-sum from a linear model and that
linear model is well-specified for `gStar`, then sequential consistency targets `gStar`.

This is the explicit bridge from well-specification (or “no interactions” via
`wellSpecified_of_noInteractions`) into the SD-consistency chain.
-/
theorem paper_sd_total_sequential_consistency_to_gStar_ae_of_WellSpecified
    {Term : Type*} [Fintype Term] [DecidableEq B]
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hTotalModel :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x)
    (hspec : WellSpecified (μexp := μexp) (Y := Y) (β := β) (φ := φ))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        attrSD (ν) (gTotalΘ (gB := gB) θ0) =
          attrSD (ν) (gStar (μexp := μexp) (Y := Y)) := by
  have hBlocks :
      gStar (μexp := μexp) (Y := Y)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gStar_eq_sum_blocks_of_WellSpecified
      (μexp := μexp) (Y := Y) (blk := blk) (β := β) (φ := φ) hspec
  have hStar :
      InvarianceAE
        (ν := ν)
        (gTotalΘ (gB := gB) θ0)
        (gStar (μexp := μexp) (Y := Y)) := by
    refine ae_of_all _ ?_
    intro x
    have hBlocksx :
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x
          =
        gStar (μexp := μexp) (Y := Y) x := by
      simpa using congrArg (fun f => f x) hBlocks.symm
    simpa [hBlocksx] using hTotalModel x
  rcases paper_sd_total_sequential_consistency_to_true_target_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMomEval := hMomEval)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (gTrue := gStar (μexp := μexp) (Y := Y)) (hTrue := hStar)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  rcases hM m hm with ⟨hCons, hEq⟩
  exact ⟨hCons, hEq⟩

end SDSequentialConsistency

section SDSequentialConsistencyOLSNoInteractions

variable {Ω : Type*} [MeasurableSpace Ω]
variable {K : Type*} {V : K → Type*} [Fintype K]
variable [∀ k : K, MeasurableSpace (V k)]
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable {B : Type*} [Fintype B] [DecidableEq B]
variable [DecidableEq (PaperTerm Main Inter)]

variable (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
variable (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
variable (Aeval : ℕ → Ω → Profile K V)

variable (ν : Measure (Profile K V)) [ProbMeasureAssumptions ν]
variable (w : Profile K V → ℝ)

variable (Y : Profile K V → Ω → ℝ)
variable (fMain : Main → Profile K V → ℝ) (fInter : Inter → Profile K V → ℝ)
variable (blk : PaperTerm Main Inter → B)

theorem paper_sd_total_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization
    (Atrain : ℕ → Ω → Profile K V) (Yobs : ℕ → Ω → ℝ)
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Atrain) (Y := Y))
    (hMomTotal : ∀ ω m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := Aeval) (ν := ν)
        (w := w)
        (s := gHat
          (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
          (fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n) m))
    (hSplitTotal :
      ∀ ω m,
        SplitEvalWeightAssumptions
          (ρ := ρ) (A := Aeval) (w := w)
          (g := gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
          (θhat := fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n) m)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Atrain) (Y := Y) (Yobs := Yobs)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Atrain)) (fMain := fMain) (fInter := fInter))
    (hTerms :
      FullMainEffectsTerms (K := K) (V := V) (Term := PaperTerm Main Inter)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)))
    (hNoInt : NoInteractions (K := K) (V := V) (μexp := μexp) (Y := Y))
    (gTrue : Profile K V → ℝ)
    (hInv :
      InvarianceAE (ν := ν) (gStar (μexp := μexp) (Y := Y)) gTrue)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ θ0 : PaperTerm Main Inter → ℝ,
      ∀ᵐ ω ∂μexp,
        ∃ M : ℕ,
          ∀ m ≥ M,
            (∀ᵐ ω' ∂ρ,
              ∀ᶠ n : ℕ in atTop,
                totalErr ρ Aeval (ν) w
                  (gTotalΘ
                    (gB := fun b θ a =>
                      gBlockTerm (blk := blk) (β := θ)
                        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
                  θ0
                  (fun n =>
                    olsThetaHat
                      (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
                      (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
                  n)
                  m n ω' < ε)
            ∧
            attrSD (ν)
                (gTotalΘ
                  (gB := fun b θ a =>
                    gBlockTerm (blk := blk) (β := θ)
                      (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                  θ0)
              =
              attrSD (ν) gTrue := by
  rcases
      wellSpecified_of_noInteractions_of_fullMainEffects
        (K := K) (V := V) (Term := PaperTerm Main Inter)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
        (μexp := μexp) (Y := Y) hTerms hNoInt with
    ⟨θ0, hspec⟩
  have hPop : DesignAttrIID (κ := μexp) Atrain :=
    DesignAttrIID.of_randomization_stream
      (μexp := μexp) (A := Atrain) (Y := Y) hRand
  have hθ :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n)
          atTop
          (nhds θ0) :=
    theta_tendsto_of_paper_ols_design_ae
      (μexp := μexp) (Y := Y)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Atrain) (Yobsω := Yobs)
      hPop hDesign hFull hspec
  have hContTotal :
      FunctionalContinuityAssumptions
        (xiAttr := ν)
        (g := gTotalΘ
          (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
        θ0 :=
    functionalContinuity_gTotalΘ_of_bounded
      (Attr := Profile K V) (Main := Main) (Inter := Inter) (B := B)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := ν) (blk := blk) (θ0 := θ0)
      hDesign.meas_fMain hDesign.meas_fInter
      hDesign.bound_fMain hDesign.bound_fInter
  refine ⟨θ0, ?_⟩
  refine hθ.mono ?_
  intro ω hθω
  have hStarEq :
      ∀ᵐ x ∂ν,
        gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
            θ0 x
          =
        gStar (μexp := μexp) (Y := Y) x := by
    have hBlocks :
        gStar (μexp := μexp) (Y := Y)
          =
        gTotal
          (B := B)
          (g := gBlockTerm (blk := blk) (β := θ0)
            (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) :=
      gStar_eq_sum_blocks_of_WellSpecified
        (μexp := μexp) (Y := Y) (blk := blk) (β := θ0)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) hspec
    refine ae_of_all _ ?_
    intro x
    have hBlocksx :
        gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x
          =
        gStar (μexp := μexp) (Y := Y) x := by
      simpa using congrArg (fun f => f x) hBlocks.symm
    calc
      gTotalΘ
          (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
          θ0 x
          =
          gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x := by
            simp [gTotalΘ, gTotal]
      _ = gStar (μexp := μexp) (Y := Y) x := hBlocksx
  have hTrue :
      InvarianceAE
        (ν := ν)
        (gTotalΘ
          (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
          θ0)
        gTrue := by
    refine (hStarEq.and hInv).mono ?_
    intro x hx
    exact hx.1.trans hx.2
  rcases paper_sd_total_sequential_consistency_to_true_target_ae
      (ρ := ρ) (A := Aeval) (ν := ν) (w := w) (hMomEval := hMomTotal ω)
      (gB := fun b θ a =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
          n)
      (hSplitTotal := hSplitTotal ω)
      (hθ := hθω) (hContTotal := hContTotal)
      (gTrue := gTrue) (hTrue := hTrue)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  exact hM m hm

end SDSequentialConsistencyOLSNoInteractions

section SDSequentialConsistencyNoTopo

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*} [TopologicalSpace Θ]
variable {B : Type*} [Fintype B]

variable (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
variable (A : ℕ → Ω → Attr)
variable (ν : Measure Attr) [ProbMeasureAssumptions ν]
variable (w : Attr → ℝ)

variable (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

theorem paper_sd_total_sequential_consistency_ae_of_hGTotal
    (hMom : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) :=
  by
    simpa using
      (sequential_consistency_total_ae
        (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMom)
        (gB := gB) (θ0 := θ0) (θhat := θhat)
        (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
        (ε := ε) (hε := hε))

section PaperOLSNoTopo

variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable {B : Type*} [Fintype B] [DecidableEq B]
variable [DecidableEq (PaperTerm Main Inter)]

theorem paper_sd_total_sequential_consistency_ae_of_paper_ols_gStar_total
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (Aeval : ℕ → Ω → Attr)
    (Y : Attr → Ω → ℝ) (Atrain : ℕ → Ω → Attr) (Yobs : ℕ → Ω → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (w : Attr → ℝ)
    (hSplitTotal :
      ∀ ω m,
        SplitEvalWeightAssumptions
          (ρ := ρ) (A := Aeval) (w := w)
          (g := gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
          (θhat := fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n) m)
    (hMomEval : ∀ ω m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := Aeval) (ν := ν)
        (w := w)
        (s := gHat
          (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
          (fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n) m))
    (hPop : DesignAttrIID (κ := μexp) Atrain)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Atrain) (Y := Y) (Yobs := Yobs)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Atrain)) (fMain := fMain) (fInter := fInter))
    (hspec :
      WellSpecified
        (μexp := μexp)
        (Y := Y)
        (β := θ0)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∀ᵐ ω ∂μexp,
      ∃ M : ℕ,
        ∀ m ≥ M,
          (∀ᵐ ω' ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ Aeval (ν) w
                (gTotalΘ
                  (gB := fun b θ a =>
                    gBlockTerm (blk := blk) (β := θ)
                      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
                θ0
                (fun n =>
                  olsThetaHat
                    (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
                    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                    n)
                m n ω' < ε)
          ∧
          attrSD (ν)
              (gTotalΘ
                (gB := fun b θ a =>
                  gBlockTerm (blk := blk) (β := θ)
                    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
                θ0)
            =
            attrSD (ν) (gStar (μexp := μexp) (Y := Y)) := by
  have hθ :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n)
          atTop
          (nhds θ0) :=
    theta_tendsto_of_paper_ols_design_ae
      (μexp := μexp) (Y := Y)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Atrain) (Yobsω := Yobs)
      hPop hDesign hFull hspec
  have hContTotal :
      FunctionalContinuityAssumptions
        (xiAttr := ν)
        (g := gTotalΘ
          (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
        θ0 :=
    functionalContinuity_gTotalΘ_of_bounded
      (Attr := Attr) (Main := Main) (Inter := Inter) (B := B)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := ν) (blk := blk) (θ0 := θ0)
      hDesign.meas_fMain hDesign.meas_fInter
      hDesign.bound_fMain hDesign.bound_fInter
  refine hθ.mono ?_
  intro ω hθω
  rcases paper_sd_total_sequential_consistency_ae_of_hGTotal
      (ρ := ρ) (A := Aeval) (ν := ν) (w := w) (hMom := hMomEval ω)
      (gB := fun b θ a =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      (hSplitTotal := hSplitTotal ω)
      (hθ := hθω) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  have hBlocks :
      gStar (μexp := μexp) (Y := Y)
        =
      gTotal
        (B := B)
        (g := gBlockTerm (blk := blk) (β := θ0)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) :=
    gStar_eq_sum_blocks_of_WellSpecified
      (μexp := μexp) (Y := Y) (blk := blk) (β := θ0)
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) hspec
  have hStar :
      InvarianceAE
        (ν := ν)
        (gTotalΘ
          (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
          θ0)
        (gStar (μexp := μexp) (Y := Y)) := by
    refine ae_of_all _ ?_
    intro x
    have hBlocksx :
        gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) x
          =
        gStar (μexp := μexp) (Y := Y) x := by
      simpa using congrArg (fun f => f x) hBlocks.symm
    calc
      gTotalΘ
          (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
          θ0 x
          =
          gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) x := by
            simp [gTotalΘ, gTotal]
      _ = gStar (μexp := μexp) (Y := Y) x := hBlocksx
  have hEq :
      attrSD (ν)
          (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
            θ0)
        =
      attrSD (ν) (gStar (μexp := μexp) (Y := Y)) :=
    attrSD_congr_ae (ν := ν) hStar
  refine ⟨M, ?_⟩
  intro m hm
  exact ⟨hM m hm, hEq⟩

end PaperOLSNoTopo

theorem paper_sd_total_sequential_consistency_to_true_target_ae_of_hGTotal
    (hMom : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (gTrue : Attr → ℝ)
    (hTrue : InvarianceAE (ν := ν) (gTotalΘ (gB := gB) θ0) gTrue)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        attrSD (ν) (gTotalΘ (gB := gB) θ0)
          = attrSD (ν) gTrue := by
  rcases paper_sd_total_sequential_consistency_ae_of_hGTotal
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMom)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hCons := hM m hm
  have hEq :
      attrSD (ν) (gTotalΘ (gB := gB) θ0)
        = attrSD (ν) gTrue :=
    attrSD_congr_ae (ν := ν)
      (s := gTotalΘ (gB := gB) θ0) (t := gTrue) hTrue
  exact ⟨hCons, hEq⟩

theorem paper_sd_total_sequential_consistency_to_gStar_ae_of_WellSpecified_of_hGTotal
    {Term : Type*} [Fintype Term] [DecidableEq B]
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hTotalModel :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x)
    (hspec : WellSpecified (μexp := μexp) (Y := Y) (β := β) (φ := φ))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν) w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        attrSD (ν) (gTotalΘ (gB := gB) θ0) =
          attrSD (ν) (gStar (μexp := μexp) (Y := Y)) := by
  have hBlocks :
      gStar (μexp := μexp) (Y := Y)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gStar_eq_sum_blocks_of_WellSpecified
      (μexp := μexp) (Y := Y) (blk := blk) (β := β) (φ := φ) hspec
  have hStar :
      InvarianceAE
        (ν := ν)
        (gTotalΘ (gB := gB) θ0)
        (gStar (μexp := μexp) (Y := Y)) := by
    refine ae_of_all _ ?_
    intro x
    have hBlocksx :
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x
          =
        gStar (μexp := μexp) (Y := Y) x := by
      simpa using congrArg (fun f => f x) hBlocks.symm
    simpa [hBlocksx] using hTotalModel x
  rcases paper_sd_total_sequential_consistency_to_true_target_ae_of_hGTotal
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomEval)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (gTrue := gStar (μexp := μexp) (Y := Y)) (hTrue := hStar)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  rcases hM m hm with ⟨hCons, hEq⟩
  exact ⟨hCons, hEq⟩


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

variable (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
variable (A : ℕ → Ω → Profile K V)
variable (ν : Measure (Profile K V)) [ProbMeasureAssumptions ν]
variable (w : Profile K V → ℝ)

variable (gB : B → Θ → Profile K V → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

/--
No-interactions corollary: if `gStar` is additive in attributes, then we can
derive well-specification and plug it into the `gStar` consistency bridge.

`hTotalModel` encodes how the estimation model’s total score at `θ0` matches the
linear-in-terms total score induced by the additive structure.
-/
theorem paper_sd_total_sequential_consistency_to_gStar_ae_of_NoInteractions
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (Y : Profile K V → Ω → ℝ)
    (blk : Term K → B)
    (hNoInt : NoInteractions (K := K) (V := V) (μexp := μexp) (Y := Y))
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hTotalModel :
      ∀ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
        (∀ x, gStar (μexp := μexp) (Y := Y) x = α0 + ∑ k : K, main k (x k)) →
        ∀ x,
          gTotalΘ (gB := gB) θ0 x
            =
          gTotal
            (B := B)
            (g := gBlockTerm
              (blk := blk)
              (β := βMain (K := K) α0)
              (φ := φMain (K := K) (V := V) main))
            x)
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ (gB := gB)) θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A (ν)
              w (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε)
        ∧
        attrSD (ν) (gTotalΘ (gB := gB) θ0) =
          attrSD (ν) (gStar (μexp := μexp) (Y := Y)) := by
  rcases hNoInt with ⟨α0, main, hadd⟩
  have hspec :
      WellSpecified (Ω := Ω) (Attr := Profile K V) (Term := Term K)
        (μexp := μexp) (Y := Y) (β := βMain (K := K) α0) (φ := φMain (K := K) (V := V) main) := by
    intro x
    have hlin :
        gLin (Attr := Profile K V) (Term := Term K)
            (β := βMain (K := K) α0)
            (φ := φMain (K := K) (V := V) main) x
          =
        α0 + ∑ k : K, main k (x k) :=
      gLin_eq_additive (K := K) (V := V) α0 main x
    calc
      gLin (Attr := Profile K V) (Term := Term K)
          (β := βMain (K := K) α0)
          (φ := φMain (K := K) (V := V) main) x
          =
        α0 + ∑ k : K, main k (x k) := hlin
      _ = gStar (μexp := μexp) (Y := Y) x := by
        simpa using (hadd x).symm
  have hTotalModel' :
      ∀ x,
        gTotalΘ (gB := gB) θ0 x
          =
        gTotal
          (B := B)
          (g := gBlockTerm
            (blk := blk)
            (β := βMain (K := K) α0)
            (φ := φMain (K := K) (V := V) main))
          x :=
    hTotalModel α0 main hadd
  exact
    paper_sd_total_sequential_consistency_to_gStar_ae_of_WellSpecified
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMomEval := hMomEval)
      (μexp := μexp) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (Y := Y) (blk := blk) (β := βMain (K := K) α0) (φ := φMain (K := K) (V := V) main)
      (hTotalModel := hTotalModel') (hspec := hspec)
      (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)

end NoInteractionsCorollary

end ConjointSD
