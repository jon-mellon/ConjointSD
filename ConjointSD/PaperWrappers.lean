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
import ConjointSD.SampleSplitting
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
    (hPlug : ∀ b : B,
      PlugInMomentAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
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
      (hSplit := hSplit) (hMom := hMom) (hPlug := hPlug)
      (ε := ε) (hε := hε)

theorem paper_sd_blocks_sequential_consistency_ae_of_randomization
    (Y : Attr → Ω → ℝ)
    (hRand : ConjointRandomizationStream (μexp := ρ) (A := A) (Y := Y))
    (hMom : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hSplit : ∀ m b,
      SplitEvalWeightAssumptionsNoIID (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hPlug : ∀ b : B,
      PlugInMomentAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A ν w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε) := by
  have hSplit' :
      ∀ m b,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gBlock (gB := gB) b) (θhat := θhat) m :=
    fun m b =>
      splitEvalWeightAssumptions_of_stream
        (ρ := ρ) (A := A) (Y := Y) (hStream := hRand)
        (w := w) (g := gBlock (gB := gB) b) (θhat := θhat) (m := m)
        (h := hSplit m b)
  exact
    paper_sd_blocks_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hMom := hMom) (hSplit := hSplit') (hPlug := hPlug)
      (ε := ε) (hε := hε)

theorem paper_sd_blocks_sequential_consistency_ae_of_bounded
    (hPop : EvalAttrIID (κ := ρ) A)
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
    (hPlug : ∀ b : B,
      PlugInMomentAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
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
      (hMom := hMom) (hPlug := hPlug)
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
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
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
      (hSplitTotal := hSplitTotal) (hMom := hMom) (hPlugTotal := hPlugTotal)
      (ε := ε) (hε := hε)

theorem paper_sd_total_sequential_consistency_ae_of_randomization
    (Y : Attr → Ω → ℝ)
    (hRand : ConjointRandomizationStream (μexp := ρ) (A := A) (Y := Y))
    (hMom : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptionsNoIID (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A ν w
              (gTotalΘ (gB := gB)) θ0 θhat m n ω < ε) := by
  have hSplitTotal' :
      ∀ m,
        SplitEvalWeightAssumptions (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m :=
    fun m =>
      splitEvalWeightAssumptions_of_stream
        (ρ := ρ) (A := A) (Y := Y) (hStream := hRand)
        (w := w) (g := gTotalΘ (gB := gB)) (θhat := θhat) (m := m)
        (h := hSplitTotal m)
  exact
    paper_sd_total_sequential_consistency_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hMom := hMom) (hSplitTotal := hSplitTotal') (hPlugTotal := hPlugTotal)
      (ε := ε) (hε := hε)

theorem paper_sd_total_sequential_consistency_ae_of_bounded
    (hPop : EvalAttrIID (κ := ρ) A)
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
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
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
      (hMom := hMom) (hPlugTotal := hPlugTotal)
      (ε := ε) (hε := hε)

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
    (hPlug : ∀ b : B,
      PlugInMomentAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
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
      (hSplit := hSplit) (hPlug := hPlug) (ε := ε) (hε := hε)
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

theorem paper_sd_blocks_sequential_consistency_to_true_target_ae_of_randomization
    (Y : Attr → Ω → ℝ)
    (hRand : ConjointRandomizationStream (μexp := ρ) (A := A) (Y := Y))
    (hMom : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gBlock (gB := gB) b) θhat m))
    (hSplit : ∀ m b,
      SplitEvalWeightAssumptionsNoIID (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hPlug : ∀ b : B,
      PlugInMomentAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
    (gTrueB : B → Attr → ℝ)
    (hTrueB : ∀ b, InvarianceAE (ν := ν) (gBlock (gB := gB) b θ0) (gTrueB b))
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
  rcases paper_sd_blocks_sequential_consistency_ae_of_randomization
      (ρ := ρ) (A := A) (ν := ν) (w := w) (Y := Y) (hRand := hRand)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hMom := hMom) (hSplit := hSplit) (hPlug := hPlug)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  have hCons := hM m hm b
  have hEq :
      attrSD (ν) (gBlock (gB := gB) b θ0)
        = attrSD (ν) (gTrueB b) :=
    attrSD_congr_ae
      (ν := ν) (s := gBlock (gB := gB) b θ0) (t := gTrueB b) (hTrueB b)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMom)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hPlug := hPlug)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMom)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hPlugTotal := hPlugTotal)
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
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
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
      (hSplitTotal := hSplitTotal) (hPlugTotal := hPlugTotal)
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

theorem paper_sd_total_sequential_consistency_to_true_target_ae_of_randomization
    (Y : Attr → Ω → ℝ)
    (hRand : ConjointRandomizationStream (μexp := ρ) (A := A) (Y := Y))
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat (gTotalΘ (gB := gB)) θhat m))
    (hSplitTotal :
      ∀ m,
        SplitEvalWeightAssumptionsNoIID (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gB)) (θhat := θhat) m)
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gB)) (θ0 := θ0) (θhat := θhat))
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
  rcases paper_sd_total_sequential_consistency_ae_of_randomization
      (ρ := ρ) (A := A) (ν := ν) (w := w) (Y := Y) (hRand := hRand)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hMom := hMomEval) (hSplitTotal := hSplitTotal)
      (hPlugTotal := hPlugTotal)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomEval)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hPlugTotal := hPlugTotal)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMomEval)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotal := hSplitTotal) (hPlugTotal := hPlugTotal)
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

theorem paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization
    (Atrain : ℕ → Ω → Profile K V) (Yobs : ℕ → Ω → ℝ)
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Atrain) (Y := Y))
    (hMomBlocks : ∀ ω m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := Aeval) (ν := ν)
        (w := w)
        (s := gHat
          (gBlock
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
            b)
          (fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n) m))
    (hSplitBlocks :
      ∀ ω m b,
        SplitEvalWeightAssumptions
          (ρ := ρ) (A := Aeval) (w := w)
          (g := gBlock
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
            b)
          (θhat := fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n) m)
    (hPlugBlocks :
      ∀ θ0,
        WellSpecified (μexp := μexp) (Y := Y) θ0
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) →
          ∀ ω b,
            PlugInMomentAssumptions
              (ν := ν)
              (g := gBlock
                (gB := fun b θ a =>
                  gBlockTerm (blk := blk) (β := θ)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                b)
              (θ0 := θ0)
              (θhat := fun n =>
                olsThetaHat
                  (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
                  (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
                  n))
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
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ θ0 : PaperTerm Main Inter → ℝ,
      ∀ᵐ ω ∂μexp,
        ∃ M : ℕ,
          ∀ m ≥ M,
            ∀ b : B,
              (∀ᵐ ω' ∂ρ,
                ∀ᶠ n : ℕ in atTop,
                  totalErr ρ Aeval (ν) w
                    (gBlock
                      (gB := fun b θ a =>
                        gBlockTerm (blk := blk) (β := θ)
                          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                      b)
                    θ0
                    (fun n =>
                      olsThetaHat
                        (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
                        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
                        n)
                    m n ω' < ε)
              ∧
              attrSD (ν)
                  (gBlock
                    (gB := fun b θ a =>
                      gBlockTerm (blk := blk) (β := θ)
                        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                    b θ0)
                =
                attrSD (ν)
                  (gBlockTerm (blk := blk) (β := θ0)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b) := by
  rcases
      wellSpecified_of_noInteractions_of_fullMainEffects
        (K := K) (V := V) (Term := PaperTerm Main Inter)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
        (μexp := μexp) (Y := Y) hTerms hNoInt with
    ⟨θ0, hspec⟩
  have hPlugBlocks' :
      ∀ ω b,
        PlugInMomentAssumptions
          (ν := ν)
          (g := gBlock
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
            b)
          (θ0 := θ0)
          (θhat := fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n) :=
    hPlugBlocks θ0 hspec
  refine ⟨θ0, ?_⟩
  refine ae_of_all _ ?_
  intro ω
  have hTrueB :
      ∀ b : B,
        InvarianceAE
          (ν := ν)
          (gBlock
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
            b θ0)
          (gBlockTerm (blk := blk) (β := θ0)
            (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b) := by
    intro b
    refine ae_of_all _ ?_
    intro x
    rfl
  rcases paper_sd_blocks_sequential_consistency_to_true_target_ae
      (ρ := ρ) (A := Aeval) (ν := ν) (w := w)
      (hMom := hMomBlocks ω)
      (gB := fun b θ a =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
          n)
      (hSplit := hSplitBlocks ω)
      (hPlug := fun b => hPlugBlocks' ω b)
      (gTrueB := fun b =>
        gBlockTerm (blk := blk) (β := θ0)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b)
      (hTrueB := hTrueB)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  exact hM m hm b

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
    (hPlugTotal :
      ∀ θ0,
        WellSpecified (μexp := μexp) (Y := Y) θ0
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) →
          ∀ ω,
            PlugInMomentAssumptions
              (ν := ν)
              (g := gTotalΘ
                (gB := fun b θ a =>
                  gBlockTerm (blk := blk) (β := θ)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
              (θ0 := θ0)
              (θhat := fun n =>
                olsThetaHat
                  (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
                  (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
                  n))
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
  have hPlugTotal' :
      ∀ ω,
        PlugInMomentAssumptions
          (ν := ν)
          (g := gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
          (θ0 := θ0)
          (θhat := fun n =>
            olsThetaHat
              (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
              n) :=
    hPlugTotal θ0 hspec
  refine ⟨θ0, ?_⟩
  refine ae_of_all _ ?_
  intro ω
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
      (ρ := ρ) (A := Aeval) (ν := ν) (w := w)
      (hMomEval := hMomTotal ω)
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
      (hPlugTotal := hPlugTotal' ω)
      (gTrue := gTrue) (hTrue := hTrue)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  exact hM m hm

end SDSequentialConsistencyOLSNoInteractions

end ConjointSD
