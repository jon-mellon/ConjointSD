/-
ConjointSD/PaperWrappers.lean

A “paper-facing” wrapper layer that exposes the main checked implications in vocabulary
closest to the manuscript:

1) Conjoint identification (conditional means identify potential-outcome means; AMCE as
   difference of observed conditional means).

2) Regression / term model bridge to block decomposition (well-specification implies the
   causal estimand decomposes as a sum of block scores).

3) Sequential consistency for SDs, with plug-in moments derived from OLS:
   - per-block SDs are sequentially consistent (single M for all blocks, finite B),
   - total-score SD is sequentially consistent,
   - combined statement (blocks + total) with a single M.

4) “Convergence to the true estimand” is obtained by adding an explicit target-equality
   assumption (now via subject-sampling LLN), plus AE-congruence lemmas
   showing target human population SDs match when score functions match ν-a.e.
-/

import Mathlib
import ConjointSD.ModelBridge
import ConjointSD.Assumptions
import ConjointSD.Transport
import ConjointSD.DecompositionSequentialConsistency
import ConjointSD.SampleSplitting
import ConjointSD.TargetEquivalence
import ConjointSD.PaperOLSConsistency
import ConjointSD.DeriveGEstimationAssumptions
import ConjointSD.WellSpecifiedFromNoInteractions
import ConjointSD.SubjectSamplingLLNFromIID

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/-!
## 2) Route-2 sequential SD consistency wrappers (blocks + total)
-/

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

/-- Paper-facing: per-block SDs are sequentially consistent (single `M` works for all blocks). -/
theorem paper_sd_blocks_sequential_consistency_ae
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (hSplitBounded : ∀ m b,
      SplitEvalWeightAssumptionsBounded (ρ := ρ) (A := A) (w := w)
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
      (hSplit := hSplitBounded) (hLaw := hLaw) (hW := hW) (hPlug := hPlug)
      (ε := ε) (hε := hε)

/-- Paper-facing: total-score SD is sequentially consistent. -/
theorem paper_sd_total_sequential_consistency_ae
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (hSplitTotalBounded :
      ∀ m,
        SplitEvalWeightAssumptionsBounded (ρ := ρ) (A := A) (w := w)
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
      (hSplitTotal := hSplitTotalBounded) (hLaw := hLaw) (hW := hW) (hPlugTotal := hPlugTotal)
      (ε := ε) (hε := hε)

/-!
## 4) Turn “converges to attrSD ν (g θ0)” into “converges to the true SD target”
by assuming ν-a.e. equality to a declared true score function and using congruence lemmas.
-/

/--
Blocks: sequential consistency + ν-a.e. target equality packages convergence to the true block SD.
-/
theorem paper_sd_blocks_sequential_consistency_to_true_target_ae
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (hSplitBounded : ∀ m b,
      SplitEvalWeightAssumptionsBounded (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gB) b) (θhat := θhat) m)
    (hPlug : ∀ b : B,
      PlugInMomentAssumptions (ν := ν)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat))
    (gTrueB : B → Attr → ℝ)
    (hTrueB :
      ∀ b : B,
        ∀ᵐ x ∂ν, gBlock (gB := gB) b θ0 x = gTrueB b x)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hLaw := hLaw) (hW := hW)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitBounded := hSplitBounded) (hPlug := hPlug) (ε := ε) (hε := hε)
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

/--
Total-score: sequential consistency + ν-a.e. target equality packages convergence to the true SD.
-/
theorem paper_sd_total_sequential_consistency_to_true_target_ae
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
    (hTrue :
      ∀ᵐ x ∂ν, gTotalΘ (gB := gB) θ0 x = gTrue x)
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
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hLaw := hLaw) (hW := hW)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplitTotalBounded := hSplitTotalBounded) (hPlugTotal := hPlugTotal)
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

set_option linter.style.longLine false
theorem
    paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization
    (Atrain : ℕ → Ω → Profile K V) (Yobs : ℕ → Ω → ℝ)
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Atrain) (Y := Y))
    (hLawEval : EvalAttrLawEqPop (ρ := ρ) (A := Aeval) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (hSplitBlocks :
      ∀ ω m b,
        SplitEvalWeightAssumptionsBounded
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
    {Person : Type*} [MeasurableSpace Person]
    (μpop : Measure Person) [ProbMeasureAssumptions μpop]
    (R : ℕ → Ω → Person)
    (gP : Person → Profile K V → ℝ)
    (hSubjectIID :
      SubjectSamplingIID (μexp := μexp) (μpop := μpop) (R := R))
    (hSubjectScore :
      SubjectScoreAssumptions (μpop := μpop) (gP := gP))
    (hSubjectLLNStar :
      SubjectSamplingLLNStar
        (μexp := μexp) (ν := ν) (μpop := μpop)
        (R := R) (gP := gP) (Y := Y))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ θ0 : PaperTerm Main Inter → ℝ,
      (∀ᵐ ω ∂μexp,
        ∃ M : ℕ,
          ∀ m ≥ M,
            ∀ b : B,
              (∀ᵐ ω' ∂ρ,
                ∀ᶠ n : ℕ in atTop,
                  totalErr ρ Aeval (ν) w
                    (gBlock
                      (gB := fun b θ a =>
                        gBlockTerm (blk := blk) (β := θ)
                          (φ :=
                            φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
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
                        (φ :=
                          φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                    b θ0)
                =
                attrSD (ν)
                  (gBlockTerm (blk := blk) (β := θ0)
                    (φ :=
                      φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b))
      ∧
      (∀ᵐ x ∂ν,
        gPop (μpop := μpop) gP x
          =
        gTotal
          (B := B)
          (g := gBlockTerm (blk := blk) (β := θ0)
            (φ :=
              φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x) := by
  rcases
      wellSpecified_of_noInteractions_of_fullMainEffects
        (K := K) (V := V) (Term := PaperTerm Main Inter)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
        (μexp := μexp) (Y := Y) hTerms hNoInt with
    ⟨θ0, hspec⟩
  have hContBlocks :
      BlockFunctionalContinuityAssumptions (xiAttr := ν)
        (gB := fun b θ a =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
        θ0 :=
    blockFunctionalContinuity_gBlockTerm_of_bounded
      (Attr := Profile K V) (Main := Main) (Inter := Inter)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := ν) (blk := blk) (θ0 := θ0)
      hDesign.meas_fMain hDesign.meas_fInter
      hDesign.bound_fMain hDesign.bound_fInter
  have hTheta :
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
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Atrain) (Yobsω := Yobs)
      hRand hDesign hFull hspec
  have hStarEq :
      ∀ᵐ x ∂ν,
        gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ :=
                φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x
          =
        gStar (μexp := μexp) (Y := Y) x := by
    have hBlocks :
        gTotal
          (B := B)
          (g := gBlockTerm (blk := blk) (β := θ0)
            (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)))
          =
        gStar (μexp := μexp) (Y := Y) := by
      classical
      funext x
      have hLinBlocks :
          gLin (β := θ0)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
            =
          gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) :=
        gLin_eq_gTotal_blocks
          (B := B)
          (Term := PaperTerm Main Inter)
          (blk := blk)
          (β := θ0)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
      have hLinBlocksX :
          gTotal
              (B := B)
              (g := gBlockTerm (blk := blk) (β := θ0)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x
            =
          gLin (β := θ0)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) x := by
        simpa using congrArg (fun f => f x) hLinBlocks.symm
      calc
        gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ :=
                φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x
            =
          gLin (β := θ0)
              (φ :=
                φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) x := hLinBlocksX
        _ =
          gStar (μexp := μexp) (Y := Y) x := by
            simpa [WellSpecified] using hspec x
    refine ae_of_all _ ?_
    intro x
    simpa using congrArg (fun f => f x) hBlocks
  have hSubjectLLN :
      SubjectSamplingLLN
        (μexp := μexp) (ν := ν) (μpop := μpop)
        (R := R) (gP := gP) (Y := Y) :=
    subjectSamplingLLN_of_iid_of_lln_gStar
      (hIID := hSubjectIID) (hScore := hSubjectScore) (hStar := hSubjectLLNStar)
  have hPopEq :
      ∀ᵐ x ∂ν, gStar (μexp := μexp) (Y := Y) x = gPop (μpop := μpop) gP x :=
    subject_lln_ae_eq (h := hSubjectLLN)
  have hPopBlocks :
      ∀ᵐ x ∂ν,
        gPop (μpop := μpop) gP x
          =
        gTotal
          (B := B)
          (g := gBlockTerm (blk := blk) (β := θ0)
            (φ :=
              φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x := by
    refine (hPopEq.and hStarEq).mono ?_
    intro x hx
    exact hx.1.symm.trans hx.2.symm
  refine ⟨θ0, ?_⟩
  refine ⟨?_, hPopBlocks⟩
  filter_upwards [hTheta] with ω hThetaω
  have hPlugBlocks' :
      ∀ b : B,
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
    plugInMomentAssumptions_blocks_of_theta_tendsto
      (xiAttr := ν)
      (gB := fun b θ a =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
          n)
      hThetaω
      hContBlocks
  have hTrueB :
      ∀ b : B,
        ∀ᵐ x ∂ν,
          gBlock
              (gB := fun b θ a =>
                gBlockTerm (blk := blk) (β := θ)
                  (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
              b θ0 x
            =
          gBlockTerm (blk := blk) (β := θ0)
            (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b x := by
    intro b
    refine ae_of_all _ ?_
    intro x
    rfl
  rcases paper_sd_blocks_sequential_consistency_to_true_target_ae
      (ρ := ρ) (A := Aeval) (ν := ν) (w := w)
      (hLaw := hLawEval) (hW := hW)
      (gB := fun b θ a =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
          n)
      (hSplitBounded := hSplitBlocks ω)
      (hPlug := fun b => hPlugBlocks' b)
      (gTrueB := fun b =>
        gBlockTerm (blk := blk) (β := θ0)
          (φ :=
            φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b)
      (hTrueB := hTrueB)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  exact hM m hm b

set_option linter.style.longLine true

set_option linter.style.longLine false
theorem
    paper_sd_total_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization
    (Atrain : ℕ → Ω → Profile K V) (Yobs : ℕ → Ω → ℝ)
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Atrain) (Y := Y))
    (hLawEval : EvalAttrLawEqPop (ρ := ρ) (A := Aeval) (ν := ν))
    (hW : w = fun _ => (1 : ℝ))
    (hSplitTotal :
      ∀ ω m,
        SplitEvalWeightAssumptionsBounded
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
    {Person : Type*} [MeasurableSpace Person]
    (μpop : Measure Person) [ProbMeasureAssumptions μpop]
    (R : ℕ → Ω → Person)
    (gP : Person → Profile K V → ℝ)
    (hSubjectIID :
      SubjectSamplingIID (μexp := μexp) (μpop := μpop) (R := R))
    (hSubjectScore :
      SubjectScoreAssumptions (μpop := μpop) (gP := gP))
    (hSubjectLLNStar :
      SubjectSamplingLLNStar
        (μexp := μexp) (ν := ν) (μpop := μpop)
        (R := R) (gP := gP) (Y := Y))
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
                        (φ :=
                          φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
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
                      (φ :=
                        φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                  θ0)
              =
              attrSD (ν) (gPop (μpop := μpop) gP) := by
  rcases
      wellSpecified_of_noInteractions_of_fullMainEffects
        (K := K) (V := V) (Term := PaperTerm Main Inter)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
        (μexp := μexp) (Y := Y) hTerms hNoInt with
    ⟨θ0, hspec⟩
  have hContTotal :
      FunctionalContinuityAssumptions (xiAttr := ν)
        (g := gTotalΘ
          (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ :=
                φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
        θ0 :=
    functionalContinuity_gTotalΘ_of_bounded
      (Attr := Profile K V) (Main := Main) (Inter := Inter)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := ν) (blk := blk) (θ0 := θ0)
      hDesign.meas_fMain hDesign.meas_fInter
      hDesign.bound_fMain hDesign.bound_fInter
  have hTheta :
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
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Atrain) (Yobsω := Yobs)
      hRand hDesign hFull hspec
  refine ⟨θ0, ?_⟩
  filter_upwards [hTheta] with ω hThetaω
  have hPlugTotal' :
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
    plugInMomentAssumptions_of_theta_tendsto
      (xiAttr := ν)
      (g := gTotalΘ
        (gB := fun b θ a =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
          n)
      hThetaω
      hContTotal
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
        gTotal
          (B := B)
          (g := gBlockTerm (blk := blk) (β := θ0)
            (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)))
          =
        gStar (μexp := μexp) (Y := Y) := by
      classical
      funext x
      have hLinBlocks :
          gLin (β := θ0)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
            =
          gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) :=
        gLin_eq_gTotal_blocks
          (B := B)
          (Term := PaperTerm Main Inter)
          (blk := blk)
          (β := θ0)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
      have hLinBlocksX :
          gTotal
              (B := B)
              (g := gBlockTerm (blk := blk) (β := θ0)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x
            =
          gLin (β := θ0)
              (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) x := by
        simpa using congrArg (fun f => f x) hLinBlocks.symm
      calc
        gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ :=
                φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x
            =
          gLin (β := θ0)
              (φ :=
                φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) x := hLinBlocksX
        _ =
          gStar (μexp := μexp) (Y := Y) x := by
            simpa [WellSpecified] using hspec x
    refine ae_of_all _ ?_
    intro x
    have hBlocksx :
        gTotal
            (B := B)
            (g := gBlockTerm (blk := blk) (β := θ0)
              (φ :=
                φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x
          =
        gStar (μexp := μexp) (Y := Y) x := by
      simpa using congrArg (fun f => f x) hBlocks
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
  have hSubjectLLN :
      SubjectSamplingLLN
        (μexp := μexp) (ν := ν) (μpop := μpop)
        (R := R) (gP := gP) (Y := Y) :=
    subjectSamplingLLN_of_iid_of_lln_gStar
      (hIID := hSubjectIID) (hScore := hSubjectScore) (hStar := hSubjectLLNStar)
  have hInv :
      ∀ᵐ x ∂ν,
        gStar (μexp := μexp) (Y := Y) x = gPop (μpop := μpop) gP x :=
    subject_lln_ae_eq (h := hSubjectLLN)
  have hTrue :
      ∀ᵐ x ∂ν,
        gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
            θ0 x
          =
        gPop (μpop := μpop) gP x := by
    refine (hStarEq.and hInv).mono ?_
    intro x hx
    exact hx.1.trans hx.2
  rcases paper_sd_total_sequential_consistency_to_true_target_ae
      (ρ := ρ) (A := Aeval) (ν := ν) (w := w)
      (hLaw := hLawEval) (hW := hW)
      (gB := fun b θ a =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
          (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
          n)
      (hSplitTotalBounded := hSplitTotal ω)
      (hPlugTotal := hPlugTotal')
      (gTrue := gPop (μpop := μpop) gP) (hTrue := hTrue)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  exact hM m hm

set_option linter.style.longLine true

end SDSequentialConsistencyOLSNoInteractions

end ConjointSD
