/-
ConjointSD/PaperWrappers.lean

A “paper-facing” wrapper layer that exposes the main checked implications in vocabulary
closest to the manuscript:

1) Conjoint identification (conditional means identify potential-outcome means; AMCE as
   difference of observed conditional means).

2) Regression / term model bridge to block decomposition (well-specification implies the
   causal estimand decomposes as a sum of block scores).

3) Sequential consistency for SDs, with plug-in moments derived from OLS:
   - per-block SDs are sequentially consistent (single M for all blocks, finite B).

4) “Convergence to the true estimand” is obtained by adding an explicit target-equality
   assumption (now via subject-sampling LLN), plus AE-congruence lemmas
   showing target human population SDs match when score functions match ν_pop-a.e.
-/

import Mathlib
import ConjointSD.ModelBridge
import ConjointSD.Assumptions
import ConjointSD.Transport
import ConjointSD.DecompositionSequentialConsistency
import ConjointSD.SampleSplitting
import ConjointSD.TargetEquivalence
import ConjointSD.PaperOLSConsistency
import ConjointSD.WellSpecifiedFromNoInteractions
import ConjointSD.SubjectSamplingLLNFromIID

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/-!
## 2) Route-2 sequential SD consistency wrappers (blocks)
-/

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
## 4) Turn “converges to attrSD ν_pop (g θ0)” into “converges to the true SD target”
by assuming ν_pop-a.e. equality to a declared true score function and using congruence lemmas.
-/

/--
Blocks: sequential consistency + ν_pop-a.e. target equality packages
convergence to the true block SD.
-/
theorem paper_sd_blocks_sequential_consistency_to_true_target_ae
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
    (hTrueB :
      ∀ b : B,
        ∀ᵐ x ∂ν_pop, gBlock (gB := gB) b θ0 x = gTrueB b x)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A (ν_pop)
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε)
          ∧
          attrSD (ν_pop) (gBlock (gB := gB) b θ0)
            = attrSD (ν_pop) (gTrueB b) := by
  rcases sequential_consistency_blocks_ae
      (ρ := ρ) (A := A) (ν_pop := ν_pop)
      (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplitBounded) (hLaw := hLaw) (hMean := hMean) (hM2 := hM2)
      (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm b
  have hCons := hM m hm b
  have hEq :
      attrSD (ν_pop) (gBlock (gB := gB) b θ0)
        = attrSD (ν_pop) (gTrueB b) :=
    attrSD_congr_ae
      (ν_pop := ν_pop)
      (s := gBlock (gB := gB) b θ0) (t := gTrueB b) (hTrueB b)
  exact ⟨hCons, hEq⟩



end SDSequentialConsistency

section SDSequentialConsistencyOLSNoInteractions

variable {Ω : Type*} [MeasurableSpace Ω]
variable {K : Type*} {V : K → Type*} [Fintype K]
variable [∀ k : K, MeasurableSpace (V k)]
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable {B : Type*} [Fintype B] [DecidableEq B]
variable [DecidableEq (PaperTerm Main Inter)]

variable (ρ : Measure Ω) [IsProbabilityMeasure ρ]
variable (μexp : Measure Ω) [IsProbabilityMeasure μexp]
variable (Aeval : ℕ → Ω → Profile K V)

variable (ν_pop : Measure (Profile K V)) [IsProbabilityMeasure ν_pop]

variable (Y : Profile K V → Ω → ℝ)
variable (fMain : Main → Profile K V → ℝ) (fInter : Inter → Profile K V → ℝ)
variable (blk : PaperTerm Main Inter → B)

set_option linter.style.longLine false
theorem
    paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization
    (Atrain : ℕ → Ω → Profile K V) (Yobs : ℕ → Ω → ℝ)
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Atrain) (Y := Y))
    (hLawEval : EvalAttrLawEqPop (ρ := ρ) (A := Aeval) (ν_pop := ν_pop))
    (hSplitBlocks :
      ∀ ω m b,
        SplitEvalAssumptionsBounded
          (ρ := ρ) (A := Aeval)
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
      MainEffectsRepresentable
        (K := K) (V := V) (Term := PaperTerm Main Inter)
        (μexp := μexp) (Y := Y)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)))
    (hNoInt : NoInteractions (K := K) (V := V) (μexp := μexp) (Y := Y))
    {Person : Type*} [MeasurableSpace Person]
    (μpop : Measure Person) [IsProbabilityMeasure μpop]
    (R : ℕ → Ω → Person)
    (gP : Person → Profile K V → ℝ)
    (hSubjectIID :
      SubjectSamplingIID (μexp := μexp) (μpop := μpop) (R := R))
    (hSubjectScore :
      SubjectScoreAssumptions (μpop := μpop) (gP := gP))
    (hSubjectLLNStar :
      SubjectSamplingLLNStar
        (μexp := μexp) (ν_pop := ν_pop) (μpop := μpop)
        (R := R) (gP := gP) (Y := Y))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ θ0 : PaperTerm Main Inter → ℝ,
      (∀ᵐ ω ∂μexp,
        ∃ M : ℕ,
          ∀ m ≥ M,
            ∀ b : B,
              (∀ᵐ ω' ∂ρ,
                ∀ᶠ n : ℕ in atTop,
                  totalErr ρ Aeval (ν_pop)
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
              attrSD (ν_pop)
                  (gBlock
                    (gB := fun b θ a =>
                      gBlockTerm (blk := blk) (β := θ)
                        (φ :=
                          φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                    b θ0)
                =
                attrSD (ν_pop)
                  (gBlockTerm (blk := blk) (β := θ0)
                    (φ :=
                      φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b))
      ∧
      (∀ᵐ x ∂ν_pop,
        gPop (μpop := μpop) gP x
          =
        gTotal
          (B := B)
          (g := gBlockTerm (blk := blk) (β := θ0)
            (φ :=
              φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))) x) := by
  rcases
      wellSpecified_of_noInteractions_of_mainEffectsRepresentable
        (K := K) (V := V) (Term := PaperTerm Main Inter)
        (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
        (μexp := μexp) (Y := Y) hTerms hNoInt with
    ⟨θ0, hspec⟩
  have hContMeanBlocks :
      ∀ b : B,
        ContinuousAt
          (attrMeanΘ (xiAttr := ν_pop)
            (g := gBlock (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a) b))
          θ0 :=
    cont_mean_blocks_gBlockTerm_of_bounded
      (Attr := Profile K V) (Main := Main) (Inter := Inter)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := ν_pop) (blk := blk) (θ0 := θ0)
      hDesign.meas_fMain hDesign.meas_fInter
      hDesign.bound_fMain hDesign.bound_fInter
  have hContM2Blocks :
      ∀ b : B,
        ContinuousAt
          (attrM2Θ (xiAttr := ν_pop)
            (g := gBlock (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a) b))
          θ0 :=
    cont_m2_blocks_gBlockTerm_of_bounded
      (Attr := Profile K V) (Main := Main) (Inter := Inter)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := ν_pop) (blk := blk) (θ0 := θ0)
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
      ∀ᵐ x ∂ν_pop,
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
  have hPopEq :
      ∀ᵐ x ∂ν_pop, gStar (μexp := μexp) (Y := Y) x = gPop (μpop := μpop) gP x :=
    subject_lln_ae_eq_of_iid
      (hIID := hSubjectIID) (hScore := hSubjectScore) (hStar := hSubjectLLNStar)
  have hPopBlocks :
      ∀ᵐ x ∂ν_pop,
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
  have hMeanBlocks' :
      ∀ b : B,
        Tendsto
          (fun m =>
            attrMean ν_pop
              (gHat
                (gBlock
                  (gB := fun b θ a =>
                    gBlockTerm (blk := blk) (β := θ)
                      (φ :=
                        φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                  b)
                (fun n =>
                  olsThetaHat
                    (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
                    n)
                m))
          atTop
          (nhds
            (attrMean ν_pop
              (gBlock
                (gB := fun b θ a =>
                  gBlockTerm (blk := blk) (β := θ)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                b θ0))) := by
    intro b
    simpa [gBlock] using
      attrMean_tendsto_of_theta_tendsto
        (xiAttr := ν_pop)
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
            n)
        hThetaω
        (hContMeanBlocks b)
  have hM2Blocks' :
      ∀ b : B,
        Tendsto
          (fun m =>
            attrM2 ν_pop
              (gHat
                (gBlock
                  (gB := fun b θ a =>
                    gBlockTerm (blk := blk) (β := θ)
                      (φ :=
                        φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                  b)
                (fun n =>
                  olsThetaHat
                    (A := fun k => Atrain k ω) (Y := fun k => Yobs k ω)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter))
                    n)
                m))
          atTop
          (nhds
            (attrM2 ν_pop
              (gBlock
                (gB := fun b θ a =>
                  gBlockTerm (blk := blk) (β := θ)
                    (φ := φPaper (Attr := Profile K V) (fMain := fMain) (fInter := fInter)) b a)
                b θ0))) := by
    intro b
    simpa [gBlock] using
      attrM2_tendsto_of_theta_tendsto
        (xiAttr := ν_pop)
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
            n)
        hThetaω
        (hContM2Blocks b)
  have hTrueB :
      ∀ b : B,
        ∀ᵐ x ∂ν_pop,
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
      (ρ := ρ) (A := Aeval) (ν_pop := ν_pop)
      (hLaw := hLawEval)
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
      (hMean := fun b => hMeanBlocks' b)
      (hM2 := fun b => hM2Blocks' b)
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

end SDSequentialConsistencyOLSNoInteractions

end ConjointSD
