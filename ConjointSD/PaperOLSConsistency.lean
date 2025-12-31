/-
ConjointSD/PaperOLSConsistency.lean

Paper-specific OLS consistency wrappers targeting the causal estimand `gStar`
with the paper's term set (intercept + main effects + interactions).
-/

import ConjointSD.ModelBridge
import ConjointSD.DecompositionSequentialConsistency
import ConjointSD.RegressionEstimator
import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.DesignAttributeBridge
import ConjointSD.Assumptions

open Filter MeasureTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section PaperTermScore

variable {Attr : Type*}
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]

variable (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)

/-- Paper regression score with coefficients `θ` on the paper term set. -/
def gPaper (θ : PaperTerm Main Inter → ℝ) : Attr → ℝ :=
  gLin (β := θ) (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))

theorem gPaper_eq_gTotalΘ_blocks
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B) :
    gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      =
    (fun θ a =>
      ∑ b : B,
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a) := by
  classical
  funext θ a
  have hblocks :
      gLin (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        =
      gTotal (B := B)
        (g := gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) :=
    gLin_eq_gTotal_blocks (B := B) (Term := PaperTerm Main Inter)
      (blk := blk) (β := θ)
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
  have hblocks' := congrArg (fun f => f a) hblocks
  have hTotal :
      (∑ b : B,
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
        =
      gTotal (B := B)
        (g := gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) a := by
    simp [gTotal]
  calc
    gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ a
        =
      gLin (β := θ)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) a := by
          simp [gPaper]
    _ = gTotal (B := B)
        (g := gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) a := hblocks'
    _ = ∑ b : B,
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a := by
        symm
        exact hTotal

end PaperTermScore

section PaperOLS

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable [DecidableEq (PaperTerm Main Inter)]

variable (μ : Measure Ω) [ProbMeasureAssumptions μ]
variable (ν : Measure Attr) [ProbMeasureAssumptions ν]

variable (Y : Attr → Ω → ℝ)
variable (A : ℕ → Attr) (Yobs : ℕ → ℝ)

variable (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)

omit [DecidableEq (PaperTerm Main Inter)] [ProbMeasureAssumptions ν] in
theorem paper_ols_lln_of_score_assumptions_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hYobs : ∀ n ω, Yobsω n ω = gStar (μ := μ) (Y := Y) (Aω n ω))
    (hScoreGram :
      ∀ i j,
        ScoreAssumptions
          (μ := μ) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)))
    (hScoreCross :
      ∀ i,
        ScoreAssumptions
          (μ := μ) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * gStar (μ := μ) (Y := Y) a)) :
    ∀ᵐ ω ∂μ,
      (∀ i j,
        Tendsto
          (fun n =>
            gramMatrix
              (A := fun k => Aω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n i j)
          atTop
          (nhds
            (attrGram
              (ν := Measure.map (Aω 0) μ)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)))
      ∧
      (∀ i,
        Tendsto
          (fun n =>
            crossVec
              (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n i)
          atTop
          (nhds
            (attrCross
              (ν := Measure.map (Aω 0) μ)
              (g := gStar (μ := μ) (Y := Y))
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))) := by
  classical
  have hgram : ∀ i j, ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          gramMatrix
            (A := fun k => Aω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i j)
        atTop
        (nhds
          (attrGram
            (ν := Measure.map (Aω 0) μ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)) := by
    intro i j
    let gGram : Attr → ℝ :=
      fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)
    have hIID :
        IIDAssumptions (μ := μ) (Zcomp (A := Aω) (g := gGram)) :=
      iidAssumptions_Zcomp (μ := μ) (A := Aω) (g := gGram) (hScoreGram i j)
    have hmean :
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n : ℕ =>
              meanHatZ (Z := Zcomp (A := Aω) (g := gGram)) n ω)
            atTop
            (nhds (designMeanZ (μ := μ) (Z := Zcomp (A := Aω) (g := gGram)))) :=
      meanHatZ_tendsto_ae (μ := μ) (Z := Zcomp (A := Aω) (g := gGram)) hIID
    have hpop :
        designMeanZ (μ := μ) (Z := Zcomp (A := Aω) (g := gGram))
          =
        attrMean (Measure.map (Aω 0) μ) gGram :=
      designMeanZ_Zcomp_eq_attrMean
        (μ := μ) (A := Aω) (g := gGram)
        (hA0 := (hScoreGram i j).designAttrIID.measA 0)
        (hg := (hScoreGram i j).meas_g)
    refine hmean.mono ?_
    intro ω hω
    have hω' :
        Tendsto
          (fun n =>
            meanHatZ (Z := Zcomp (A := Aω) (g := gGram)) n ω)
          atTop
          (nhds (attrMean (Measure.map (Aω 0) μ) gGram)) := by
      simpa [hpop] using hω
    have hgram_eq :
        ∀ n,
          gramMatrix
              (A := fun k => Aω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n i j
            =
          ((n : ℝ)⁻¹) * ∑ k ∈ Finset.range n,
            gGram (Aω k ω) := by
      intro n
      have hsum :
          (∑ k : Fin n, gGram (Aω k ω))
            =
          ∑ k ∈ Finset.range n, gGram (Aω k ω) := by
        simpa using (Fin.sum_univ_eq_sum_range (n := n) (fun k => gGram (Aω k ω)))
      simp [gramMatrix, gGram, hsum]
    simpa [meanHatZ, Zcomp, gGram, attrGram, hgram_eq]
      using hω'
  have hcross : ∀ i, ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          crossVec
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i)
        atTop
        (nhds
          (attrCross
            (ν := Measure.map (Aω 0) μ)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i)) := by
    intro i
    let gCross : Attr → ℝ :=
      fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μ := μ) (Y := Y) a
    have hIID :
        IIDAssumptions (μ := μ) (Zcomp (A := Aω) (g := gCross)) :=
      iidAssumptions_Zcomp (μ := μ) (A := Aω) (g := gCross) (hScoreCross i)
    have hmean :
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n : ℕ =>
              meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω)
            atTop
            (nhds (designMeanZ (μ := μ) (Z := Zcomp (A := Aω) (g := gCross)))) :=
      meanHatZ_tendsto_ae (μ := μ) (Z := Zcomp (A := Aω) (g := gCross)) hIID
    have hpop :
        designMeanZ (μ := μ) (Z := Zcomp (A := Aω) (g := gCross))
          =
        attrMean (Measure.map (Aω 0) μ) gCross :=
      designMeanZ_Zcomp_eq_attrMean
        (μ := μ) (A := Aω) (g := gCross)
        (hA0 := (hScoreCross i).designAttrIID.measA 0)
        (hg := (hScoreCross i).meas_g)
    refine hmean.mono ?_
    intro ω hω
    have hω' :
        Tendsto
          (fun n =>
            meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω)
          atTop
          (nhds (attrMean (Measure.map (Aω 0) μ) gCross)) := by
      simpa [hpop] using hω
    have hcross_eq :
        (fun n =>
          crossVec
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i)
          =
        (fun n =>
          meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω) := by
      funext n
      have hsum :
          (∑ k : Fin n, gCross (Aω k ω))
            =
          ∑ k ∈ Finset.range n, gCross (Aω k ω) := by
        simpa using (Fin.sum_univ_eq_sum_range (n := n) (fun k => gCross (Aω k ω)))
      simp [crossVec, meanHatZ, Zcomp, gCross, smul_eq_mul, hYobs, hsum]
    simpa [attrCross, gCross, hcross_eq] using hω'
  have hgram_all : ∀ᵐ ω ∂μ, ∀ i j, Tendsto
      (fun n =>
        gramMatrix
          (A := fun k => Aω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n i j)
      atTop
      (nhds
        (attrGram
          (ν := Measure.map (Aω 0) μ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)) := by
    refine (ae_all_iff.2 ?_)
    intro i
    refine (ae_all_iff.2 ?_)
    intro j
    exact hgram i j
  have hcross_all : ∀ᵐ ω ∂μ, ∀ i, Tendsto
      (fun n =>
        crossVec
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n i)
      atTop
      (nhds
        (attrCross
          (ν := Measure.map (Aω 0) μ)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i)) := by
    refine (ae_all_iff.2 ?_)
    intro i
    exact hcross i
  refine (hgram_all.and hcross_all).mono ?_
  intro ω hω
  rcases hω with ⟨hgramω, hcrossω⟩
  exact ⟨hgramω, hcrossω⟩

variable {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}

omit [ProbMeasureAssumptions μ] [ProbMeasureAssumptions ν] in
theorem paper_ols_attr_moments_of_lln_fullrank_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hLLN :
      ∀ᵐ ω ∂μ,
        (∀ i j,
          Tendsto
            (fun n =>
              gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n i j)
            atTop
            (nhds
              (attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)))
        ∧
        (∀ i,
          Tendsto
            (fun n =>
              crossVec
                (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n i)
            atTop
            (nhds
              (attrCross
                (ν := ν)
                (g := gStar (μ := μ) (Y := Y))
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))))
    (hInv :
      ∀ᵐ ω ∂μ,
        ∀ i j,
          Tendsto
            (fun n =>
              (gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n)⁻¹ i j)
            atTop
            (nhds
              ((attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
    (hId :
      θ0 =
        (attrGram
          (ν := ν)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (ν := ν)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))) :
    ∀ᵐ ω ∂μ,
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0 := by
  refine (hLLN.and hInv).mono ?_
  intro ω hω
  rcases hω with ⟨hLLNω, hInvω⟩
  refine
    { gramInv_tendsto := hInvω
      cross_tendsto := hLLNω.2
      theta0_eq := hId }

omit [ProbMeasureAssumptions μ] [ProbMeasureAssumptions ν] in
theorem theta_tendsto_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          olsThetaHat
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)
        atTop
        (nhds θ0) := by
  refine hMom.mono ?_
  intro ω hω
  simpa using
    (olsThetaHat_tendsto_of_attr_moments
      (ν := ν)
      (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
      (g := gStar (μ := μ) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      hω)

omit [ProbMeasureAssumptions μ] in
theorem GEstimationAssumptions_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μ,
      GEstimationAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0
        (fun n =>
          olsThetaHat
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n) := by
  refine (theta_tendsto_of_paper_ols_moments_ae
    (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
    (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom).mono ?_
  intro ω hθ
  exact
    GEstimationAssumptions_of_theta_tendsto
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      ⟨hθ⟩
      hCont

omit [ProbMeasureAssumptions μ] [ProbMeasureAssumptions ν] in
theorem theta_tendsto_of_paper_ols_moments
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := A) (Y := Yobs)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      atTop
      (nhds θ0) :=
  olsThetaHat_tendsto_of_attr_moments
    (ν := ν) (A := A) (Y := Yobs)
    (g := gStar (μ := μ) (Y := Y))
    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
    (θ0 := θ0)
    hMom

omit [ProbMeasureAssumptions μ] in
theorem GEstimationAssumptions_of_paper_ols_gStar
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := A) (Y := Yobs)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    GEstimationAssumptions
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      θ0
      (fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n) := by
  have hθ :
      Tendsto
        (fun n =>
          olsThetaHat
            (A := A) (Y := Yobs)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)
        atTop
        (nhds θ0) :=
    theta_tendsto_of_paper_ols_moments
      (μ := μ) (ν := ν)
      (Y := Y) (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom
  exact
    GEstimationAssumptions_of_theta_tendsto
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      ⟨hθ⟩
      hCont

omit [ProbMeasureAssumptions μ] in
theorem GEstimationAssumptions_of_paper_ols_gStar_total
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := A) (Y := Yobs)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    GEstimationAssumptions
      (ν := ν)
      (g := gTotalΘ
      (gB := fun b θ a =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
      θ0
      (fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n) := by
  have hG :
      GEstimationAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0
        (fun n =>
          olsThetaHat
            (A := A) (Y := Yobs)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n) :=
    GEstimationAssumptions_of_paper_ols_gStar
      (μ := μ) (ν := ν) (Y := Y)
      (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom hCont
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hG

omit [ProbMeasureAssumptions μ] in
theorem GEstimationAssumptions_of_paper_ols_moments_total_ae
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μ,
      GEstimationAssumptions
        (ν := ν)
        (g := gTotalΘ
          (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
        θ0
        (fun n =>
          olsThetaHat
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n) := by
  have hG :
      ∀ᵐ ω ∂μ,
        GEstimationAssumptions
          (ν := ν)
          (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0
          (fun n =>
            olsThetaHat
              (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n) :=
    GEstimationAssumptions_of_paper_ols_moments_ae
      (μ := μ) (ν := ν) (Y := Y)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom hCont
  refine hG.mono ?_
  intro ω hω
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hω

end PaperOLS

end ConjointSD
