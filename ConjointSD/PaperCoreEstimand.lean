/-
ConjointSD/PaperCoreEstimand.lean

Core estimand used in the paper: population SDs of block contributions (and of the total score),
expressed in terms of the “true block score” induced by the linear-in-terms model.
-/

import ConjointSD.TrueBlockEstimand
import ConjointSD.PaperWrappers
import ConjointSD.SurveyWeights

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/-!
## Core paper target: population SDs of true block contributions
-/

section CoreEstimand

variable {Attr : Type*} [MeasurableSpace Attr]
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {Term : Type*} [Fintype Term]

variable (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ)

variable (ν : Measure Attr) [ProbMeasureAssumptions ν]

/-- Paper’s “true block score”: the block contribution `Attr → ℝ` for block `b`. -/
def paperTrueBlockScore (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) (b : B) : Attr → ℝ :=
  trueBlockScore blk β0 φ b

/-- Paper’s “true total score”: additive sum of block contributions. -/
def paperTrueTotalScore (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) : Attr → ℝ := by
  classical
  exact fun a => ∑ b : B, paperTrueBlockScore (blk := blk) (β0 := β0) (φ := φ) b a

/-- Population SD of the true block score for block `b` under `ν`. -/
def paperBlockSD
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) (b : B) : ℝ :=
  by
    let _ := (inferInstance : IsProbabilityMeasure ν)
    exact popSDAttr ν (paperTrueBlockScore blk β0 φ b)

/-- Population SD of the true total score under `ν`. -/
def paperTotalSD
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) : ℝ :=
  by
    let _ := (inferInstance : IsProbabilityMeasure ν)
    exact popSDAttr ν (paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ))

/-- Vector of paper block-SD targets. -/
def paperBlockSDs
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) : B → ℝ :=
  by
    let _ := (inferInstance : IsProbabilityMeasure ν)
    exact fun b => paperBlockSD (ν := ν) blk β0 φ b

theorem paperBlockSDs_apply
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) (b : B) :
    paperBlockSDs (ν := ν) blk β0 φ b = paperBlockSD (ν := ν) blk β0 φ b := rfl

theorem paperTotalSD_def
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) :
    paperTotalSD (ν := ν) blk β0 φ
      =
    popSDAttr ν (paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ)) := rfl

/-!
## Weighted population targets (survey-weighted population SDs)
-/

/-- Weighted population SD of the true block score for block `b` under `ν` with weights `w`. -/
def paperBlockSD_weighted
    (ν : Measure Attr) (w : Attr → ℝ)
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) (b : B) : ℝ :=
  weightSDAttr ν w (paperTrueBlockScore blk β0 φ b)

/-- Weighted population SD of the true total score under `ν` with weights `w`. -/
def paperTotalSD_weighted
    (ν : Measure Attr) (w : Attr → ℝ)
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) : ℝ :=
  weightSDAttr ν w (paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ))

/-- Vector of weighted paper block-SD targets. -/
def paperBlockSDs_weighted
    (ν : Measure Attr) (w : Attr → ℝ)
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) : B → ℝ :=
  fun b => paperBlockSD_weighted (ν := ν) (w := w) blk β0 φ b

theorem paperBlockSD_weighted_eq_pop
    (ν : Measure Attr) [ProbMeasureAssumptions ν] (w : Attr → ℝ)
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) (b : B)
    (hMom : WeightMatchesPopMoments (ν := ν) (w := w)
      (s := paperTrueBlockScore blk β0 φ b)) :
    paperBlockSD_weighted (ν := ν) (w := w) blk β0 φ b
      =
    paperBlockSD (ν := ν) blk β0 φ b := by
  simpa [paperBlockSD_weighted, paperBlockSD] using
    (weightSDAttr_eq_popSDAttr_of_moments (ν := ν) (w := w)
      (s := paperTrueBlockScore blk β0 φ b) hMom)

theorem paperTotalSD_weighted_eq_pop
    (ν : Measure Attr) [ProbMeasureAssumptions ν] (w : Attr → ℝ)
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ)
    (hMom : WeightMatchesPopMoments (ν := ν) (w := w)
      (s := paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ))) :
    paperTotalSD_weighted (ν := ν) (w := w) blk β0 φ
      =
    paperTotalSD (ν := ν) blk β0 φ := by
  simpa [paperTotalSD_weighted, paperTotalSD] using
    (weightSDAttr_eq_popSDAttr_of_moments (ν := ν) (w := w)
      (s := paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ)) hMom)

theorem paperBlockSDs_weighted_eq_pop
    (ν : Measure Attr) [ProbMeasureAssumptions ν] (w : Attr → ℝ)
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ)
    (hMom : ∀ b : B, WeightMatchesPopMoments (ν := ν) (w := w)
      (s := paperTrueBlockScore blk β0 φ b)) :
    ∀ b : B,
      paperBlockSDs_weighted (ν := ν) (w := w) blk β0 φ b
        =
      paperBlockSDs (ν := ν) blk β0 φ b := by
  intro b
  simpa [paperBlockSDs_weighted, paperBlockSDs, paperBlockSDs_apply] using
    paperBlockSD_weighted_eq_pop (ν := ν) (w := w)
      (blk := blk) (β0 := β0) (φ := φ) (b := b) (hMom := hMom b)

end CoreEstimand

/-!
## Main paper estimator: evaluation-stage SD for the term-induced total score
-/

section MainEstimator

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {Term : Type*} [Fintype Term]
variable {Θ : Type*} [TopologicalSpace Θ]

variable (μ : Measure Ω) [ProbMeasureAssumptions μ]
variable (A : ℕ → Ω → Attr)

variable (ν : Measure Attr) [ProbMeasureAssumptions ν]

/-- Paper’s main SD estimator: evaluation-stage SD for the term-induced total score. -/
def paperTotalSDEst
    (blk : Term → B) (βOf : Θ → Term → ℝ) (φ : Term → Attr → ℝ)
    (θhat : ℕ → Θ) (m n : ℕ) (ω : Ω) : ℝ :=
  sdEst μ A
    (gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)))
    θhat m n ω

/--
End-to-end wrapper: under coefficient identification and the sequential-consistency
assumptions, the paper’s main SD estimator converges (sequentially) to the paper’s
total SD target.
-/
theorem paper_total_sd_estimator_consistency_ae_of_gBTerm
    (blk : Term → B) (φ : Term → Attr → ℝ)
    (βOf : Θ → Term → ℝ) (β0 : Term → ℝ)
    (θ0 : Θ) (θhat : ℕ → Θ)
    (w : Attr → ℝ)
    (hβ : βOf θ0 = β0)
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions
          (μ := μ) (A := A)
          (g := gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)))
          (θhat := θhat) m)
    (hθ : ThetaTendstoAssumptions (θhat := θhat) (θ0 := θ0))
    (hContTotal :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)))
        θ0)
    (hMom :
      WeightMatchesPopMoments (ν := ν) (w := w)
        (s := paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ)))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            abs
              (paperTotalSDEst (μ := μ) (A := A)
                (blk := blk) (βOf := βOf) (φ := φ)
                (θhat := θhat) m n ω
                - paperTotalSD_weighted (ν := ν) (w := w) (blk := blk) (β0 := β0) (φ := φ))
              < ε) := by
  classical
  have hTrue :
      InvarianceAE
        (ν := ν)
        (gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) θ0)
        (paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ)) := by
    refine ae_of_all _ ?_
    intro a
    simp [paperTrueTotalScore, paperTrueBlockScore, trueBlockScore, gTotalΘ, gBTerm, hβ]
  rcases paper_sd_total_sequential_consistency_to_weighted_target_ae
      (μ := μ) (A := A) (ν := ν)
      (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ))
      (θ0 := θ0) (θhat := θhat)
      (hMap := hMap) (hSplitTotal := hSplitTotal) (hθ := hθ) (hContTotal := hContTotal)
      (gTrue := paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ))
      (hTrue := hTrue) (w := w) (hMom := hMom) (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hCons := hM m hm
  have hEqTarget :
      popSDAttr ν
          (gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) θ0)
        =
      paperTotalSD_weighted (ν := ν) (w := w) (blk := blk) (β0 := β0) (φ := φ) := by
    simpa [paperTotalSD_weighted] using hCons.2
  refine hCons.1.mono ?_
  intro ω hω
  refine hω.mono ?_
  intro n hn
  simpa [paperTotalSDEst, totalErr, sdOracle, hEqTarget] using hn

/-!
## Discharge `hTotalModel` automatically for the term model
-/

theorem gTotalΘ_eq_gTotal_gBTerm
    {Attr B Term Θ : Type*} [MeasurableSpace Attr]
    [Fintype B] [Fintype Term] [DecidableEq B]
    (blk : Term → B) (βOf : Θ → Term → ℝ) (φ : Term → Attr → ℝ) (θ0 : Θ) :
    ∀ x,
      gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) θ0 x
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := βOf θ0) (φ := φ)) x := by
  classical
  intro x
  simp [gTotalΘ, gBTerm, gTotal]

theorem paper_sd_total_sequential_consistency_to_gStar_ae_of_gBTerm
    (blk : Term → B) (φ : Term → Attr → ℝ)
    (βOf : Θ → Term → ℝ) (β : Term → ℝ)
    (θ0 : Θ) (θhat : ℕ → Θ)
    (hβ : βOf θ0 = β)
    (Y : Attr → Ω → ℝ)
    (hspec : WellSpecified (μ := μ) (Y := Y) (β := β) (φ := φ))
    (hMap : MapLawAssumptions (μ := μ) (A := A) (ν := ν))
    (hSplitTotal :
      ∀ m,
        SplitEvalAssumptions
          (μ := μ) (A := A)
          (g := gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)))
          (θhat := θhat) m)
    (hθ : ThetaTendstoAssumptions (θhat := θhat) (θ0 := θ0))
    (hContTotal :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)))
        θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν
              (gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)))
              θ0 θhat m n ω < ε)
        ∧
        popSDAttr ν
            (gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) θ0)
          =
        popSDAttr ν (gStar (μ := μ) (Y := Y)) := by
  have hTotalModel :
      ∀ x,
        gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) θ0 x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x := by
    intro x
    simpa [hβ] using
      (gTotalΘ_eq_gTotal_gBTerm
        (blk := blk) (βOf := βOf) (φ := φ) (θ0 := θ0) x)
  exact
    paper_sd_total_sequential_consistency_to_gStar_ae_of_WellSpecified
      (μ := μ) (A := A) (ν := ν)
      (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ))
      (θ0 := θ0) (θhat := θhat)
      (Y := Y) (blk := blk) (β := β) (φ := φ)
      (hTotalModel := hTotalModel) (hspec := hspec)
      (hMap := hMap) (hSplitTotal := hSplitTotal)
      (hθ := hθ) (hContTotal := hContTotal)
      (ε := ε) (hε := hε)

end MainEstimator

end ConjointSD
