/-
ConjointSD/PaperOLSConsistency.lean

Paper-specific OLS consistency wrappers targeting the causal estimand `gStar`
with the paper's term set (intercept + main effects + interactions).
-/

import ConjointSD.ModelBridge
import ConjointSD.RegressionEstimator

open Filter MeasureTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section PaperOLS

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable [DecidableEq (PaperTerm Main Inter)]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (ν : Measure Attr) [IsProbabilityMeasure ν]

variable (Y : Attr → Ω → ℝ)
variable (A : ℕ → Attr) (Yobs : ℕ → ℝ)

variable (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)

/-- Paper regression score with coefficients `θ` on the paper term set. -/
def gPaper (θ : PaperTerm Main Inter → ℝ) : Attr → ℝ :=
  gLin (β := θ) (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))

variable {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}

/--
Moment assumptions for the paper OLS estimator at the sample-path level.

This is the LLN/identifiability package: for almost every ω, the empirical Gram
and cross moments converge to their population targets for `gStar`.
-/
def PaperOLSMomentAssumptions
    (μ : Measure Ω) (ν : Measure Attr)
    (Y : Attr → Ω → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)
    (θ0 : PaperTerm Main Inter → ℝ)
    (Aω : ℕ → Ω → Attr) (Yobsω : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ,
    OLSMomentAssumptionsOfPop
      (ν := ν)
      (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
      (g := gStar (μ := μ) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      θ0

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem theta_tendsto_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom : PaperOLSMomentAssumptions
      (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
      θ0 Aω Yobsω) :
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
    (olsThetaHat_tendsto_of_pop_moments
      (ν := ν)
      (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
      (g := gStar (μ := μ) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      hω)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem theta_tendsto_of_paper_ols_moments
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfPop
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
  olsThetaHat_tendsto_of_pop_moments
    (ν := ν) (A := A) (Y := Yobs)
    (g := gStar (μ := μ) (Y := Y))
    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
    (θ0 := θ0)
    hMom

omit [IsProbabilityMeasure μ] in
theorem GEstimationAssumptions_of_paper_ols_gStar
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfPop
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
      hθ
      hCont

end PaperOLS

end ConjointSD
