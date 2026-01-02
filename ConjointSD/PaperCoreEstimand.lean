/-
ConjointSD/PaperCoreEstimand.lean

Core estimand used in the paper: target human population SDs of block contributions
(and of the total score),
expressed in terms of the “true block score” induced by the linear-in-terms model.
-/

import ConjointSD.TrueBlockEstimand
import ConjointSD.PaperWrappers

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/-!
## Core paper target: target human population SDs of true block contributions
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

/-- Target human population SD of the true block score for block `b` under `ν`. -/
def paperBlockSD
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) (b : B) : ℝ :=
  by
    let _ := (inferInstance : IsProbabilityMeasure ν)
    exact attrSD ν (paperTrueBlockScore blk β0 φ b)

/-- Target human population SD of the true total score under `ν`. -/
def paperTotalSD
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ) : ℝ :=
  by
    let _ := (inferInstance : IsProbabilityMeasure ν)
    exact attrSD ν (paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ))

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
    attrSD ν (paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ)) := rfl

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

variable (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
variable (A : ℕ → Ω → Attr)
variable (ν : Measure Attr) [ProbMeasureAssumptions ν]

/-- Paper’s main SD estimator: evaluation-stage SD for the term-induced total score. -/
def paperTotalSDEst
    (w : Attr → ℝ) (blk : Term → B) (βOf : Θ → Term → ℝ) (φ : Term → Attr → ℝ)
    (θhat : ℕ → Θ) (m n : ℕ) (ω : Ω) : ℝ :=
  sdEst ρ A w
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
    (hβ : βOf θ0 = β0)
    (w : Attr → ℝ)
    (hMomEval : ∀ m,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w)
        (s := gHat (gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ))) θhat m))
    (hSplitTotalBounded :
      ∀ m,
        SplitEvalWeightAssumptionsBounded
          (ρ := ρ) (A := A) (w := w)
          (g := gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)))
          (θhat := θhat) m)
    (hPlugTotal :
      PlugInMomentAssumptions (ν := ν)
        (g := gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)))
        (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            abs
              (paperTotalSDEst (ρ := ρ) (A := A)
                (w := w) (blk := blk) (βOf := βOf) (φ := φ)
                (θhat := θhat) m n ω
                - paperTotalSD (ν := ν) (blk := blk) (β0 := β0) (φ := φ))
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
  rcases paper_sd_total_sequential_consistency_to_true_target_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMomEval := hMomEval)
      (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ))
      (θ0 := θ0) (θhat := θhat)
      (hSplitTotalBounded := hSplitTotalBounded) (hPlugTotal := hPlugTotal)
      (gTrue := paperTrueTotalScore (blk := blk) (β0 := β0) (φ := φ))
      (hTrue := hTrue) (ε := ε) (hε := hε)
      with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hCons := hM m hm
  have hEqTarget :
      attrSD (ν)
          (gTotalΘ (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) θ0)
        =
      paperTotalSD (ν := ν) (blk := blk) (β0 := β0) (φ := φ) := by
    simpa [paperTotalSD] using hCons.2
  refine hCons.1.mono ?_
  intro ω hω
  refine hω.mono ?_
  intro n hn
  simpa [paperTotalSDEst, totalErr, sdOracle, hEqTarget] using hn

end MainEstimator

end ConjointSD
