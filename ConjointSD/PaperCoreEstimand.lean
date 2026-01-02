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

end ConjointSD
