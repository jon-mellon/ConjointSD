/-
ConjointSD/TrueBlockEstimand.lean

Instantiate the “true target” for block SDs using a linear-in-terms representation.
-/

import ConjointSD.TermModelBlocks

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/-!
## 1) Term-induced “true block score” and its link to the conjoint causal estimand
-/

section TrueBlockScore

variable {Attr : Type*}
variable {B : Type*} [Fintype B]
variable {Term : Type*} [Fintype Term] [DecidableEq B]

variable (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ)

/-- “True” block score induced by `(blk, β0, φ)`. -/
def trueBlockScore (b : B) : Attr → ℝ :=
  gBlockTerm (blk := blk) (β := β0) (φ := φ) b

/--
If the conjoint causal estimand is well-specified by the linear-in-terms model
`(β0, φ)`, then it equals the sum of the induced true blocks.
-/
theorem gStar_eq_sum_trueBlocks_of_WellSpecified
    {Ωe : Type*} [MeasurableSpace Ωe]
    (μe : Measure Ωe) (Y : Attr → Ωe → ℝ)
    (hspec : WellSpecified (μexp := μe) (Y := Y) (β := β0) (φ := φ)) :
    gStar (μexp := μe) (Y := Y)
      =
    gTotal (B := B) (g := trueBlockScore (blk := blk) (β0 := β0) (φ := φ)) := by
  classical
  simpa [trueBlockScore] using
    (gStar_eq_sum_blocks_of_WellSpecified
      (μexp := μe) (Y := Y) (blk := blk) (β := β0) (φ := φ) hspec)

end TrueBlockScore

/-!
## 2) Block SD sequential consistency to the instantiated term-induced target
-/

section BlockSDToTrueTarget

variable {Attr : Type*} [MeasurableSpace Attr]
variable {B : Type*} [Fintype B]

variable {Ω : Type*} [MeasurableSpace Ω]
variable (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
variable (A : ℕ → Ω → Attr)

variable {Θ : Type*} [TopologicalSpace Θ]
variable (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)

/--
Generic block-SD sequential consistency to a supplied “true target” `trueBlockScore`,
assuming a pointwise block-specification hypothesis at `θ0`.
-/
theorem paper_blocks_converge_to_trueBlockSDs_ae
    {Term : Type*} [Fintype Term] [DecidableEq B]
    (blk : Term → B) (β0 : Term → ℝ) (φ : Term → Attr → ℝ)
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (w : Attr → ℝ)
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
    (hBlockSpec :
      ∀ b x,
        gBlock (gB := gB) b θ0 x
          =
        trueBlockScore (blk := blk) (β0 := β0) (φ := φ) b x)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A ν w
                (gBlock (gB := gB) b) θ0 θhat m n ω < ε)
          ∧
          attrSD ν (gBlock (gB := gB) b θ0)
            =
          attrSD ν
            (trueBlockScore (blk := blk) (β0 := β0) (φ := φ) b) := by
  classical
  let gTrueB : B → Attr → ℝ :=
    fun b => trueBlockScore (blk := blk) (β0 := β0) (φ := φ) b
  have hTrueB :
      ∀ b : B,
        InvarianceAE (ν := ν) (gBlock (gB := gB) b θ0) (gTrueB b) := by
    intro b
    refine ae_of_all _ ?_
    intro x
    simpa [gTrueB] using hBlockSpec b x
  simpa [gTrueB] using
    (paper_sd_blocks_sequential_consistency_to_true_target_ae
      (ρ := ρ) (A := A) (ν := ν) (w := w) (hMom := hMom) (gB := gB) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit) (hθ := hθ) (hCont := hCont)
      (gTrueB := gTrueB) (hTrueB := hTrueB)
      (ε := ε) (hε := hε))

/--
Term-model specialization: the block-specification hypothesis is discharged by
coefficient identification `βOf θ0 = β0` for the induced block-score model `gBTerm`.
-/
theorem paper_blocks_converge_to_trueBlockSDs_ae_of_gBTerm
    {Term : Type*} [Fintype Term] [DecidableEq B]
    (blk : Term → B) (φ : Term → Attr → ℝ)
    (βOf : Θ → Term → ℝ) (β0 : Term → ℝ)
    (hβ : βOf θ0 = β0)
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (w : Attr → ℝ)
    (hMom : ∀ m b,
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w)
        (s := gHat (gBlock (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) b) θhat m))
    (hSplit : ∀ m b,
      SplitEvalWeightAssumptions
        (ρ := ρ) (A := A) (w := w)
        (g := gBlock (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) b)
        (θhat := θhat) m)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : ∀ b : B,
      FunctionalContinuityAssumptions
        (xiAttr := ν)
        (g := gBlock (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) b)
        θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        ∀ b : B,
          (∀ᵐ ω ∂ρ,
            ∀ᶠ n : ℕ in atTop,
              totalErr ρ A ν w
                (gBlock (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) b)
                θ0 θhat m n ω < ε)
          ∧
          attrSD ν
            (gBlock (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) b θ0)
            =
          attrSD ν
            (trueBlockScore (blk := blk) (β0 := β0) (φ := φ) b) := by
  classical
  have hBlockSpec :
      ∀ b x,
        gBlock (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) b θ0 x
          =
        trueBlockScore (blk := blk) (β0 := β0) (φ := φ) b x := by
    intro b x
    have h :=
      gBTerm_blockSpec
        (blk := blk) (φ := φ) (βOf := βOf) (β0 := β0) (θ0 := θ0) hβ b x
    simpa [trueBlockScore] using h
  simpa using
    (paper_blocks_converge_to_trueBlockSDs_ae
      (ρ := ρ) (A := A) (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ))
      (θ0 := θ0) (θhat := θhat)
      (blk := blk) (β0 := β0) (φ := φ) (ν := ν) (w := w) (hMom := hMom)
      (hSplit := hSplit) (hθ := hθ) (hCont := hCont)
      (hBlockSpec := hBlockSpec) (ε := ε) (hε := hε))

end BlockSDToTrueTarget

end ConjointSD
