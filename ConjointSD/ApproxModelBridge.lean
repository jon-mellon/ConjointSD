import ConjointSD.ModelBridge

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

section WellSpecified

variable {Ω Attr Term : Type*} [MeasurableSpace Ω] [Fintype Term]

/-- Approximate well-specification: the estimand is within ε of the linear-in-terms model. -/
def ApproxWellSpecified
    (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ x, |gLin (β := β) (φ := φ) x - gStar (μexp := μexp) (Y := Y) x| ≤ ε

/-- Approximate well-specification on target-population attribute support (ν_pop-a.e.). -/
def ApproxWellSpecifiedAE
    {Attr : Type*} [MeasurableSpace Attr]
    (ν_pop : Measure Attr) (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ᵐ x ∂ν_pop, |gLin (β := β) (φ := φ) x - gStar (μexp := μexp) (Y := Y) x| ≤ ε

end WellSpecified

/--
AE version of the approximation bridge: if `gStar` is ε-close to the linear model
on target-population support (ν_pop-a.e.), then it is ε-close to the induced block sum ν_pop-a.e.
-/
theorem gStar_approx_sum_blocks_of_ApproxWellSpecifiedAE
    {Ω Attr B Term : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Attr] [Fintype B] [Fintype Term] [DecidableEq B]
    (ν_pop : Measure Attr) (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ)
    (hspec : ApproxWellSpecifiedAE (ν_pop := ν_pop) (μexp := μexp) (Y := Y) (β := β) (φ := φ) ε) :
    ∀ᵐ x ∂ν_pop,
      |gStar (μexp := μexp) (Y := Y) x
        - gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x|
        ≤ ε := by
  classical
  have hblocks :
      gLin (β := β) (φ := φ)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gLin_eq_gTotal_blocks (B := B) (Term := Term) (blk := blk) (β := β) (φ := φ)
  have hlin :
      ∀ x,
        gLin (β := β) (φ := φ) x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x := by
    intro x
    simpa using congrArg (fun f => f x) hblocks
  refine hspec.mono ?_
  intro x hx
  simpa [hlin x, abs_sub_comm] using hx

end ConjointSD
