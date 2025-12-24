import Mathlib
import ConjointSD.VarianceDecompositionFromBlocks
import ConjointSD.ConjointIdentification

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

/-!
# Model bridge: from linear score models to block/component scores
-/

/-- An additive linear-in-terms score function. -/
def gLin {Attr Term : Type*} [Fintype Term]
    (β : Term → ℝ) (φ : Term → Attr → ℝ) : Attr → ℝ :=
  fun a => ∑ t, β t * φ t a

/--
Block score defined by summing the terms assigned to block `b`.

We use an `if` formulation so the additivity proof is just sum-swapping + `simp`.
-/
def gBlockTerm {Attr B Term : Type*} [Fintype B] [Fintype Term] [DecidableEq B]
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) : B → Attr → ℝ :=
  fun b a => ∑ t, (if blk t = b then (β t * φ t a) else 0)

/--
**Additivity bridge:** allocating each model term to exactly one block implies the total score
equals the sum of block scores.
-/
theorem gLin_eq_gTotal_blocks
    {Attr B Term : Type*}
    [Fintype B] [Fintype Term] [DecidableEq B]
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) :
    gLin (β := β) (φ := φ)
      =
    gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) := by
  classical
  funext a

  -- Prove RHS = LHS pointwise, then flip.
  have h :
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) a
        =
      gLin (β := β) (φ := φ) a := by
    calc
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) a
          = (∑ b : B, ∑ t : Term, (if blk t = b then (β t * φ t a) else 0)) := by
              simp [gTotal, gBlockTerm]
      _   = (∑ t : Term, ∑ b : B, (if blk t = b then (β t * φ t a) else 0)) := by
              -- swap the two finite sums
              simpa using
                (Finset.sum_comm
                  (s := (Finset.univ : Finset B))
                  (t := (Finset.univ : Finset Term))
                  (f := fun b t => (if blk t = b then (β t * φ t a) else 0)))
      _   = (∑ t : Term, (β t * φ t a)) := by
              -- inner sum over b picks exactly b = blk t
              refine Finset.sum_congr rfl ?_
              intro t ht
              -- `simp` knows how to evaluate `∑ b, if blk t = b then r else 0`
              simp [eq_comm]
      _   = gLin (β := β) (φ := φ) a := by
              simp [gLin]

  simpa using h.symm

/-!
## Optional: connect to the conjoint causal estimand
-/

/-- Conjoint causal estimand as a function of profiles: `g⋆ x = E[Y(x)]`. -/
def gStar {Ω Attr : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Attr → Ω → ℝ) : Attr → ℝ :=
  fun x => potMean (μ := μ) Y x

/-- Well-specification: the causal estimand lies in the linear-in-terms model class. -/
def WellSpecified
    {Ω Attr Term : Type*}
    [MeasurableSpace Ω] [Fintype Term]
    (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) : Prop :=
  ∀ x, gLin (β := β) (φ := φ) x = gStar (μ := μ) (Y := Y) x

/--
If the estimand is well-specified by a linear-in-terms model, then it decomposes into blocks
(using the chosen term-to-block assignment).
-/
theorem gStar_eq_sum_blocks_of_WellSpecified
    {Ω Attr B Term : Type*}
    [MeasurableSpace Ω] [Fintype B] [Fintype Term] [DecidableEq B]
    (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hspec : WellSpecified (μ := μ) (Y := Y) (β := β) (φ := φ)) :
    gStar (μ := μ) (Y := Y)
      =
    gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) := by
  classical
  funext x
  have hblocks :
      gLin (β := β) (φ := φ)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gLin_eq_gTotal_blocks (B := B) (Term := Term) (blk := blk) (β := β) (φ := φ)

  calc
    gStar (μ := μ) (Y := Y) x
        = gLin (β := β) (φ := φ) x := by
            simpa [WellSpecified] using (hspec x).symm
    _   = gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x := by
            simpa using congrArg (fun f => f x) hblocks

end ConjointSD
