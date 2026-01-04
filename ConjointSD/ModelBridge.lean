import ConjointSD.VarianceDecompositionFromBlocks
import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

/-!
# Model bridge: from linear score models to block/component scores
-/

section WellSpecified

variable {Ω Attr Term : Type*} [MeasurableSpace Ω] [Fintype Term]

/-- Well-specification: the causal estimand lies in the linear-in-terms model class. -/
def WellSpecified
    (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) : Prop :=
  ∀ x, gLin (β := β) (φ := φ) x = gStar (μexp := μexp) (Y := Y) x

end WellSpecified

/--
Block score defined by summing the terms assigned to block `b`.

We use an `if` formulation so the additivity proof is just sum-swapping + `simp`.
-/
def gBlockTerm {Attr B Term : Type*} [Fintype B] [Fintype Term] [DecidableEq B]
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) : B → Attr → ℝ :=
  by
    classical
    let _ := (inferInstance : Fintype B)
    exact fun b a => ∑ t, (if blk t = b then (β t * φ t a) else 0)

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

/-
## Parametric model: intercept + main effects + selected interactions

The paper runs a linear regression with an intercept, a collection of main-effect terms,
and a finite list of interaction terms. We encode exactly that term set and show that the
stated parametric equality of the causal estimand implies `WellSpecified`, which can then
be fed into the block decomposition bridge above.
-/

end ConjointSD
