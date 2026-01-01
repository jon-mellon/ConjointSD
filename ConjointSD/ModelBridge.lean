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

/-- Approximate well-specification: the estimand is within ε of the linear-in-terms model. -/
def ApproxWellSpecified
    (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ x, |gLin (β := β) (φ := φ) x - gStar (μexp := μexp) (Y := Y) x| ≤ ε

/-- Approximate well-specification on target-population attribute support (ν-a.e.). -/
def ApproxWellSpecifiedAE
    {Attr : Type*} [MeasurableSpace Attr]
    (ν : Measure Attr) (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ᵐ x ∂ν, |gLin (β := β) (φ := φ) x - gStar (μexp := μexp) (Y := Y) x| ≤ ε

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

/--
If the estimand is well-specified by a linear-in-terms model, then it decomposes into blocks
(using the chosen term-to-block assignment).
-/
theorem gStar_eq_sum_blocks_of_WellSpecified
    {Ω Attr B Term : Type*}
    [MeasurableSpace Ω] [Fintype B] [Fintype Term] [DecidableEq B]
    (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hspec : WellSpecified (μexp := μexp) (Y := Y) (β := β) (φ := φ)) :
    gStar (μexp := μexp) (Y := Y)
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
    gStar (μexp := μexp) (Y := Y) x
        = gLin (β := β) (φ := φ) x := by
            simpa [WellSpecified] using (hspec x).symm
    _   = gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x := by
            simpa using congrArg (fun f => f x) hblocks

/--
If the estimand is within ε of a linear-in-terms model, it is within ε of the induced block sum.
-/
theorem gStar_approx_sum_blocks_of_ApproxWellSpecified
    {Ω Attr B Term : Type*}
    [MeasurableSpace Ω] [Fintype B] [Fintype Term] [DecidableEq B]
    (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ)
    (hspec : ApproxWellSpecified (μexp := μexp) (Y := Y) (β := β) (φ := φ) ε) :
    ∀ x,
      |gStar (μexp := μexp) (Y := Y) x
        - gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x|
        ≤ ε := by
  classical
  intro x
  have hblocks :
      gLin (β := β) (φ := φ)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gLin_eq_gTotal_blocks (B := B) (Term := Term) (blk := blk) (β := β) (φ := φ)
  have hlin :
      gLin (β := β) (φ := φ) x
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x := by
    simpa using congrArg (fun f => f x) hblocks
  have h := hspec x
  simpa [hlin, abs_sub_comm] using h

/--
AE version of the approximation bridge: if `gStar` is ε-close to the linear model
on target-population support (ν-a.e.), then it is ε-close to the induced block sum ν-a.e.
-/
theorem gStar_approx_sum_blocks_of_ApproxWellSpecifiedAE
    {Ω Attr B Term : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Attr] [Fintype B] [Fintype Term] [DecidableEq B]
    (ν : Measure Attr) (μexp : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ)
    (hspec : ApproxWellSpecifiedAE (ν := ν) (μexp := μexp) (Y := Y) (β := β) (φ := φ) ε) :
    ∀ᵐ x ∂ν,
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

/-
## Parametric model: intercept + main effects + selected interactions

The paper runs a linear regression with an intercept, a collection of main-effect terms,
and a finite list of interaction terms. We encode exactly that term set and show that the
stated parametric equality of the causal estimand implies `WellSpecified`, which can then
be fed into the block decomposition bridge above.
-/

end ConjointSD
