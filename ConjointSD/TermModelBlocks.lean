/-
ConjointSD/TermModelBlocks.lean

Define a block-score model induced by a term-level linear model, and prove the
coefficient-identification specialization needed to discharge the block-specification
assumption in the paper-facing theorems.
-/

import ConjointSD.PaperWrappers

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section
namespace ConjointSD

/--
Block-score model induced by a term-level coefficient map `βOf` and term features `φ`:
each block sums the terms assigned to it.
-/
def gBTerm
    {Attr B Term Θ : Type*}
    [MeasurableSpace Attr] [Fintype B] [Fintype Term] [DecidableEq B]
    (blk : Term → B) (βOf : Θ → Term → ℝ) (φ : Term → Attr → ℝ) :
    B → Θ → Attr → ℝ :=
  fun b θ a => gBlockTerm (blk := blk) (β := βOf θ) (φ := φ) b a

/--
If `βOf θ0 = β0`, then the limiting block score induced by `gBTerm` at `θ0`
equals the “true” term-induced block score using coefficients `β0`.
-/
theorem gBTerm_blockSpec
    {Attr B Term Θ : Type*}
    [MeasurableSpace Attr] [Fintype B] [Fintype Term] [DecidableEq B]
    (blk : Term → B) (φ : Term → Attr → ℝ) (βOf : Θ → Term → ℝ)
    (β0 : Term → ℝ) (θ0 : Θ)
    (hβ : βOf θ0 = β0) :
    ∀ b x,
      gBlock (gB := gBTerm (blk := blk) (βOf := βOf) (φ := φ)) b θ0 x
        =
      gBlockTerm (blk := blk) (β := β0) (φ := φ) b x := by
  intro b x
  simp [ConjointSD.gBlock, gBTerm, hβ]

end ConjointSD
