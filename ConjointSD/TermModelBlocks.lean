/-
ConjointSD/TermModelBlocks.lean

Define a block-score model induced by a term-level linear model.
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
  by
    let _ := (inferInstance : MeasurableSpace Attr)
    exact fun b θ a => gBlockTerm (blk := blk) (β := βOf θ) (φ := φ) b a

end ConjointSD
