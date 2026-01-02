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

end TrueBlockScore
end ConjointSD
