import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω)

variable {Attr : Type*}
variable {B : Type*} [Fintype B]

/-- Total additive score. -/
def gTotal (g : B → Attr → ℝ) : Attr → ℝ :=
  fun a => Finset.sum Finset.univ (fun b => g b a)

end ConjointSD
