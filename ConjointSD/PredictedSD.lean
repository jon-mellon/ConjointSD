import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (κ : Measure Ω)

/-- Measurable squaring map on ℝ. -/
lemma measurable_sq : Measurable (fun x : ℝ => x ^ 2) := by
  simpa [pow_two] using (measurable_id.mul measurable_id)


end ConjointSD
