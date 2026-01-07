import Mathlib
import ConjointSD.ConjointIdentification
import ConjointSD.StatusConjointDesign
import ConjointSD.Assumptions

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/-!
## 1) Conjoint identification wrappers
-/

section Identification

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω) [IsProbabilityMeasure μexp]
variable {Attr : Type*} [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
variable (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)

/-- Identification: observed conditional mean among `X = x0` equals the potential-outcome mean. -/
theorem paper_identifies_potMean_from_condMean
    (h : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (x0 : Attr)
    (hpos : μexp (eventX (X := X) x0) ≠ 0) :
    condMean (κ := μexp) Yobs (eventX (X := X) x0) = potMean (κ := μexp) Y x0 :=
  identified_potMean_from_condMean (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) h x0 hpos

end Identification

/-!
## 1b) Status-conjoint identification wrappers
-/

end ConjointSD
