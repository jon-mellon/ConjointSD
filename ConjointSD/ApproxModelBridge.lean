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

end ConjointSD
