import Mathlib
import ConjointSD.Assumptions

open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

section ConjointIdentification

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω)
variable {Attr : Type*} [MeasurableSpace Attr]

/-- Randomized-assignment assumptions that imply the `rand` factorization. -/
structure ConjointIdRandomized
    [MeasurableSpace Attr] (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    [IsProbabilityMeasure μexp] : Prop where
  measX : Measurable X
  measYobs : Measurable Yobs
  measY : ∀ x, Measurable (Y x)
  consistency : ∀ ω, Yobs ω = Y (X ω) ω
  bounded :
    ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Y x ω| ≤ C
  ignorability : ∀ x, (fun ω => X ω) ⟂ᵢ[μexp] (fun ω => Y x ω)

end ConjointIdentification

end ConjointSD
