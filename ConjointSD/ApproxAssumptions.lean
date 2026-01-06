import Mathlib
import ConjointSD.Defs

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
open scoped Topology

noncomputable section
namespace ConjointSD

section Transport

variable {Attr : Type*} [MeasurableSpace Attr]

/-- Approximate invariance on attribute-distribution support: `|s - t| ≤ ε` ν_pop-a.e. -/
def ApproxInvarianceAE (ν_pop : Measure Attr) (s t : Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ᵐ a ∂ν_pop, |s a - t a| ≤ ε

end Transport

section ApproximateOracle

variable {Attr : Type*} [MeasurableSpace Attr]

/--
Two-stage approximation: a flexible score `gFlex` approximates the experimental
causal score `gStar`, and the model score `gModel` approximates `gFlex`, both ν_pop-a.e.
-/
def ApproxOracleAE
    (ν_pop : Measure Attr)
    (gModel gFlex gStar : Attr → ℝ) (δModel δOracle : ℝ) : Prop :=
  (∀ᵐ x ∂ν_pop, |gModel x - gFlex x| ≤ δModel) ∧
  (∀ᵐ x ∂ν_pop, |gFlex x - gStar x| ≤ δOracle)

/--
L2-style approximation: the model score differs from the target by at most delta in mean-square.
-/
def L2Approx
    (ν_pop : Measure Attr)
    (gModel gTarget : Attr → ℝ) (δ : ℝ) : Prop :=
  MemLp (fun a => gModel a - gTarget a) (ENNReal.ofReal 2) ν_pop ∧
  Real.sqrt (∫ a, |gModel a - gTarget a| ^ 2 ∂ν_pop) ≤ δ

end ApproximateOracle

section WellSpecifiedFromNoInteractions

variable {Ω : Type*} [MeasurableSpace Ω]
variable {K : Type*} {V : K → Type*} [Fintype K]

/-- Approximate additivity: `gStar` is within ε of an additive main-effects surface. -/
def ApproxNoInteractions
    (μexp : Measure Ω) (Y : Profile K V → Ω → ℝ) (ε : ℝ) : Prop :=
  ∃ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V,
      |gStar (μexp := μexp) (Y := Y) x - (α0 + ∑ k : K, main k (x k))| ≤ ε

end WellSpecifiedFromNoInteractions

end ConjointSD
