/-
ConjointSD/WellSpecifiedFromNoInteractions.lean

Goal:
  Bridge from “no interactions” (additive structure over attributes)
  to `ConjointSD.WellSpecified` (i.e., `gStar` lies in the `gLin` class).

This file is written against ConjointSD/ModelBridge.lean as provided:
  - `gLin` : linear-in-terms model
  - `gStar`: conjoint causal estimand `x ↦ E[Y(x)]`
  - `WellSpecified μexp Y β φ` : ∀ x, gLin β φ x = gStar μexp Y x
-/

import ConjointSD.ModelBridge
import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

universe u v

/-!
## “No interactions” as exact additivity of the conjoint estimand `gStar`
-/

/-!
## Construct a linear-in-terms representation using `Term := Option K`
-/

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {K : Type u} {V : K → Type v} [Fintype K]

/-- Terms: `none` is intercept, `some k` is the main effect for attribute `k`. -/
abbrev Term (K : Type u) : Type u := Option K

/-- Coefficients: intercept gets `α0`, each main-effect term gets coefficient `1`. -/
def βMain (α0 : ℝ) : Term K → ℝ
  | none    => α0
  | some _  => 1

/-- Features: intercept feature is constant `1`; main-effect feature is `main k (x k)`. -/
def φMain (main : ∀ k : K, V k → ℝ) : Term K → Profile K V → ℝ
  | none    => fun _ => 1
  | some k  => fun x => main k (x k)

/-!
## Main bridge theorem: NoInteractions ⟹ WellSpecified
-/

/--
If `gStar` is additive and the term basis can express that additive surface,
then the model is well-specified for some coefficient vector.
-/
theorem wellSpecified_of_noInteractions_of_mainEffectsRepresentable
    {Term : Type*} [Fintype Term]
    (φ : Term → Profile K V → ℝ)
    (μexp : Measure Ω) (Y : Profile K V → Ω → ℝ)
    (hTerms :
      MainEffectsRepresentable
        (K := K) (V := V) (Term := Term) (μexp := μexp) (Y := Y) (φ := φ))
    (h : NoInteractions (K := K) (V := V) (μexp := μexp) (Y := Y)) :
    ∃ β : Term → ℝ,
      WellSpecified (Ω := Ω) (Attr := Profile K V) (Term := Term)
        (μexp := μexp) (Y := Y) (β := β) (φ := φ) := by
  classical
  rcases h with ⟨α0, main, hadd⟩
  rcases hTerms α0 main hadd with ⟨β, hβ⟩
  refine ⟨β, ?_⟩
  intro x
  calc
    gLin (Attr := Profile K V) (Term := Term) (β := β) (φ := φ) x
        = α0 + ∑ k : K, main k (x k) := hβ x
    _ = gStar (μexp := μexp) (Y := Y) x := by
        simpa using (hadd x).symm

end

end ConjointSD
