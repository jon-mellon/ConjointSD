/-
ConjointSD/WellSpecifiedFromNoInteractions.lean

Goal:
  Bridge from “no interactions” (additive structure over attributes)
  to `ConjointSD.WellSpecified` (i.e., `gStar` lies in the `gLin` class).

This file is written against ConjointSD/ModelBridge.lean as provided:
  - `gLin` : linear-in-terms model
  - `gStar`: conjoint causal estimand `x ↦ E[Y(x)]`
  - `WellSpecified μ Y β φ` : ∀ x, gLin β φ x = gStar μ Y x
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

/-- Coefficients: intercept gets `μ0`, each main-effect term gets coefficient `1`. -/
def βMain (μ0 : ℝ) : Term K → ℝ
  | none    => μ0
  | some _  => 1

/-- Features: intercept feature is constant `1`; main-effect feature is `main k (x k)`. -/
def φMain (main : ∀ k : K, V k → ℝ) : Term K → Profile K V → ℝ
  | none    => fun _ => 1
  | some k  => fun x => main k (x k)

/-- The resulting `gLin` is exactly `μ0 + ∑ k, main k (x k)`. -/
  theorem gLin_eq_additive
      (μ0 : ℝ) (main : ∀ k : K, V k → ℝ) (x : Profile K V) :
      gLin (Attr := Profile K V) (Term := Term K)
          (β := βMain (K := K) μ0)
          (φ := φMain (K := K) (V := V) main) x
        =
      μ0 + ∑ k : K, main k (x k) := by
    classical
    -- Split the `Option K` sum into the `none` term plus the `some k` terms.
    simp [gLin, βMain, φMain, Fintype.sum_option]

/-!
## Main bridge theorem: NoInteractions ⟹ WellSpecified
-/

/--
If `gStar` is additive in the attributes (no interactions), then it is well-specified by a
linear-in-terms model with `Term := Option K` (intercept + main effects).
-/
theorem wellSpecified_of_noInteractions
    (μ : Measure Ω) (Y : Profile K V → Ω → ℝ)
    (h : NoInteractions (K := K) (V := V) (μ := μ) (Y := Y)) :
    ∃ (β : Term K → ℝ) (φ : Term K → Profile K V → ℝ),
      WellSpecified (Ω := Ω) (Attr := Profile K V) (Term := Term K)
        (μ := μ) (Y := Y) (β := β) (φ := φ) := by
  classical
  rcases h with ⟨μ0, main, hadd⟩
  refine ⟨βMain (K := K) μ0, φMain (K := K) (V := V) main, ?_⟩
  intro x
  have hlin :
      gLin (Attr := Profile K V) (Term := Term K)
          (β := βMain (K := K) μ0)
          (φ := φMain (K := K) (V := V) main) x
        =
      μ0 + ∑ k : K, main k (x k) :=
    gLin_eq_additive (K := K) (V := V) μ0 main x
  -- Convert the additive form into the `WellSpecified` equality.
  calc
    gLin (Attr := Profile K V) (Term := Term K)
        (β := βMain (K := K) μ0)
        (φ := φMain (K := K) (V := V) main) x
        = μ0 + ∑ k : K, main k (x k) := hlin
    _   = gStar (μ := μ) (Y := Y) x := by
            simpa using (hadd x).symm

end

end ConjointSD
