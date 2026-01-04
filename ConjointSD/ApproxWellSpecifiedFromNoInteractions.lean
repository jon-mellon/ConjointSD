import ConjointSD.WellSpecifiedFromNoInteractions
import ConjointSD.ApproxModelBridge

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {K : Type*} {V : K → Type*} [Fintype K]

/--
If `gStar` is approximately additive and the term features include the full
set of main effects, then the model is approximately well-specified.
-/
theorem approxWellSpecified_of_approxNoInteractions_of_fullMainEffects
    {Term : Type*} [Fintype Term]
    (φ : Term → Profile K V → ℝ)
    (μexp : Measure Ω) (Y : Profile K V → Ω → ℝ) (ε : ℝ)
    (hTerms : FullMainEffectsTerms (K := K) (V := V) (Term := Term) (φ := φ))
    (h : ApproxNoInteractions (K := K) (V := V) (μexp := μexp) (Y := Y) ε) :
    ∃ β : Term → ℝ,
      ApproxWellSpecified (μexp := μexp) (Y := Y) (β := β) (φ := φ) ε := by
  rcases h with ⟨α0, main, happrox⟩
  rcases hTerms α0 main with ⟨β, hβ⟩
  refine ⟨β, ?_⟩
  intro x
  have hlin :
      gLin (Attr := Profile K V) (Term := Term) (β := β) (φ := φ) x
        =
      α0 + ∑ k : K, main k (x k) := hβ x
  calc
    |gLin (Attr := Profile K V) (Term := Term) (β := β) (φ := φ) x
        - gStar (μexp := μexp) (Y := Y) x|
        =
      |gStar (μexp := μexp) (Y := Y) x - (α0 + ∑ k : K, main k (x k))| := by
        simp [hlin, abs_sub_comm]
    _ ≤ ε := happrox x

end

end ConjointSD
