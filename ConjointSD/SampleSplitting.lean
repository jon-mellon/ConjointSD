/-
ConjointSD/SampleSplitting.lean

Evaluation-stage convergence for sample-splitting arguments.

For a fixed training index `m`, treat `gHat g θhat m` as a fixed (“oracle”) score
function and apply the oracle SD consistency theorem.
-/

import ConjointSD.OracleSDConsistency
import ConjointSD.EstimatedG

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/--
Assumptions needed to evaluate the empirical SD of the score `gHat g θhat m`
on draws `A n` from the evaluation process.
-/
structure SplitEvalAssumptions
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hScore : ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m)
  hA0 : Measurable (A 0)

/--
For fixed training index `m`, the empirical SD of `gHat g θhat m (A i)` converges a.s.
to the population SD under the evaluation attribute law `law(A 0)`.
-/
theorem sdHat_fixed_m_tendsto_ae_popSDAttr
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
        atTop
        (nhds (popSDAttr (Measure.map (A 0) μ) (gHat g θhat m))) := by
  simpa using
    (sd_component_consistent_to_popSDAttr
      (μ := μ) (A := A) (ν := Measure.map (A 0) μ)
      (g := gHat g θhat m)
      (hScore := h.hScore)
      (hA0 := h.hA0)
      (hLaw := rfl))

end

end ConjointSD
