/-
ConjointSD/EstimatedG.lean

Step 3: handle that g depends on estimated parameters.

We assume the attribute-distribution moments on attributes (attrMean/attrM2/attrVar/attrSD)
are already defined in ConjointSD.Transport. We package assumptions about convergence of
attribute-distribution *mean* and *second moment* under ν_pop when we replace oracle `g θ0`
by `g (θhat n)`,
and we *derive* variance and SD convergence from those.
-/

import ConjointSD.Assumptions
import Mathlib.Topology.Basic

namespace ConjointSD

noncomputable section

universe u v

open scoped Topology
open Filter
open MeasureTheory

variable {Attr : Type u} [MeasurableSpace Attr]
variable {Θ : Type v}

/-- Derived: attribute-distribution variance convergence under ν_pop for the plug-in score. -/
theorem attrVar_tendsto_of_mean_m2_tendsto
    {ν_pop : Measure Attr} [ProbMeasureAssumptions ν_pop]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (hmean :
      Tendsto
        (fun n => attrMean ν_pop (gHat g θhat n))
        atTop
        (nhds (attrMean ν_pop (g θ0))))
    (hm2 :
      Tendsto
        (fun n => attrM2 ν_pop (gHat g θhat n))
        atTop
        (nhds (attrM2 ν_pop (g θ0)))) :
    Tendsto
      (fun n => attrVar ν_pop (gHat g θhat n))
      atTop
      (nhds (attrVar ν_pop (g θ0))) := by
  have hmean2 :
      Tendsto
        (fun n => (attrMean ν_pop (gHat g θhat n)) ^ 2)
        atTop
        (nhds ((attrMean ν_pop (g θ0)) ^ 2)) := by
    simpa [pow_two] using (hmean.mul hmean)
  have hvar :
      Tendsto
        (fun n => attrM2 ν_pop (gHat g θhat n) - (attrMean ν_pop (gHat g θhat n)) ^ 2)
        atTop
        (nhds (attrM2 ν_pop (g θ0) - (attrMean ν_pop (g θ0)) ^ 2)) :=
    hm2.sub hmean2
  simpa [attrVar] using hvar

/-- Derived: attribute-distribution SD convergence under ν_pop for the plug-in score. -/
theorem attrSD_tendsto_of_mean_m2_tendsto
    {ν_pop : Measure Attr} [ProbMeasureAssumptions ν_pop]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (hmean :
      Tendsto
        (fun n => attrMean ν_pop (gHat g θhat n))
        atTop
        (nhds (attrMean ν_pop (g θ0))))
    (hm2 :
      Tendsto
        (fun n => attrM2 ν_pop (gHat g θhat n))
        atTop
        (nhds (attrM2 ν_pop (g θ0)))) :
    Tendsto
      (fun n => attrSD ν_pop (gHat g θhat n))
      atTop
      (nhds (attrSD ν_pop (g θ0))) := by
  have hvar :=
    attrVar_tendsto_of_mean_m2_tendsto
      (ν_pop := ν_pop) (g := g) (θ0 := θ0) (θhat := θhat) hmean hm2
  have hsqrt :
      Tendsto Real.sqrt (nhds (attrVar ν_pop (g θ0)))
        (nhds (Real.sqrt (attrVar ν_pop (g θ0)))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  -- attrSD is defined as sqrt(attrVar)
  simpa [attrSD] using (hsqrt.comp hvar)

end
end ConjointSD
