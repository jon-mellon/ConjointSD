/-
ConjointSD/EstimatedG.lean

Step 3: handle that g depends on estimated parameters.

We assume the attribute-distribution moments on attributes (attrMean/attrM2/attrVar/attrSD)
are already defined in ConjointSD.Transport. We package assumptions about convergence of
attribute-distribution *mean* and *second moment* under ν when we replace oracle `g θ0`
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

theorem attrMean_tendsto_of_GEstimationAssumptions
    {ν : Measure Attr} [ProbMeasureAssumptions ν]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => attrMean ν (gHat g θhat n))
      atTop
      (nhds (attrMean ν (g θ0))) :=
  h.mean_tendsto

theorem attrM2_tendsto_of_GEstimationAssumptions
    {ν : Measure Attr} [ProbMeasureAssumptions ν]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => attrM2 ν (gHat g θhat n))
      atTop
      (nhds (attrM2 ν (g θ0))) :=
  h.m2_tendsto

/-- Derived: attribute-distribution variance convergence under ν for the plug-in score. -/
theorem attrVar_tendsto_of_GEstimationAssumptions
    {ν : Measure Attr} [ProbMeasureAssumptions ν]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => attrVar ν (gHat g θhat n))
      atTop
      (nhds (attrVar ν (g θ0))) := by
  have hmean := h.mean_tendsto
  have hm2 := h.m2_tendsto
  have hmean2 :
      Tendsto
        (fun n => (attrMean ν (gHat g θhat n)) ^ 2)
        atTop
        (nhds ((attrMean ν (g θ0)) ^ 2)) := by
    simpa [pow_two] using (hmean.mul hmean)
  have hvar :
      Tendsto
        (fun n => attrM2 ν (gHat g θhat n) - (attrMean ν (gHat g θhat n)) ^ 2)
        atTop
        (nhds (attrM2 ν (g θ0) - (attrMean ν (g θ0)) ^ 2)) :=
    hm2.sub hmean2
  simpa [attrVar] using hvar

/-- Derived: attribute-distribution SD convergence under ν for the plug-in score. -/
theorem attrSD_tendsto_of_GEstimationAssumptions
    {ν : Measure Attr} [ProbMeasureAssumptions ν]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => attrSD ν (gHat g θhat n))
      atTop
      (nhds (attrSD ν (g θ0))) := by
  have hvar :=
    attrVar_tendsto_of_GEstimationAssumptions
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) h
  have hsqrt :
      Tendsto Real.sqrt (nhds (attrVar ν (g θ0)))
        (nhds (Real.sqrt (attrVar ν (g θ0)))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  -- attrSD is defined as sqrt(attrVar)
  simpa [attrSD] using (hsqrt.comp hvar)

end
end ConjointSD
