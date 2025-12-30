/-
ConjointSD/EstimatedG.lean

Step 3: handle that g depends on estimated parameters.

We assume the population moments on attributes (popMeanAttr/popM2Attr/popVarAttr/popSDAttr)
are already defined in ConjointSD.Transport. We package assumptions about convergence of
population *mean* and *second moment* under ν when we replace oracle `g θ0` by `g (θhat n)`,
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

theorem popMeanAttr_tendsto_of_GEstimationAssumptions
    {ν : Measure Attr} [ProbMeasureAssumptions ν]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => popMeanAttr ν (gHat g θhat n))
      atTop
      (nhds (popMeanAttr ν (g θ0))) :=
  h.mean_tendsto

theorem popM2Attr_tendsto_of_GEstimationAssumptions
    {ν : Measure Attr} [ProbMeasureAssumptions ν]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => popM2Attr ν (gHat g θhat n))
      atTop
      (nhds (popM2Attr ν (g θ0))) :=
  h.m2_tendsto

/-- Derived: population variance convergence under ν for the plug-in score. -/
theorem popVarAttr_tendsto_of_GEstimationAssumptions
    {ν : Measure Attr} [ProbMeasureAssumptions ν]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => popVarAttr ν (gHat g θhat n))
      atTop
      (nhds (popVarAttr ν (g θ0))) := by
  have hmean := h.mean_tendsto
  have hm2 := h.m2_tendsto
  have hmean2 :
      Tendsto
        (fun n => (popMeanAttr ν (gHat g θhat n)) ^ 2)
        atTop
        (nhds ((popMeanAttr ν (g θ0)) ^ 2)) := by
    simpa [pow_two] using (hmean.mul hmean)
  have hvar :
      Tendsto
        (fun n => popM2Attr ν (gHat g θhat n) - (popMeanAttr ν (gHat g θhat n)) ^ 2)
        atTop
        (nhds (popM2Attr ν (g θ0) - (popMeanAttr ν (g θ0)) ^ 2)) :=
    hm2.sub hmean2
  simpa [popVarAttr] using hvar

/-- Derived: population SD convergence under ν for the plug-in score. -/
theorem popSDAttr_tendsto_of_GEstimationAssumptions
    {ν : Measure Attr} [ProbMeasureAssumptions ν]
    {g : Θ → Attr → ℝ} {θ0 : Θ} {θhat : ℕ → Θ}
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => popSDAttr ν (gHat g θhat n))
      atTop
      (nhds (popSDAttr ν (g θ0))) := by
  have hvar :=
    popVarAttr_tendsto_of_GEstimationAssumptions
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) h
  have hsqrt :
      Tendsto Real.sqrt (nhds (popVarAttr ν (g θ0)))
        (nhds (Real.sqrt (popVarAttr ν (g θ0)))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  -- popSDAttr is defined as sqrt(popVarAttr)
  simpa [popSDAttr] using (hsqrt.comp hvar)

end
end ConjointSD
