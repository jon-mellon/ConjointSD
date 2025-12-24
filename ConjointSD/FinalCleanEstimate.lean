/-
ConjointSD/FinalCleanEstimate.lean

Clean plug-in convergence statements for population functionals under a fixed target
attribute distribution `ν`, when we replace oracle `g θ0` by the estimated `g (θhat n)`.

This file is noncomputable because it uses integrals.
-/

import Mathlib
import ConjointSD.Transport
import ConjointSD.EstimatedG

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

universe u v

section

variable {Attr : Type u} [MeasurableSpace Attr]
variable (ν : Measure Attr) [IsProbabilityMeasure ν]

variable {Θ : Type v}
variable (g : Θ → Attr → ℝ)
variable (θ0 : Θ) (θhat : ℕ → Θ)

/-- Plug-in estimate of population mean under ν using θhat n. -/
def meanPlugIn (n : ℕ) : ℝ :=
  popMeanAttr ν (gHat g θhat n)

/-- Plug-in estimate of population second moment under ν using θhat n. -/
def m2PlugIn (n : ℕ) : ℝ :=
  popM2Attr ν (gHat g θhat n)

/-- Plug-in estimate of population variance under ν using θhat n. -/
def varPlugIn (n : ℕ) : ℝ :=
  popVarAttr ν (gHat g θhat n)

/-- Plug-in estimate of population SD under ν using θhat n. -/
def sdPlugIn (n : ℕ) : ℝ :=
  popSDAttr ν (gHat g θhat n)

theorem meanPlugIn_tendsto
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => meanPlugIn (ν := ν) (g := g) (θhat := θhat) n)
      atTop
      (nhds (popMeanAttr ν (g θ0))) := by
  simpa [meanPlugIn] using
    (popMeanAttr_tendsto_of_GEstimationAssumptions
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) h)

theorem m2PlugIn_tendsto
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => m2PlugIn (ν := ν) (g := g) (θhat := θhat) n)
      atTop
      (nhds (popM2Attr ν (g θ0))) := by
  simpa [m2PlugIn] using
    (popM2Attr_tendsto_of_GEstimationAssumptions
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) h)

theorem varPlugIn_tendsto
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => varPlugIn (ν := ν) (g := g) (θhat := θhat) n)
      atTop
      (nhds (popVarAttr ν (g θ0))) := by
  simpa [varPlugIn] using
    (popVarAttr_tendsto_of_GEstimationAssumptions
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) h)

theorem sdPlugIn_tendsto
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => sdPlugIn (ν := ν) (g := g) (θhat := θhat) n)
      atTop
      (nhds (popSDAttr ν (g θ0))) := by
  simpa [sdPlugIn] using
    (popSDAttr_tendsto_of_GEstimationAssumptions
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) h)

/-- Convenience corollary: the clean SD plug-in estimator is consistent (Tendsto). -/
theorem sdPlugIn_consistent
    (h : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => sdPlugIn (ν := ν) (g := g) (θhat := θhat) n)
      atTop
      (nhds (popSDAttr ν (g θ0))) :=
  sdPlugIn_tendsto (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) h

end

end ConjointSD
