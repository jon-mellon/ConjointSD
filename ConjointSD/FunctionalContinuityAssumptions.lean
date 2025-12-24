/-
ConjointSD/FunctionalContinuityAssumptions.lean

Helper lemmas for Route 2.

Important: `FunctionalContinuityAssumptions` is already defined elsewhere
(currently in `ConjointSD.RegressionConsistencyBridge`), and its field names may
differ. So this file never refers to fields like `.mean_cont`; instead, it
extracts the needed `ContinuousAt` facts by type.
-/

import ConjointSD.RegressionConsistencyBridge
import ConjointSD.Transport

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

universe u v

section

variable {Attr : Type u} [MeasurableSpace Attr]
variable {Θ : Type v} [TopologicalSpace Θ]

variable (ν : Measure Attr) [IsProbabilityMeasure ν]
variable (g : Θ → Attr → ℝ) (θ0 : Θ)

/-- Extract mean-continuity at `θ0` from `FunctionalContinuityAssumptions` (field-name free). -/
theorem meanContinuousAt_of_FunctionalContinuityAssumptions
    (hC : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    ContinuousAt (fun θ => popMeanAttr ν (g θ)) θ0 := by
  rcases hC with ⟨h1, h2⟩
  first
  | simpa using h1
  | simpa using h2

/-- Extract second-moment continuity at `θ0` from `FunctionalContinuityAssumptions` (field-name free). -/
theorem m2ContinuousAt_of_FunctionalContinuityAssumptions
    (hC : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    ContinuousAt (fun θ => popM2Attr ν (g θ)) θ0 := by
  rcases hC with ⟨h1, h2⟩
  first
  | simpa using h1
  | simpa using h2

/-- If `θhat → θ0`, then the population mean plug-in converges by continuity. -/
theorem popMeanAttr_tendsto_of_theta_tendsto
    {θhat : ℕ → Θ}
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hC : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    Tendsto
      (fun n => popMeanAttr ν (g (θhat n)))
      atTop
      (nhds (popMeanAttr ν (g θ0))) := by
  have hMeanCont :
      ContinuousAt (fun θ => popMeanAttr ν (g θ)) θ0 :=
    meanContinuousAt_of_FunctionalContinuityAssumptions (ν := ν) (g := g) (θ0 := θ0) hC
  simpa using (hMeanCont.tendsto.comp hθ)

/-- If `θhat → θ0`, then the population second-moment plug-in converges by continuity. -/
theorem popM2Attr_tendsto_of_theta_tendsto
    {θhat : ℕ → Θ}
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hC : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    Tendsto
      (fun n => popM2Attr ν (g (θhat n)))
      atTop
      (nhds (popM2Attr ν (g θ0))) := by
  have hM2Cont :
      ContinuousAt (fun θ => popM2Attr ν (g θ)) θ0 :=
    m2ContinuousAt_of_FunctionalContinuityAssumptions (ν := ν) (g := g) (θ0 := θ0) hC
  simpa using (hM2Cont.tendsto.comp hθ)

/-- If `θhat → θ0`, then the population variance proxy plug-in converges. -/
theorem popVarAttr_tendsto_of_theta_tendsto
    {θhat : ℕ → Θ}
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hC : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    Tendsto
      (fun n => popVarAttr ν (g (θhat n)))
      atTop
      (nhds (popVarAttr ν (g θ0))) := by
  have hMean :
      Tendsto
        (fun n => popMeanAttr ν (g (θhat n)))
        atTop
        (nhds (popMeanAttr ν (g θ0))) :=
    popMeanAttr_tendsto_of_theta_tendsto (ν := ν) (g := g) (θ0 := θ0) hθ hC

  have hM2 :
      Tendsto
        (fun n => popM2Attr ν (g (θhat n)))
        atTop
        (nhds (popM2Attr ν (g θ0))) :=
    popM2Attr_tendsto_of_theta_tendsto (ν := ν) (g := g) (θ0 := θ0) hθ hC

  have hMeanSq :
      Tendsto
        (fun n => (popMeanAttr ν (g (θhat n))) ^ 2)
        atTop
        (nhds ((popMeanAttr ν (g θ0)) ^ 2)) := by
    simpa [pow_two] using (hMean.mul hMean)

  have hVar :
      Tendsto
        (fun n =>
          popM2Attr ν (g (θhat n)) - (popMeanAttr ν (g (θhat n))) ^ 2)
        atTop
        (nhds (popM2Attr ν (g θ0) - (popMeanAttr ν (g θ0)) ^ 2)) :=
    hM2.sub hMeanSq

  simpa [popVarAttr] using hVar

/-- If `θhat → θ0`, then the population SD plug-in converges (sqrt ∘ var). -/
theorem popSDAttr_tendsto_of_theta_tendsto
    {θhat : ℕ → Θ}
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hC : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    Tendsto
      (fun n => popSDAttr ν (g (θhat n)))
      atTop
      (nhds (popSDAttr ν (g θ0))) := by
  have hVar :
      Tendsto
        (fun n => popVarAttr ν (g (θhat n)))
        atTop
        (nhds (popVarAttr ν (g θ0))) :=
    popVarAttr_tendsto_of_theta_tendsto (ν := ν) (g := g) (θ0 := θ0) hθ hC

  have hsqrt :
      Tendsto Real.sqrt (nhds (popVarAttr ν (g θ0)))
        (nhds (Real.sqrt (popVarAttr ν (g θ0)))) :=
    (Real.continuous_sqrt.continuousAt).tendsto

  simpa [popSDAttr] using (hsqrt.comp hVar)

end

end ConjointSD
