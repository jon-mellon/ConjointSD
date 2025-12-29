/-
ConjointSD/RegressionConsistencyBridge.lean

Route 2 bridge: derive `GEstimationAssumptions` from (i) parameter convergence `θhat → θ0`
and (ii) continuity of the induced population functionals at `θ0`.

This version matches your current `GEstimationAssumptions` interface:
  fields: `mean_tendsto` and `m2_tendsto`.

We do NOT redeclare `popSDAttr_tendsto_of_GEstimationAssumptions` (it already exists in your project).
-/

import ConjointSD.EstimatedG
import ConjointSD.Assumptions
import Mathlib.Topology.Basic

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

/- Definitions and assumption packages live in ConjointSD.Defs / ConjointSD.Assumptions. -/

/--
Main bridge: if θhat → θ0 and the induced mean/second-moment functionals are continuous at θ0,
then `GEstimationAssumptions` holds.
-/
theorem GEstimationAssumptions_of_theta_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (ν := ν) g θ0) :
    GEstimationAssumptions (ν := ν) g θ0 θhat := by
  refine
    { mean_tendsto := ?_
      m2_tendsto   := ?_ }
  · -- mean_tendsto
    simpa [gHat, popMeanΘ] using (hcont.cont_mean.tendsto.comp hθ)
  · -- m2_tendsto
    simpa [gHat, popM2Θ] using (hcont.cont_m2.tendsto.comp hθ)

/--
Derived variance convergence (new name to avoid collisions).

`popVarAttr ν s = popM2Attr ν s - (popMeanAttr ν s)^2`.
So if mean and second moment converge, variance converges.
-/
theorem popVarAttr_tendsto_of_GEstimationAssumptions_bridge
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hG : GEstimationAssumptions (ν := ν) g θ0 θhat) :
    Tendsto
      (fun n => popVarAttr ν (gHat g θhat n))
      atTop
      (nhds (popVarAttr ν (g θ0))) := by
  let _ := (inferInstance : TopologicalSpace Θ)
  have hmean :
      Tendsto
        (fun n => popMeanAttr ν (gHat g θhat n))
        atTop
        (nhds (popMeanAttr ν (g θ0))) :=
    hG.mean_tendsto
  have hm2 :
      Tendsto
        (fun n => popM2Attr ν (gHat g θhat n))
        atTop
        (nhds (popM2Attr ν (g θ0))) :=
    hG.m2_tendsto
  have hmean_sq :
      Tendsto
        (fun n => (popMeanAttr ν (gHat g θhat n)) ^ 2)
        atTop
        (nhds ((popMeanAttr ν (g θ0)) ^ 2)) := by
    -- use continuity of x ↦ x^2
    simpa [pow_two] using (hmean.mul hmean)
  have hsub :
      Tendsto
        (fun n =>
          popM2Attr ν (gHat g θhat n)
            - (popMeanAttr ν (gHat g θhat n)) ^ 2)
        atTop
        (nhds (popM2Attr ν (g θ0) - (popMeanAttr ν (g θ0)) ^ 2)) :=
    hm2.sub hmean_sq
  simpa [popVarAttr] using hsub

/-!
## Blocks: continuity assumptions and resulting `GEstimationAssumptions` per block
-/

/-- Route-2 bridge for blocks: θhat → θ0 plus continuity per block gives
`GEstimationAssumptions` per block. -/
theorem block_GEstimationAssumptions_of_theta_tendsto
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : BlockFunctionalContinuityAssumptions (ν := ν) gB θ0) :
    ∀ b : B, GEstimationAssumptions (ν := ν) (blockScoreΘ (gB := gB) b) θ0 θhat := by
  let _ := (inferInstance : Fintype B)
  intro b
  exact
    GEstimationAssumptions_of_theta_tendsto
      (ν := ν)
      (g := blockScoreΘ (gB := gB) b)
      (θ0 := θ0)
      (θhat := θhat)
      hθ
      (hcont.cont b)

end ConjointSD
