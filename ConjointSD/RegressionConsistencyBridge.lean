/-
ConjointSD/RegressionConsistencyBridge.lean

Route 2 bridge: derive attribute-distribution moment convergence from
(i) parameter convergence `θhat → θ0` and (ii) continuity of the induced
functionals at `θ0`.
-/

import ConjointSD.EstimatedG
import ConjointSD.Assumptions
import Mathlib.Topology.Basic

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

/- Definitions live in ConjointSD.Defs / ConjointSD.Assumptions. -/

/-- Mean convergence under θhat → θ0 and continuity of the mean functional. -/
theorem attrMean_tendsto_of_theta_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (ν := ν) g θ0) :
    Tendsto
      (fun n => attrMean ν (gHat g θhat n))
      atTop
      (nhds (attrMean ν (g θ0))) := by
  simpa [gHat, attrMeanΘ] using (hcont.cont_mean.tendsto.comp hθ)

/- Second-moment convergence under θhat → θ0 and continuity of the m2 functional. -/
theorem attrM2_tendsto_of_theta_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (ν := ν) g θ0) :
    Tendsto
      (fun n => attrM2 ν (gHat g θhat n))
      atTop
      (nhds (attrM2 ν (g θ0))) := by
  simpa [gHat, attrM2Θ] using (hcont.cont_m2.tendsto.comp hθ)

/-!
## Blocks: continuity assumptions and resulting moment convergence per block
-/

/-- Route-2 bridge for blocks: θhat → θ0 plus continuity per block gives
mean convergence per block. -/
theorem block_attrMean_tendsto_of_theta_tendsto
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : BlockFunctionalContinuityAssumptions (ν := ν) gB θ0) :
    ∀ b : B,
      Tendsto
        (fun n => attrMean ν (gHat (blockScoreΘ (gB := gB) b) θhat n))
        atTop
        (nhds (attrMean ν (blockScoreΘ (gB := gB) b θ0))) := by
  let _ := (inferInstance : Fintype B)
  intro b
  exact
    attrMean_tendsto_of_theta_tendsto
      (ν := ν)
      (g := blockScoreΘ (gB := gB) b)
      (θ0 := θ0)
      (θhat := θhat)
      hθ
      (hcont.cont b)

theorem block_attrM2_tendsto_of_theta_tendsto
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : BlockFunctionalContinuityAssumptions (ν := ν) gB θ0) :
    ∀ b : B,
      Tendsto
        (fun n => attrM2 ν (gHat (blockScoreΘ (gB := gB) b) θhat n))
        atTop
        (nhds (attrM2 ν (blockScoreΘ (gB := gB) b θ0))) := by
  let _ := (inferInstance : Fintype B)
  intro b
  exact
    attrM2_tendsto_of_theta_tendsto
      (ν := ν)
      (g := blockScoreΘ (gB := gB) b)
      (θ0 := θ0)
      (θhat := θhat)
      hθ
      (hcont.cont b)

end ConjointSD
