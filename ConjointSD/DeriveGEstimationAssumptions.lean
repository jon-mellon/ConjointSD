/-
ConjointSD/DeriveGEstimationAssumptions.lean

Utilities to eliminate direct moment-convergence assumptions in paper-facing theorems,
by deriving them from:
  (1) θhat → θ0
  (2) continuity-at-θ0 of the attribute-distribution functionals

This file compiles independently and is meant to be imported by your paper wrapper file
(previously `FinalTheorems.lean`).
-/

import ConjointSD.RegressionConsistencyBridge

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

/--
Route-2: derive mean convergence (single score) from `θhat → θ0`
and functional continuity.
-/
theorem derive_mean_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (ν := ν) g θ0) :
    Tendsto
      (fun n => attrMean ν (gHat g θhat n))
      atTop
      (nhds (attrMean ν (g θ0))) :=
  attrMean_tendsto_of_theta_tendsto
    (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hθ hcont

/-- Route-2: derive second-moment convergence (single score) from `θhat → θ0`. -/
theorem derive_m2_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (ν := ν) g θ0) :
    Tendsto
      (fun n => attrM2 ν (gHat g θhat n))
      atTop
      (nhds (attrM2 ν (g θ0))) :=
  attrM2_tendsto_of_theta_tendsto
    (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hθ hcont

/--
Route-2: derive mean convergence for each block score from
`θhat → θ0` and block continuity.
-/
theorem derive_mean_tendsto_blocks
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : BlockFunctionalContinuityAssumptions (ν := ν) gB θ0) :
    ∀ b : B,
      Tendsto
        (fun n => attrMean ν (gHat (blockScoreΘ (gB := gB) b) θhat n))
        atTop
        (nhds (attrMean ν (blockScoreΘ (gB := gB) b θ0))) :=
  block_attrMean_tendsto_of_theta_tendsto
    (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat) hθ hcont

/-- Route-2: derive second-moment convergence for each block score. -/
theorem derive_m2_tendsto_blocks
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : BlockFunctionalContinuityAssumptions (ν := ν) gB θ0) :
    ∀ b : B,
      Tendsto
        (fun n => attrM2 ν (gHat (blockScoreΘ (gB := gB) b) θhat n))
        atTop
        (nhds (attrM2 ν (blockScoreΘ (gB := gB) b θ0))) :=
  block_attrM2_tendsto_of_theta_tendsto
    (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat) hθ hcont

end ConjointSD
