/-
ConjointSD/DeriveGEstimationAssumptions.lean

Utilities to eliminate the Route-1 assumption
  hG : ∀ b, GEstimationAssumptions …
from paper-facing theorems, by deriving it from:
  (1) θhat → θ0
  (2) continuity-at-θ0 of the population functionals

This file compiles independently and is meant to be imported by your paper wrapper file
(previously `FinalTheorems.lean`).
-/

import ConjointSD.RegressionConsistencyBridge

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

/--
Route-2: derive `GEstimationAssumptions` (single score) from `θhat → θ0`
and functional continuity.
-/
theorem derive_hG
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : ThetaTendstoAssumptions (θhat := θhat) (θ0 := θ0))
    (hcont : FunctionalContinuityAssumptions (ν := ν) g θ0) :
    GEstimationAssumptions (ν := ν) g θ0 θhat :=
  GEstimationAssumptions_of_theta_tendsto
    (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hθ hcont

/--
Route-2: derive `∀ b, GEstimationAssumptions …` for block scores from
`θhat → θ0` and block continuity.
-/
theorem derive_hG_blocks
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : ThetaTendstoAssumptions (θhat := θhat) (θ0 := θ0))
    (hcont : BlockFunctionalContinuityAssumptions (ν := ν) gB θ0) :
    ∀ b : B, GEstimationAssumptions (ν := ν) (blockScoreΘ (gB := gB) b) θ0 θhat :=
  block_GEstimationAssumptions_of_theta_tendsto
    (ν := ν) (gB := gB) (θ0 := θ0) (θhat := θhat) hθ hcont

end ConjointSD
