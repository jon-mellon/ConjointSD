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
import ConjointSD.DecompositionSequentialConsistency

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
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (xiAttr := xiAttr) g θ0) :
    Tendsto
      (fun n => attrMean xiAttr (gHat g θhat n))
      atTop
      (nhds (attrMean xiAttr (g θ0))) :=
  attrMean_tendsto_of_theta_tendsto
    (xiAttr := xiAttr) (g := g) (θ0 := θ0) (θhat := θhat) hθ hcont

/-- Route-2: derive second-moment convergence (single score) from `θhat → θ0`. -/
theorem derive_m2_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (xiAttr := xiAttr) g θ0) :
    Tendsto
      (fun n => attrM2 xiAttr (gHat g θhat n))
      atTop
      (nhds (attrM2 xiAttr (g θ0))) :=
  attrM2_tendsto_of_theta_tendsto
    (xiAttr := xiAttr) (g := g) (θ0 := θ0) (θhat := θhat) hθ hcont

/-!
## Bundled plug-in assumptions from θhat → θ0
-/

/-- Bundle mean + second-moment convergence into `PlugInMomentAssumptions`. -/
theorem plugInMomentAssumptions_of_theta_tendsto
    {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : FunctionalContinuityAssumptions (xiAttr := xiAttr) g θ0) :
    PlugInMomentAssumptions (ν := xiAttr) (g := g) (θ0 := θ0) (θhat := θhat) :=
  ⟨
    attrMean_tendsto_of_theta_tendsto
      (xiAttr := xiAttr) (g := g) (θ0 := θ0) (θhat := θhat) hθ hcont,
    attrM2_tendsto_of_theta_tendsto
      (xiAttr := xiAttr) (g := g) (θ0 := θ0) (θhat := θhat) hθ hcont
  ⟩

/--
Route-2: derive mean convergence for each block score from
`θhat → θ0` and block continuity.
-/
theorem derive_mean_tendsto_blocks
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : BlockFunctionalContinuityAssumptions (xiAttr := xiAttr) gB θ0) :
    ∀ b : B,
      Tendsto
        (fun n => attrMean xiAttr (gHat (blockScoreΘ (gB := gB) b) θhat n))
        atTop
        (nhds (attrMean xiAttr (blockScoreΘ (gB := gB) b θ0))) :=
by
  intro b
  exact
    attrMean_tendsto_of_theta_tendsto
      (xiAttr := xiAttr)
      (g := blockScoreΘ (gB := gB) b)
      (θ0 := θ0)
      (θhat := θhat)
      hθ
      (hcont.cont b)

/-- Route-2: derive second-moment convergence for each block score. -/
theorem derive_m2_tendsto_blocks
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : BlockFunctionalContinuityAssumptions (xiAttr := xiAttr) gB θ0) :
    ∀ b : B,
      Tendsto
        (fun n => attrM2 xiAttr (gHat (blockScoreΘ (gB := gB) b) θhat n))
        atTop
        (nhds (attrM2 xiAttr (blockScoreΘ (gB := gB) b θ0))) :=
by
  intro b
  exact
    attrM2_tendsto_of_theta_tendsto
      (xiAttr := xiAttr)
      (g := blockScoreΘ (gB := gB) b)
      (θ0 := θ0)
      (θhat := θhat)
      hθ
      (hcont.cont b)

/-- Bundle blockwise mean + second-moment convergence into `PlugInMomentAssumptions`. -/
theorem plugInMomentAssumptions_blocks_of_theta_tendsto
    {Attr Θ B : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ] [Fintype B]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (gB : B → Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hcont : BlockFunctionalContinuityAssumptions (xiAttr := xiAttr) gB θ0) :
    ∀ b : B,
      PlugInMomentAssumptions
        (ν := xiAttr)
        (g := gBlock (gB := gB) b) (θ0 := θ0) (θhat := θhat) := by
  intro b
  refine
    plugInMomentAssumptions_of_theta_tendsto
      (xiAttr := xiAttr)
      (g := gBlock (gB := gB) b)
      (θ0 := θ0) (θhat := θhat)
      hθ
      ?_
  simpa [gBlock] using hcont.cont b

end ConjointSD
