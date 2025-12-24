import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

/-!
# Transport (population prediction) layer

This file introduces:

1) A *population* probability measure `ν` on the attribute space `Attr`.
2) A *design* (conjoint profile) probability measure `π` on `Attr` (optional but useful).
3) Formal “overlap / support” assumptions between `ν` and `π`.
4) Formal “invariance” (a.k.a. external validity / stability) assumptions connecting an
   experiment-identified status function to the population status function.
5) Target population mean/variance/SD estimands as integrals under `ν`.
-/

variable {Attr : Type*} [MeasurableSpace Attr]

/-- Population mean of a score function `s : Attr → ℝ` under `ν`. -/
def popMeanAttr (ν : Measure Attr) (s : Attr → ℝ) : ℝ :=
  ∫ a, s a ∂ν

/-- Population second moment of a score function `s` under `ν`. -/
def popM2Attr (ν : Measure Attr) (s : Attr → ℝ) : ℝ :=
  ∫ a, (s a) ^ 2 ∂ν

/-- Population variance via `E[s^2] - (E[s])^2` under `ν`. -/
def popVarAttr (ν : Measure Attr) (s : Attr → ℝ) : ℝ :=
  popM2Attr (ν := ν) s - (popMeanAttr (ν := ν) s) ^ 2

/-- Population SD under `ν` (square root of `popVarAttr`). -/
def popSDAttr (ν : Measure Attr) (s : Attr → ℝ) : ℝ :=
  Real.sqrt (popVarAttr (ν := ν) s)

/-- Convenient moment conditions on `s` under a population measure `ν`. -/
structure PopulationMomentAssumptions (ν : Measure Attr) (s : Attr → ℝ) : Prop where
  int1 : Integrable s ν
  int2 : Integrable (fun a => (s a) ^ 2) ν

/--
Overlap/support condition between a population distribution `ν` and a design distribution `π`.

`ν ≪ π` means: any set of attribute profiles that is impossible under the design is also
impossible in the population (support of `ν` is contained in support of `π`).
-/
structure Overlap (ν π : Measure Attr) : Prop where
  absCont : ν ≪ π

/--
Pointwise invariance: the experiment-identified score `gExp` equals the population score `gPop`
for *all* attribute profiles.
-/
def Invariance (gExp gPop : Attr → ℝ) : Prop :=
  ∀ x, gExp x = gPop x

/--
Invariance only on population support (AE under `ν`): `gExp = gPop` holds `ν`-almost everywhere.
This is often the right minimal transport condition.
-/
def InvarianceAE (ν : Measure Attr) (gExp gPop : Attr → ℝ) : Prop :=
  ∀ᵐ x ∂ν, gExp x = gPop x

/--
Transport assumptions bundling:
- population distribution `ν` (probability measure),
- design distribution `π` (probability measure),
- overlap `ν ≪ π`,
- invariance on population support.

This is stated without yet connecting `gExp` to your Step (1) identification file; that comes next.
-/
structure TransportAssumptions
    (ν π : Measure Attr)
    (gExp gPop : Attr → ℝ) : Prop where
  popProb : IsProbabilityMeasure ν
  desProb : IsProbabilityMeasure π
  overlap : Overlap ν π
  invariance : InvarianceAE (ν := ν) gExp gPop

/-!
## The target population dispersion estimand

Given a *population* distribution `ν` over attributes and a score function `s : Attr → ℝ`
(typically the status function learned/identified from the conjoint), the target estimands are:

- `popMeanAttr ν s`
- `popVarAttr  ν s`
- `popSDAttr   ν s`

All are defined as integrals w.r.t. `ν`.
-/

end ConjointSD
