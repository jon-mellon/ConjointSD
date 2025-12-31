/-
ConjointSD/RegressionEstimator.lean

Minimal formalization of the paper's regression estimator (OLS-style) and a bridge
from estimator consistency to plug-in moment convergence.
-/

import ConjointSD.Assumptions
import ConjointSD.RegressionConsistencyBridge

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section
namespace ConjointSD

universe u v


/--
OLS-style estimator defined via the normal equations: `θhat n = (G n)⁻¹ * c n`.

This is a definitional estimator; the consistency proof assumes entrywise convergence
of `G n` inverse and `c n` to their attribute-distribution counterparts.
-/
def olsThetaHat {Attr : Type u} {Term : Type v} [Fintype Term] [DecidableEq Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ) (n : ℕ) : Term → ℝ :=
  (gramMatrix (A := A) (φ := φ) n)⁻¹.mulVec (crossVec (A := A) (Y := Y) (φ := φ) n)


/--
Consistency of the normal-equation estimator from entrywise convergence of the inverse
Gram matrix and cross moments.
-/
theorem olsThetaHat_tendsto_of_moment_assumptions
    {Attr : Type u} {Term : Type v} [Fintype Term] [DecidableEq Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ) (θ0 : Term → ℝ)
    (h : OLSMomentAssumptions (A := A) (Y := Y) (φ := φ) θ0) :
    Tendsto
      (fun n => olsThetaHat (A := A) (Y := Y) (φ := φ) n)
      atTop
      (nhds θ0) := by
  classical
  have hpoint :
      ∀ i,
        Tendsto
          (fun n =>
            (gramMatrix (A := A) (φ := φ) n)⁻¹.mulVec
              (crossVec (A := A) (Y := Y) (φ := φ) n) i)
          atTop
          (nhds (h.gramInvLimit.mulVec h.crossLimit i)) := by
    intro i
    have hsum :
        Tendsto
          (fun n =>
            ∑ j : Term,
              (gramMatrix (A := A) (φ := φ) n)⁻¹ i j
                * crossVec (A := A) (Y := Y) (φ := φ) n j)
          atTop
          (nhds (∑ j : Term, h.gramInvLimit i j * h.crossLimit j)) := by
      refine tendsto_finset_sum (s := (Finset.univ : Finset Term)) ?_
      intro j hj
      exact (h.gramInv_tendsto i j).mul (h.cross_tendsto j)
    simpa [Matrix.mulVec] using hsum
  have hfun :
      Tendsto
        (fun n =>
          (gramMatrix (A := A) (φ := φ) n)⁻¹.mulVec
            (crossVec (A := A) (Y := Y) (φ := φ) n))
        atTop
        (nhds (h.gramInvLimit.mulVec h.crossLimit)) := by
    refine tendsto_pi_nhds.2 ?_
    intro i
    simpa using hpoint i
  simpa [olsThetaHat, h.theta0_eq] using hfun

/- Definitions and assumption packages live in ConjointSD.Defs / ConjointSD.Assumptions. -/

/-- Convert attribute-distribution moment assumptions to sample-path moment assumptions. -/
def OLSMomentAssumptionsOfAttr.to_OLSMomentAssumptions
    {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term] [DecidableEq Term]
    (ν : Measure Attr)
    (A : ℕ → Attr) (Y : ℕ → ℝ)
    (g : Attr → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ)
    (h : OLSMomentAssumptionsOfAttr (ν := ν) (A := A) (Y := Y) (g := g) (φ := φ) θ0) :
    OLSMomentAssumptions (A := A) (Y := Y) (φ := φ) θ0 :=
  { gramInvLimit := (attrGram (ν := ν) (φ := φ))⁻¹
    crossLimit := attrCross (ν := ν) (g := g) (φ := φ)
    gramInv_tendsto := h.gramInv_tendsto
    cross_tendsto := h.cross_tendsto
    theta0_eq := h.theta0_eq }

theorem olsThetaHat_tendsto_of_attr_moments
    {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term] [DecidableEq Term]
    (ν : Measure Attr)
    (A : ℕ → Attr) (Y : ℕ → ℝ)
    (g : Attr → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ)
    (h : OLSMomentAssumptionsOfAttr (ν := ν) (A := A) (Y := Y) (g := g) (φ := φ) θ0) :
    Tendsto
      (fun n => olsThetaHat (A := A) (Y := Y) (φ := φ) n)
      atTop
      (nhds θ0) :=
  olsThetaHat_tendsto_of_moment_assumptions
    (A := A) (Y := Y) (φ := φ) (θ0 := θ0)
    (h := OLSMomentAssumptionsOfAttr.to_OLSMomentAssumptions
      (ν := ν) (A := A) (Y := Y) (g := g) (φ := φ) (θ0 := θ0) h)

/--
Bridge: if the OLS estimator sequence is consistent and the induced attribute-distribution
functionals are continuous at `θ0`, then the mean/second-moment targets converge.
-/
theorem attrMean_tendsto_of_OLSConsistency
    {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : (Term → ℝ) → Attr → ℝ) (θ0 : Term → ℝ)
    {A : ℕ → Attr} {Y : ℕ → ℝ} {φ : Term → Attr → ℝ}
    (ols : OLSSequence (A := A) (Y := Y) (φ := φ))
    (hCons : Tendsto ols.θhat atTop (nhds θ0))
    (hCont : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    Tendsto
      (fun n => attrMean ν (gHat g ols.θhat n))
      atTop
      (nhds (attrMean ν (g θ0))) :=
  attrMean_tendsto_of_theta_tendsto
    (ν := ν) (g := g) (θ0 := θ0) (θhat := ols.θhat)
    hCons hCont

theorem attrM2_tendsto_of_OLSConsistency
    {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : (Term → ℝ) → Attr → ℝ) (θ0 : Term → ℝ)
    {A : ℕ → Attr} {Y : ℕ → ℝ} {φ : Term → Attr → ℝ}
    (ols : OLSSequence (A := A) (Y := Y) (φ := φ))
    (hCons : Tendsto ols.θhat atTop (nhds θ0))
    (hCont : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    Tendsto
      (fun n => attrM2 ν (gHat g ols.θhat n))
      atTop
      (nhds (attrM2 ν (g θ0))) :=
  attrM2_tendsto_of_theta_tendsto
    (ν := ν) (g := g) (θ0 := θ0) (θhat := ols.θhat)
    hCons hCont

end ConjointSD
