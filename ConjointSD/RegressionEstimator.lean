/-
ConjointSD/RegressionEstimator.lean

Minimal formalization of the paper's regression estimator (OLS-style) and a bridge
from estimator consistency to `GEstimationAssumptions`.
-/

import Mathlib
import ConjointSD.ModelBridge
import ConjointSD.RegressionConsistencyBridge

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section
namespace ConjointSD

universe u v

/--
Empirical squared-loss risk for a linear-in-terms model using the first `n` samples.
The `A` and `Y` sequences are the training attributes/outcomes.
-/
def empiricalRisk {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ)
    (n : ℕ) (β : Term → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (Y i - gLin (β := β) (φ := φ) (A i)) ^ 2

/--
An OLS estimator sequence for the linear-in-terms model: each `θhat n` minimizes
the empirical risk based on the first `n` samples.
-/
structure OLSSequence {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ) : Type (max u v) where
  θhat : ℕ → Term → ℝ
  is_minimizer :
    ∀ n β, empiricalRisk (A := A) (Y := Y) (φ := φ) n (θhat n)
      ≤ empiricalRisk (A := A) (Y := Y) (φ := φ) n β

/--
Assumptions used to prove consistency of the OLS estimator sequence.
This packages the convergence `θhat → θ0`; the remaining statistical conditions
can be discharged for the paper's design in a dedicated instantiation.
-/
structure OLSConsistencyAssumptions {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ) (ols : OLSSequence (A := A) (Y := Y) (φ := φ)) : Prop where
  tendsto_theta : Tendsto ols.θhat atTop (nhds θ0)

/--
Empirical Gram matrix of the feature map for the first `n` samples.
-/
def gramMatrix {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (φ : Term → Attr → ℝ) (n : ℕ) : Matrix Term Term ℝ :=
  fun i j => (1 / (n : ℝ)) * ∑ k : Fin n, φ i (A k) * φ j (A k)

/--
Empirical cross-moment between features and outcomes for the first `n` samples.
-/
def crossVec {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ) (n : ℕ) : Term → ℝ :=
  fun i => (1 / (n : ℝ)) * ∑ k : Fin n, φ i (A k) * Y k

/--
OLS-style estimator defined via the normal equations: `θhat n = (G n)⁻¹ * c n`.

This is a definitional estimator; the consistency proof assumes entrywise convergence
of `G n` inverse and `c n` to their population counterparts.
-/
def olsThetaHat {Attr : Type u} {Term : Type v} [Fintype Term] [DecidableEq Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ) (n : ℕ) : Term → ℝ :=
  (gramMatrix (A := A) (φ := φ) n)⁻¹.mulVec (crossVec (A := A) (Y := Y) (φ := φ) n)

structure OLSMomentAssumptions {Attr : Type u} {Term : Type v}
    [Fintype Term] [DecidableEq Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ) : Type (max u v) where
  gramInvLimit : Matrix Term Term ℝ
  crossLimit : Term → ℝ
  gramInv_tendsto :
    ∀ i j,
      Tendsto
        (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j)
        atTop
        (nhds (gramInvLimit i j))
  cross_tendsto :
    ∀ i,
      Tendsto
        (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i)
        atTop
        (nhds (crossLimit i))
  theta0_eq : θ0 = gramInvLimit.mulVec crossLimit

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

/--
Population Gram matrix of the feature map under a target attribute distribution `ν`.
-/
def popGram {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (ν : Measure Attr) (φ : Term → Attr → ℝ) : Matrix Term Term ℝ :=
  fun i j => popMeanAttr ν (fun a => φ i a * φ j a)

/--
Population cross moment between features and a true outcome score `g` under `ν`.
-/
def popCross {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (ν : Measure Attr) (g : Attr → ℝ) (φ : Term → Attr → ℝ) : Term → ℝ :=
  fun i => popMeanAttr ν (fun a => φ i a * g a)

/--
Moment assumptions stated against the population Gram/cross moments.
These encode the LLN and identifiability conditions typically used for OLS consistency.
-/
structure OLSMomentAssumptionsOfPop {Attr : Type u} {Term : Type v}
    [MeasurableSpace Attr] [Fintype Term] [DecidableEq Term]
    (ν : Measure Attr)
    (A : ℕ → Attr) (Y : ℕ → ℝ)
    (g : Attr → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ) : Prop where
  gramInv_tendsto :
    ∀ i j,
      Tendsto
        (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j)
        atTop
        (nhds ((popGram (ν := ν) (φ := φ))⁻¹ i j))
  cross_tendsto :
    ∀ i,
      Tendsto
        (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i)
        atTop
        (nhds (popCross (ν := ν) (g := g) (φ := φ) i))
  theta0_eq :
    θ0 = (popGram (ν := ν) (φ := φ))⁻¹.mulVec (popCross (ν := ν) (g := g) (φ := φ))

def OLSMomentAssumptionsOfPop.to_OLSMomentAssumptions
    {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term] [DecidableEq Term]
    (ν : Measure Attr)
    (A : ℕ → Attr) (Y : ℕ → ℝ)
    (g : Attr → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ)
    (h : OLSMomentAssumptionsOfPop (ν := ν) (A := A) (Y := Y) (g := g) (φ := φ) θ0) :
    OLSMomentAssumptions (A := A) (Y := Y) (φ := φ) θ0 :=
  { gramInvLimit := (popGram (ν := ν) (φ := φ))⁻¹
    crossLimit := popCross (ν := ν) (g := g) (φ := φ)
    gramInv_tendsto := h.gramInv_tendsto
    cross_tendsto := h.cross_tendsto
    theta0_eq := h.theta0_eq }

theorem olsThetaHat_tendsto_of_pop_moments
    {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term] [DecidableEq Term]
    (ν : Measure Attr)
    (A : ℕ → Attr) (Y : ℕ → ℝ)
    (g : Attr → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ)
    (h : OLSMomentAssumptionsOfPop (ν := ν) (A := A) (Y := Y) (g := g) (φ := φ) θ0) :
    Tendsto
      (fun n => olsThetaHat (A := A) (Y := Y) (φ := φ) n)
      atTop
      (nhds θ0) :=
  olsThetaHat_tendsto_of_moment_assumptions
    (A := A) (Y := Y) (φ := φ) (θ0 := θ0)
    (h := OLSMomentAssumptionsOfPop.to_OLSMomentAssumptions
      (ν := ν) (A := A) (Y := Y) (g := g) (φ := φ) (θ0 := θ0) h)

/--
Bridge: if the OLS estimator sequence is consistent and the induced population
functionals are continuous at `θ0`, then `GEstimationAssumptions` holds.
-/
theorem GEstimationAssumptions_of_OLSConsistency
    {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (g : (Term → ℝ) → Attr → ℝ) (θ0 : Term → ℝ)
    {A : ℕ → Attr} {Y : ℕ → ℝ} {φ : Term → Attr → ℝ}
    (ols : OLSSequence (A := A) (Y := Y) (φ := φ))
    (hCons : OLSConsistencyAssumptions (A := A) (Y := Y) (φ := φ) θ0 ols)
    (hCont : FunctionalContinuityAssumptions (ν := ν) (g := g) θ0) :
    GEstimationAssumptions (ν := ν) g θ0 ols.θhat :=
  GEstimationAssumptions_of_theta_tendsto
    (ν := ν) (g := g) (θ0 := θ0) (θhat := ols.θhat)
    hCons.tendsto_theta hCont

end ConjointSD
