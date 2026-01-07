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


theorem olsThetaHat_tendsto_of_attr_moments
    {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term] [DecidableEq Term]
    (xiAttr : Measure Attr)
    (A : ℕ → Attr) (Y : ℕ → ℝ)
    (g : Attr → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ)
    (hGramInv :
      ∀ i j,
        Tendsto
          (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j)
          atTop
          (nhds ((attrGram (xiAttr := xiAttr) (φ := φ))⁻¹ i j)))
    (hCross :
      ∀ i,
        Tendsto
          (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i)
          atTop
          (nhds (attrCross (xiAttr := xiAttr) (g := g) (φ := φ) i)))
    (hId :
      θ0 =
        (attrGram (xiAttr := xiAttr) (φ := φ))⁻¹.mulVec
          (attrCross (xiAttr := xiAttr) (g := g) (φ := φ))) :
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
          (nhds
            (((attrGram (xiAttr := xiAttr) (φ := φ))⁻¹.mulVec
              (attrCross (xiAttr := xiAttr) (g := g) (φ := φ))) i)) := by
    intro i
    have hsum :
        Tendsto
          (fun n =>
            ∑ j : Term,
              (gramMatrix (A := A) (φ := φ) n)⁻¹ i j
                * crossVec (A := A) (Y := Y) (φ := φ) n j)
          atTop
          (nhds
            (∑ j : Term,
              ((attrGram (xiAttr := xiAttr) (φ := φ))⁻¹ i j)
                * (attrCross (xiAttr := xiAttr) (g := g) (φ := φ) j))) := by
      refine tendsto_finset_sum (s := (Finset.univ : Finset Term)) ?_
      intro j hj
      exact (hGramInv i j).mul (hCross j)
    simpa [Matrix.mulVec] using hsum
  have hfun :
      Tendsto
        (fun n =>
          (gramMatrix (A := A) (φ := φ) n)⁻¹.mulVec
            (crossVec (A := A) (Y := Y) (φ := φ) n))
        atTop
        (nhds
          ((attrGram (xiAttr := xiAttr) (φ := φ))⁻¹.mulVec
            (attrCross (xiAttr := xiAttr) (g := g) (φ := φ)))) := by
    refine tendsto_pi_nhds.2 ?_
    intro i
    simpa using hpoint i
  simpa [olsThetaHat, hId] using hfun

end ConjointSD
