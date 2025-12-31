/-
ConjointSD/SequentialConsistency.lean

Sequential consistency (“m then n”) for the *total SD error*.

We prove:

(1) For any fixed training index m, as evaluation size n → ∞,
      abs ( totalErr(m,n,ω) ) → trainErr(m)     a.e. in ω

(2) As m → ∞, trainErr(m) → 0

(3) Sequential corollary (ε–M–eventually-in-n):
    For any ε>0, ∃ M, ∀ m≥M,  (∀ᵐ ω, ∀ᶠ n, totalErr(m,n,ω) < ε).

No uniformity/joint (m,n) claim.
-/

import Mathlib
import ConjointSD.SampleSplitting
import ConjointSD.EstimatedG
import ConjointSD.RegressionConsistencyBridge
import ConjointSD.Transport

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*} [TopologicalSpace Θ]

/-- Evaluation-stage SD estimator using training index `m` and evaluation size `n`. -/
def sdEst
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (w : Attr → ℝ)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m n : ℕ) (ω : Ω) : ℝ :=
  by
    let _ := μ
    exact
      sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
        (W := Wcomp (A := A) (w := w)) n ω

/-- Oracle target SD under `ν` using the oracle score `g θ0`. -/
def sdOracle
    (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) : ℝ :=
  attrSD ν (g θ0)

/-- Training error at index `m`: SD gap between `gHat m` and oracle `g θ0` under `ν`. -/
def trainErr
    (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m : ℕ) : ℝ :=
  abs (attrSD ν (gHat g θhat m) - sdOracle ν g θ0)

/-- Total error at `(m,n)`: empirical SD gap to oracle SD. -/
def totalErr
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (ν : Measure Attr) (w : Attr → ℝ)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m n : ℕ) (ω : Ω) : ℝ :=
  abs (sdEst μ A w g θhat m n ω - sdOracle ν g θ0)

/--
Step (1): for fixed `m`, as `n → ∞`, total error → training error (a.e.).

Assumes `ν` is the law of `A 0` under `μ` (so we can rewrite the attribute-distribution SD target).
-/
theorem totalErr_tendsto_trainErr_fixed_m
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr)
    (w : Attr → ℝ)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h :
      SplitEvalWeightAssumptions (μ := μ) (A := A) (w := w) (g := g) (θhat := θhat) m)
    (hMom : EvalWeightMatchesAttrMoments (μ := μ) (A := A) (ν := ν)
      (w := w) (s := gHat g θhat m)) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          totalErr μ A ν w g θ0 θhat m n ω)
        atTop
        (nhds (trainErr ν g θ0 θhat m)) := by
  -- Base convergence from SampleSplitting:
  have hBase_map :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) n ω)
          atTop
          (nhds (attrSD ν (gHat g θhat m))) :=
    sdHat_fixed_m_tendsto_ae_attrSD
      (μ := μ) (A := A) (ν := ν) (w := w) (g := g) (θhat := θhat) m h hMom
  -- Rewrite the limit using `hLaw`.
  have hBase :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) n ω)
          atTop
          (nhds (attrSD ν (gHat g θhat m))) := by
    simpa using hBase_map
  -- Continuous mapping: x ↦ abs (x - sdOracle ν g θ0)
  have hcont :
      Continuous (fun x : ℝ => abs (x - sdOracle ν g θ0)) := by
    simpa using (continuous_abs.comp (continuous_id.sub continuous_const))
  refine hBase.mono ?_
  intro ω hω
  have ht :
      Tendsto
        (fun x : ℝ => abs (x - sdOracle ν g θ0))
        (nhds (attrSD ν (gHat g θhat m)))
        (nhds (abs (attrSD ν (gHat g θhat m)
            - sdOracle ν g θ0))) :=
    (hcont.continuousAt.tendsto)
  simpa [totalErr, trainErr, sdOracle, sdEst] using (ht.comp hω)

/--
Step (2): training error → 0 as `m → ∞` under parameter convergence and continuity.
-/
theorem trainErr_tendsto_zero
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : FunctionalContinuityAssumptions (ν := ν) g θ0) :
    Tendsto
      (fun m : ℕ => trainErr ν g θ0 θhat m)
      atTop
      (nhds 0) := by
  let c : ℝ := attrSD ν (g θ0)
  have hmean :
      Tendsto
        (fun n => attrMean ν (gHat g θhat n))
        atTop
        (nhds (attrMean ν (g θ0))) :=
    attrMean_tendsto_of_theta_tendsto
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hθ hCont
  have hm2 :
      Tendsto
        (fun n => attrM2 ν (gHat g θhat n))
        atTop
        (nhds (attrM2 ν (g θ0))) :=
    attrM2_tendsto_of_theta_tendsto
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hθ hCont
  have hBase :
      Tendsto
        (fun m : ℕ => attrSD ν (gHat g θhat m))
        atTop
        (nhds c) := by
    simpa [c] using
      (attrSD_tendsto_of_mean_m2_tendsto
        (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hmean hm2)
  have hcont :
      Continuous (fun x : ℝ => abs (x - c)) := by
    simpa using (continuous_abs.comp (continuous_id.sub continuous_const))
  have h1 :
      Tendsto
        (fun m : ℕ => abs (attrSD ν (gHat g θhat m) - c))
        atTop
        (nhds (abs (c - c))) :=
    (hcont.continuousAt.tendsto).comp hBase
  -- abs (c - c) = 0
  simpa [trainErr, sdOracle, c] using (h1.trans (by simp))

/--
Step (3): sequential ε–M–eventually-in-n consistency (a.e. over ω).

Assumptions:
- `hSplit : ∀ m, SplitEvalWeightAssumptions ... m` gives evaluation-stage conditions for each m.
- `hθ` and `hCont` give convergence of the attribute-distribution SD under `ν`
  for gHat → g θ0 via continuity.

Conclusion:
For any ε>0, ∃ M, ∀ m≥M, (∀ᵐ ω, ∀ᶠ n, totalErr ... m n ω < ε).
-/
theorem sequential_consistency_ae
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (w : Attr → ℝ)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m,
      SplitEvalWeightAssumptions (μ := μ) (A := A) (w := w) (g := g) (θhat := θhat) m)
    (hMom : ∀ m, EvalWeightMatchesAttrMoments (μ := μ) (A := A) (ν := ν)
      (w := w) (s := gHat g θhat m))
    (hθ : Tendsto θhat atTop (nhds θ0))
    (hCont : FunctionalContinuityAssumptions (ν := ν) g θ0)
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in atTop,
            totalErr μ A ν w g θ0 θhat m n ω < ε) := by
  -- training-error convergence
  have hTrain :
      Tendsto (fun m : ℕ => trainErr ν g θ0 θhat m)
        atTop (nhds 0) :=
    trainErr_tendsto_zero
      (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hθ hCont
  -- pick M so that for all m≥M, trainErr m < ε/2
  have hEv :
      ∀ᶠ m : ℕ in atTop,
        trainErr ν g θ0 θhat m < ε / 2 := by
    -- from Tendsto to 0, use the “upper” side of tendsto_order
    have : (0 : ℝ) < ε / 2 := by
      nlinarith [hε.pos]
    exact (tendsto_order.1 hTrain).2 (ε / 2) this
  rcases (eventually_atTop.1 hEv) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hmTrain : trainErr ν g θ0 θhat m < ε / 2 := hM m hm
  have hSum : trainErr ν g θ0 θhat m + ε / 2 < ε := by
    nlinarith [hε.pos]
  -- Step (1) for this m: totalErr(m,n,ω) → trainErr(m) a.e.
  have hTend :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ => totalErr μ A ν w g θ0 θhat m n ω)
          atTop
          (nhds (trainErr ν g θ0 θhat m)) :=
    totalErr_tendsto_trainErr_fixed_m
      (μ := μ) (A := A) (ν := ν) (w := w) (g := g) (θ0 := θ0) (θhat := θhat)
      (m := m) (h := hSplit m) (hMom := hMom m)
  -- Convert pointwise Tendsto into an eventually upper bound trainErr(m) + ε/2, a.e. in ω
  have hEvN :
      ∀ᵐ ω ∂μ,
        ∀ᶠ n : ℕ in atTop,
          totalErr μ A ν w g θ0 θhat m n ω
            < trainErr ν g θ0 θhat m + ε / 2 := by
    refine hTend.mono ?_
    intro ω ht
    have hlt :
        trainErr ν g θ0 θhat m
          < trainErr ν g θ0 θhat m + ε / 2 := by
      nlinarith [hε.pos]
    exact (tendsto_order.1 ht).2
      (trainErr ν g θ0 θhat m + ε / 2) hlt
  -- Strengthen to < ε using trainErr(m) + ε/2 < ε
  refine hEvN.mono ?_
  intro ω hω
  exact hω.mono (fun n hn => lt_trans hn hSum)

end

end ConjointSD
