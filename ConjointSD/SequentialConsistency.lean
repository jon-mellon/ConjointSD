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
import ConjointSD.Transport

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/-- Evaluation-stage SD estimator using training index `m` and evaluation size `n`. -/
def sdEst
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m n : ℕ) (ω : Ω) : ℝ :=
  by
    let _ := μ
    exact sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω

/-- Oracle target SD under `ν` using the oracle score `g θ0`. -/
def sdOracle
    (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) : ℝ :=
  popSDAttr ν (g θ0)

/-- Training error at index `m`: SD gap between `gHat m` and oracle `g θ0` under `ν`. -/
def trainErr
    (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m : ℕ) : ℝ :=
  abs (popSDAttr ν (gHat g θhat m) - sdOracle ν g θ0)

/-- Total error at `(m,n)`: empirical SD gap to oracle SD. -/
def totalErr
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m n : ℕ) (ω : Ω) : ℝ :=
  abs (sdEst μ A g θhat m n ω - sdOracle ν g θ0)

/--
Step (1): for fixed `m`, as `n → ∞`, total error → training error (a.e.).

Assumes `ν` is the law of `A 0` under `μ` (so we can rewrite the population SD target).
-/
theorem totalErr_tendsto_trainErr_fixed_m
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (hLaw : Measure.map (A 0) μ = ν)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h :
      SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => totalErr μ A ν g θ0 θhat m n ω)
        atTop
        (nhds (trainErr ν g θ0 θhat m)) := by
  -- Base convergence from SampleSplitting:
  have hBase_map :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
          atTop
          (nhds (popSDAttr (Measure.map (A 0) μ) (gHat g θhat m))) :=
    sdHat_fixed_m_tendsto_ae_popSDAttr (μ := μ) (A := A) (g := g) (θhat := θhat) m h
  -- Rewrite the limit using `hLaw`.
  have hBase :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
          atTop
          (nhds (popSDAttr ν (gHat g θhat m))) := by
    simpa [hLaw] using hBase_map
  -- Continuous mapping: x ↦ abs (x - sdOracle ν g θ0)
  have hcont :
      Continuous (fun x : ℝ => abs (x - sdOracle ν g θ0)) := by
    simpa using (continuous_abs.comp (continuous_id.sub continuous_const))
  refine hBase.mono ?_
  intro ω hω
  have ht :
      Tendsto
        (fun x : ℝ => abs (x - sdOracle ν g θ0))
        (nhds (popSDAttr ν (gHat g θhat m)))
        (nhds (abs (popSDAttr ν (gHat g θhat m) - sdOracle ν g θ0))) :=
    (hcont.continuousAt.tendsto)
  simpa [totalErr, trainErr, sdOracle, sdEst] using (ht.comp hω)

theorem totalErr_tendsto_trainErr_fixed_m_of_bounded
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (hLaw : Measure.map (A 0) μ = ν)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h :
      SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := g) (θhat := θhat) m) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => totalErr μ A ν g θ0 θhat m n ω)
        atTop
        (nhds (trainErr ν g θ0 θhat m)) := by
  have h' :
      SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m :=
    splitEvalAssumptions_of_bounded
      (μ := μ) (A := A) (g := g) (θhat := θhat) (m := m) h
  simpa using
    totalErr_tendsto_trainErr_fixed_m
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw) (g := g) (θ0 := θ0) (θhat := θhat)
      (m := m) (h := h')
/--
Step (2): training error → 0 as `m → ∞` under `GEstimationAssumptions` for `ν`.
-/
theorem trainErr_tendsto_zero
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hG :
      GEstimationAssumptions (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat)) :
    Tendsto
      (fun m : ℕ => trainErr ν g θ0 θhat m)
      atTop
      (nhds 0) := by
  let c : ℝ := popSDAttr ν (g θ0)
  have hBase :
      Tendsto
        (fun m : ℕ => popSDAttr ν (gHat g θhat m))
        atTop
        (nhds c) := by
    simpa [c] using
      (popSDAttr_tendsto_of_GEstimationAssumptions
        (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hG)
  have hcont :
      Continuous (fun x : ℝ => abs (x - c)) := by
    simpa using (continuous_abs.comp (continuous_id.sub continuous_const))
  have h1 :
      Tendsto
        (fun m : ℕ => abs (popSDAttr ν (gHat g θhat m) - c))
        atTop
        (nhds (abs (c - c))) :=
    (hcont.continuousAt.tendsto).comp hBase
  -- abs (c - c) = 0
  simpa [trainErr, sdOracle, c] using (h1.trans (by simp))

/--
Step (3): sequential ε–M–eventually-in-n consistency (a.e. over ω).

Assumptions:
- `hSplit : ∀ m, SplitEvalAssumptions ... m` gives evaluation-stage conditions for each m.
- `hLaw : Measure.map (A 0) μ = ν` identifies ν with the evaluation attribute law.
- `hG` gives convergence of the population SD under ν for gHat → g θ0.

Conclusion:
For any ε>0, ∃ M, ∀ m≥M, (∀ᵐ ω, ∀ᶠ n, totalErr ... m n ω < ε).
-/
theorem sequential_consistency_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (hLaw : Measure.map (A 0) μ = ν)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m, SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m)
    (hG : GEstimationAssumptions (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, totalErr μ A ν g θ0 θhat m n ω < ε) := by
  -- training-error convergence
  have hTrain : Tendsto (fun m : ℕ => trainErr ν g θ0 θhat m) atTop (nhds 0) :=
    trainErr_tendsto_zero (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat) hG
  -- pick M so that for all m≥M, trainErr m < ε/2
  have hEv :
      ∀ᶠ m : ℕ in atTop, trainErr ν g θ0 θhat m < ε / 2 := by
    -- from Tendsto to 0, use the “upper” side of tendsto_order
    have : (0 : ℝ) < ε / 2 := by
      nlinarith
    exact (tendsto_order.1 hTrain).2 (ε / 2) this
  rcases (eventually_atTop.1 hEv) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hmTrain : trainErr ν g θ0 θhat m < ε / 2 := hM m hm
  have hSum : trainErr ν g θ0 θhat m + ε / 2 < ε := by
    nlinarith
  -- Step (1) for this m: totalErr(m,n,ω) → trainErr(m) a.e.
  have hTend :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ => totalErr μ A ν g θ0 θhat m n ω)
          atTop
          (nhds (trainErr ν g θ0 θhat m)) :=
    totalErr_tendsto_trainErr_fixed_m
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw) (g := g) (θ0 := θ0) (θhat := θhat)
      (m := m) (h := hSplit m)
  -- Convert pointwise Tendsto into an eventually upper bound trainErr(m) + ε/2, a.e. in ω
  have hEvN :
      ∀ᵐ ω ∂μ,
        ∀ᶠ n : ℕ in atTop,
          totalErr μ A ν g θ0 θhat m n ω < trainErr ν g θ0 θhat m + ε / 2 := by
    refine hTend.mono ?_
    intro ω ht
    have hlt : trainErr ν g θ0 θhat m < trainErr ν g θ0 θhat m + ε / 2 := by
      nlinarith [hε]
    exact (tendsto_order.1 ht).2 (trainErr ν g θ0 θhat m + ε / 2) hlt
  -- Strengthen to < ε using trainErr(m) + ε/2 < ε
  refine hEvN.mono ?_
  intro ω hω
  exact hω.mono (fun n hn => lt_trans hn hSum)

theorem sequential_consistency_ae_of_bounded
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr) [IsProbabilityMeasure ν]
    (hLaw : Measure.map (A 0) μ = ν)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m, SplitEvalAssumptionsBounded (μ := μ) (A := A) (g := g) (θhat := θhat) m)
    (hG : GEstimationAssumptions (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, totalErr μ A ν g θ0 θhat m n ω < ε) := by
  have hSplit' :
      ∀ m, SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m :=
    fun m =>
      splitEvalAssumptions_of_bounded
        (μ := μ) (A := A) (g := g) (θhat := θhat) (m := m) (hSplit m)
  exact
    sequential_consistency_ae
      (μ := μ) (A := A) (ν := ν) (hLaw := hLaw) (g := g) (θ0 := θ0) (θhat := θhat)
      (hSplit := hSplit') (hG := hG) (ε := ε) (hε := hε)

end

end ConjointSD
