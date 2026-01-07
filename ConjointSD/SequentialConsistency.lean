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
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m n : ℕ) (ω : Ω) : ℝ :=
  by
    let _ := ρ
    exact
      sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω

/-- Oracle target SD under `ν_pop` using the oracle score `g θ0`. -/
def sdOracle
    (ν_pop : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) : ℝ :=
  attrSD ν_pop (g θ0)

/-- Training error at index `m`: SD gap between `gHat m` and oracle `g θ0` under `ν_pop`. -/
def trainErr
    (ν_pop : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m : ℕ) : ℝ :=
  abs (attrSD ν_pop (gHat g θhat m) - sdOracle ν_pop g θ0)

/-- Total error at `(m,n)`: empirical SD gap to oracle SD. -/
def totalErr
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (ν_pop : Measure Attr)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m n : ℕ) (ω : Ω) : ℝ :=
  abs (sdEst ρ A g θhat m n ω - sdOracle ν_pop g θ0)

/--
Step (1): for fixed `m`, as `n → ∞`, total error → training error (a.e.).

Assumes the evaluation attribute law equals the target-population law `ν_pop`.
-/
theorem totalErr_tendsto_trainErr_fixed_m
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (A : ℕ → Ω → Attr)
    (ν_pop : Measure Attr)
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h :
      SplitEvalAssumptionsBounded (ρ := ρ) (A := A) (g := g) (θhat := θhat) m)
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν_pop := ν_pop)) :
    ∀ᵐ ω ∂ρ,
      Tendsto
        (fun n : ℕ =>
          totalErr ρ A ν_pop g θ0 θhat m n ω)
        atTop
        (nhds (trainErr ν_pop g θ0 θhat m)) := by
  -- Base convergence from SampleSplitting:
  have hBase_map :
      ∀ᵐ ω ∂ρ,
        Tendsto
          (fun n : ℕ =>
            sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
          atTop
          (nhds (attrSD ν_pop (gHat g θhat m))) :=
    sdHat_fixed_m_tendsto_ae_attrSD
      (ρ := ρ) (A := A) (ν_pop := ν_pop) (g := g) (θhat := θhat) m h hLaw
  -- Rewrite the limit using `hLaw`.
  have hBase :
      ∀ᵐ ω ∂ρ,
        Tendsto
          (fun n : ℕ =>
            sdHatZ (Z := Zcomp (A := A) (g := gHat g θhat m)) n ω)
          atTop
          (nhds (attrSD ν_pop (gHat g θhat m))) := by
    simpa using hBase_map
  -- Continuous mapping: x ↦ abs (x - sdOracle ν_pop g θ0)
  have hcont :
      Continuous (fun x : ℝ => abs (x - sdOracle ν_pop g θ0)) := by
    simpa using (continuous_abs.comp (continuous_id.sub continuous_const))
  refine hBase.mono ?_
  intro ω hω
  have ht :
      Tendsto
        (fun x : ℝ => abs (x - sdOracle ν_pop g θ0))
        (nhds (attrSD ν_pop (gHat g θhat m)))
        (nhds (abs (attrSD ν_pop (gHat g θhat m)
            - sdOracle ν_pop g θ0))) :=
    (hcont.continuousAt.tendsto)
  simpa [totalErr, trainErr, sdOracle, sdEst] using (ht.comp hω)

/--
Step (2): training error → 0 as `m → ∞` under direct mean/m2 convergence.
-/
theorem trainErr_tendsto_zero
    (ν_pop : Measure Attr) [IsProbabilityMeasure ν_pop]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hMean : Tendsto (fun m => attrMean ν_pop (gHat g θhat m)) atTop
      (nhds (attrMean ν_pop (g θ0))))
    (hM2 : Tendsto (fun m => attrM2 ν_pop (gHat g θhat m)) atTop
      (nhds (attrM2 ν_pop (g θ0)))) :
    Tendsto
      (fun m : ℕ => trainErr ν_pop g θ0 θhat m)
      atTop
      (nhds 0) := by
  let c : ℝ := attrSD ν_pop (g θ0)
  have hBase :
      Tendsto
        (fun m : ℕ => attrSD ν_pop (gHat g θhat m))
        atTop
        (nhds c) := by
    simpa [c] using
      (attrSD_tendsto_of_mean_m2_tendsto
        (ν_pop := ν_pop) (g := g) (θ0 := θ0) (θhat := θhat)
        hMean hM2)
  have hcont :
      Continuous (fun x : ℝ => abs (x - c)) := by
    simpa using (continuous_abs.comp (continuous_id.sub continuous_const))
  have h1 :
      Tendsto
        (fun m : ℕ => abs (attrSD ν_pop (gHat g θhat m) - c))
        atTop
        (nhds (abs (c - c))) :=
    (hcont.continuousAt.tendsto).comp hBase
  -- abs (c - c) = 0
  simpa [trainErr, sdOracle, c] using (h1.trans (by simp))

/--
Step (3): sequential ε–M–eventually-in-n consistency (a.e. over ω).

Assumptions:
- `hSplit : ∀ m, SplitEvalAssumptionsBounded ... m` gives evaluation-stage
  conditions for each m.
- `hMean` / `hM2` give direct mean and second-moment convergence under `ν_pop`.

Conclusion:
For any ε>0, ∃ M, ∀ m≥M, (∀ᵐ ω, ∀ᶠ n, totalErr ... m n ω < ε).
-/
theorem sequential_consistency_ae
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (A : ℕ → Ω → Attr)
    (ν_pop : Measure Attr) [IsProbabilityMeasure ν_pop]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ)
    (hSplit : ∀ m,
      SplitEvalAssumptionsBounded
        (ρ := ρ) (A := A) (g := g) (θhat := θhat) m)
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν_pop := ν_pop))
    (hMean : Tendsto (fun m => attrMean ν_pop (gHat g θhat m)) atTop
      (nhds (attrMean ν_pop (g θ0))))
    (hM2 : Tendsto (fun m => attrM2 ν_pop (gHat g θhat m)) atTop
      (nhds (attrM2 ν_pop (g θ0))))
    (ε : ℝ) (hε : EpsilonAssumptions ε) :
    ∃ M : ℕ,
      ∀ m ≥ M,
        (∀ᵐ ω ∂ρ,
          ∀ᶠ n : ℕ in atTop,
            totalErr ρ A ν_pop g θ0 θhat m n ω < ε) := by
  -- training-error convergence
  have hTrain :
      Tendsto (fun m : ℕ => trainErr ν_pop g θ0 θhat m)
        atTop (nhds 0) :=
    trainErr_tendsto_zero
      (ν_pop := ν_pop) (g := g) (θ0 := θ0) (θhat := θhat) hMean hM2
  -- pick M so that for all m≥M, trainErr m < ε/2
  have hEv :
      ∀ᶠ m : ℕ in atTop,
        trainErr ν_pop g θ0 θhat m < ε / 2 := by
    -- from Tendsto to 0, use the “upper” side of tendsto_order
    have : (0 : ℝ) < ε / 2 := by
      nlinarith [hε.pos]
    exact (tendsto_order.1 hTrain).2 (ε / 2) this
  rcases (eventually_atTop.1 hEv) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hmTrain : trainErr ν_pop g θ0 θhat m < ε / 2 := hM m hm
  have hSum : trainErr ν_pop g θ0 θhat m + ε / 2 < ε := by
    nlinarith [hε.pos]
  -- Step (1) for this m: totalErr(m,n,ω) → trainErr(m) a.e.
  have hTend :
      ∀ᵐ ω ∂ρ,
        Tendsto
          (fun n : ℕ => totalErr ρ A ν_pop g θ0 θhat m n ω)
          atTop
          (nhds (trainErr ν_pop g θ0 θhat m)) :=
    totalErr_tendsto_trainErr_fixed_m
      (ρ := ρ) (A := A) (ν_pop := ν_pop) (g := g) (θ0 := θ0) (θhat := θhat)
      (m := m) (h := hSplit m) (hLaw := hLaw)
  -- Convert pointwise Tendsto into an eventually upper bound trainErr(m) + ε/2, a.e. in ω
  have hEvN :
      ∀ᵐ ω ∂ρ,
        ∀ᶠ n : ℕ in atTop,
          totalErr ρ A ν_pop g θ0 θhat m n ω
            < trainErr ν_pop g θ0 θhat m + ε / 2 := by
    refine hTend.mono ?_
    intro ω ht
    have hlt :
        trainErr ν_pop g θ0 θhat m
          < trainErr ν_pop g θ0 θhat m + ε / 2 := by
      nlinarith [hε.pos]
    exact (tendsto_order.1 ht).2
      (trainErr ν_pop g θ0 θhat m + ε / 2) hlt
  -- Strengthen to < ε using trainErr(m) + ε/2 < ε
  refine hEvN.mono ?_
  intro ω hω
  exact hω.mono (fun n hn => lt_trans hn hSum)

end

end ConjointSD
