/-
ConjointSD/TargetEquivalence.lean

If two score functions are equal ν-a.e., then their population mean/second-moment/variance/SD
under ν are equal. This is the basic tool to turn “consistency to g θ0” into “consistency to
the true estimand”, once you add a WellSpecified / InvarianceAE assumption.
-/

import Mathlib
import ConjointSD.Transport

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

section

variable {Attr : Type*} [MeasurableSpace Attr]
variable (ν : Measure Attr)
variable {s t : Attr → ℝ}

/-- If s = t ν-a.e., then their population means are equal. -/
theorem popMeanAttr_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    popMeanAttr ν s = popMeanAttr ν t := by
  have : (∫ a, s a ∂ν) = (∫ a, t a ∂ν) := by
    exact integral_congr_ae h
  simpa [popMeanAttr] using this

/-- If s = t ν-a.e., then their population second moments are equal. -/
theorem popM2Attr_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    popM2Attr ν s = popM2Attr ν t := by
  have h2 : ∀ᵐ a ∂ν, (s a) ^ 2 = (t a) ^ 2 := by
    refine h.mono ?_
    intro a ha
    simp [ha]
  have : (∫ a, (s a) ^ 2 ∂ν) = (∫ a, (t a) ^ 2 ∂ν) := by
    exact integral_congr_ae h2
  simpa [popM2Attr] using this

/-- If s = t ν-a.e., then their population variances are equal. -/
theorem popVarAttr_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    popVarAttr ν s = popVarAttr ν t := by
  have hm : popMeanAttr ν s = popMeanAttr ν t :=
    popMeanAttr_congr_ae (ν := ν) (s := s) (t := t) h
  have hm2 : popM2Attr ν s = popM2Attr ν t :=
    popM2Attr_congr_ae (ν := ν) (s := s) (t := t) h
  simp [popVarAttr, hm, hm2]

/-- If s = t ν-a.e., then their population SDs are equal. -/
theorem popSDAttr_congr_ae (h : ∀ᵐ a ∂ν, s a = t a) :
    popSDAttr ν s = popSDAttr ν t := by
  have hv : popVarAttr ν s = popVarAttr ν t :=
    popVarAttr_congr_ae (ν := ν) (s := s) (t := t) h
  simp [popSDAttr, hv]

end

/-!
## Approximate target bounds (misspecification)
-/

section Approximate

variable {Attr : Type*} [MeasurableSpace Attr]
variable (ν : Measure Attr)
variable {s t u : Attr → ℝ}

/-- Approximate invariance on population support: `|s - t| ≤ ε` ν-a.e. -/
def ApproxInvarianceAE (s t : Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ᵐ a ∂ν, |s a - t a| ≤ ε

/-- Uniform bound on a score function, ν-a.e. -/
def BoundedAE (s : Attr → ℝ) (C : ℝ) : Prop :=
  ∀ᵐ a ∂ν, |s a| ≤ C

/-- Combine two ν-a.e. approximation bounds by triangle inequality. -/
theorem approxInvarianceAE_triangle
    (ε₁ ε₂ : ℝ)
    (h1 : ApproxInvarianceAE (ν := ν) (s := s) (t := t) ε₁)
    (h2 : ApproxInvarianceAE (ν := ν) (s := t) (t := u) ε₂) :
    ApproxInvarianceAE (ν := ν) (s := s) (t := u) (ε₁ + ε₂) := by
  refine (h1.and h2).mono ?_
  intro x hx
  rcases hx with ⟨h1x, h2x⟩
  have htriangle : |s x - u x| ≤ |s x - t x| + |t x - u x| := by
    simpa using abs_sub_le (s x) (t x) (u x)
  nlinarith [htriangle, h1x, h2x]

section ApproximateMoments

variable [IsProbabilityMeasure ν]

theorem popMeanAttr_diff_le_of_L2Approx
    (hs : Integrable s ν)
    (ht : Integrable t ν)
    (hL2 : L2Approx (ν := ν) (gModel := s) (gTarget := t) δ) :
    |popMeanAttr ν s - popMeanAttr ν t| ≤ δ := by
  rcases hL2 with ⟨hMem, hBound⟩
  have hdiff :
      |popMeanAttr ν s - popMeanAttr ν t|
        =
      |∫ a, (s a - t a) ∂ν| := by
    simp [popMeanAttr, integral_sub, hs, ht]
  have habs :
      |∫ a, (s a - t a) ∂ν| ≤ ∫ a, |s a - t a| ∂ν := by
    simpa using
      (abs_integral_le_integral_abs (f := fun a => s a - t a) (μ := ν))
  have hcs :
      ∫ a, |s a - t a| ∂ν
        ≤
      Real.sqrt (∫ a, |s a - t a| ^ 2 ∂ν) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have hf_nonneg : 0 ≤ᵐ[ν] fun a => |s a - t a| := by
      refine Eventually.of_forall ?_
      intro a
      exact abs_nonneg _
    have hg_nonneg : 0 ≤ᵐ[ν] (fun _ : Attr => (1 : ℝ)) := by
      refine Eventually.of_forall ?_
      intro _a
      exact zero_le_one
    have hf_mem :
        MemLp (fun a => |s a - t a|) (ENNReal.ofReal 2) ν := hMem.norm
    have hg_mem :
        MemLp (fun _ : Attr => (1 : ℝ)) (ENNReal.ofReal 2) ν := by
      simpa using (memLp_const (μ := ν) (p := ENNReal.ofReal 2) (c := (1 : ℝ)))
    have h :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := ν) (p := (2 : ℝ)) (q := (2 : ℝ)) hpq
        hf_nonneg hg_nonneg hf_mem hg_mem
    have h1 :
        (∫ a, |s a - t a| ∂ν)
          ≤
        (∫ a, |s a - t a| ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
      simpa using h
    simpa [Real.sqrt_eq_rpow] using h1
  have hle : |popMeanAttr ν s - popMeanAttr ν t| ≤
      Real.sqrt (∫ a, |s a - t a| ^ 2 ∂ν) := by
    exact le_trans (by simpa [hdiff] using habs) hcs
  exact le_trans hle hBound

theorem popMeanAttr_abs_le_of_bounded_ae
    (hs : Integrable s ν)
    (hBound : BoundedAE (ν := ν) s C) :
    |popMeanAttr ν s| ≤ C := by
  have h1 : |∫ a, s a ∂ν| ≤ ∫ a, |s a| ∂ν := by
    simpa using (abs_integral_le_integral_abs (f := s) (μ := ν))
  have h2 : ∫ a, |s a| ∂ν ≤ ∫ a, C ∂ν := by
    have hs_abs : Integrable (fun a => |s a|) ν := hs.abs
    have hC_int : Integrable (fun _ : Attr => C) ν := integrable_const _
    exact integral_mono_ae hs_abs hC_int hBound
  have hconst : ∫ a, C ∂ν = C := by
    simp
  simpa [popMeanAttr, hconst] using (le_trans h1 h2)

theorem popMeanAttr_diff_le_of_approx_ae
    (hs : Integrable s ν)
    (ht : Integrable t ν)
    (hApprox : ApproxInvarianceAE (ν := ν) s t ε) :
    |popMeanAttr ν s - popMeanAttr ν t| ≤ ε := by
  have hst : Integrable (fun a => s a - t a) ν := hs.sub ht
  have h1 :
      |popMeanAttr ν s - popMeanAttr ν t|
        =
      |∫ a, (s a - t a) ∂ν| := by
    simp [popMeanAttr, integral_sub, hs, ht]
  have h2 : |∫ a, (s a - t a) ∂ν| ≤ ∫ a, |s a - t a| ∂ν := by
    simpa using
      (abs_integral_le_integral_abs (f := fun a => s a - t a) (μ := ν))
  have h3 : ∫ a, |s a - t a| ∂ν ≤ ε := by
    have hst_abs : Integrable (fun a => |s a - t a|) ν := hst.abs
    have hε_int : Integrable (fun _ : Attr => ε) ν := integrable_const _
    have hle := integral_mono_ae hst_abs hε_int hApprox
    have hconst : ∫ a, ε ∂ν = ε := by
      simp
    simpa [hconst] using hle
  simpa [h1] using (le_trans h2 h3)

private theorem abs_sqrt_sub_sqrt_le_sqrt_abs_sub
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  have hsum_nonneg : 0 ≤ Real.sqrt a + Real.sqrt b := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have hsum_abs : |Real.sqrt a + Real.sqrt b| = Real.sqrt a + Real.sqrt b := by
    simp [abs_of_nonneg hsum_nonneg]
  have hfactor :
      |a - b|
        =
      |Real.sqrt a - Real.sqrt b| * |Real.sqrt a + Real.sqrt b| := by
    have h :
        a - b
          =
        (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
      calc
        a - b
            = (Real.sqrt a) ^ 2 - (Real.sqrt b) ^ 2 := by
                simp [Real.sq_sqrt ha, Real.sq_sqrt hb]
        _   = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
                ring
    have h' := congrArg abs h
    simp only [abs_mul] at h'
    exact h'
  have hle_sum : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
    have h := abs_add_le (Real.sqrt a) (-Real.sqrt b)
    simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)] using h
  have hle_sq :
      (|Real.sqrt a - Real.sqrt b|) ^ 2 ≤ |a - b| := by
    have hnonneg : 0 ≤ |Real.sqrt a - Real.sqrt b| := abs_nonneg _
    have hmul :
        |Real.sqrt a - Real.sqrt b| * |Real.sqrt a - Real.sqrt b|
          ≤
        |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
      exact mul_le_mul_of_nonneg_left hle_sum hnonneg
    have hmul' :
        |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b)
          =
        |Real.sqrt a - Real.sqrt b| * |Real.sqrt a + Real.sqrt b| := by
      simp [hsum_abs]
    calc
      (|Real.sqrt a - Real.sqrt b|) ^ 2
          = |Real.sqrt a - Real.sqrt b| * |Real.sqrt a - Real.sqrt b| := by
              simp [pow_two]
      _   ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := hmul
      _   = |Real.sqrt a - Real.sqrt b| * |Real.sqrt a + Real.sqrt b| := hmul'
      _   = |a - b| := by simp [hfactor]
  calc
    |Real.sqrt a - Real.sqrt b|
        = Real.sqrt ((|Real.sqrt a - Real.sqrt b|) ^ 2) := by
            simpa [pow_two] using
              (Real.sqrt_sq_eq_abs (|Real.sqrt a - Real.sqrt b|)).symm
    _   ≤ Real.sqrt |a - b| := by
            exact Real.sqrt_le_sqrt hle_sq

theorem popM2Attr_diff_le_of_approx_ae
    (hs : PopulationMomentAssumptions (ν := ν) s)
    (ht : PopulationMomentAssumptions (ν := ν) t)
    (hBoundS : BoundedAE (ν := ν) s C)
    (hBoundT : BoundedAE (ν := ν) t C)
    (hApprox : ApproxInvarianceAE (ν := ν) s t ε)
    (hε : 0 ≤ ε) :
    |popM2Attr ν s - popM2Attr ν t| ≤ 2 * C * ε := by
  have hAE :
      ∀ᵐ a ∂ν, |(s a) ^ 2 - (t a) ^ 2| ≤ 2 * C * ε := by
    have hAll := hApprox.and (hBoundS.and hBoundT)
    refine hAll.mono ?_
    intro a h
    rcases h with ⟨hst, hsB, htB⟩
    have hsum : |s a + t a| ≤ |s a| + |t a| := by
      simpa using (abs_add_le (s a) (t a))
    have hfact : (s a) ^ 2 - (t a) ^ 2 = (s a - t a) * (s a + t a) := by
      ring
    have hmul :
        |(s a) ^ 2 - (t a) ^ 2| = |s a - t a| * |s a + t a| := by
      simp [hfact, abs_mul]
    calc
      |(s a) ^ 2 - (t a) ^ 2|
          = |s a - t a| * |s a + t a| := hmul
      _   ≤ ε * (|s a| + |t a|) := by
              have hnonneg : 0 ≤ |s a + t a| := abs_nonneg _
              exact mul_le_mul hst hsum hnonneg hε
      _   ≤ ε * (C + C) := by
              have hsum_le : |s a| + |t a| ≤ C + C := by nlinarith
              exact mul_le_mul_of_nonneg_left hsum_le hε
      _   = 2 * C * ε := by ring
  have hs2 : Integrable (fun a => (s a) ^ 2) ν := hs.int2
  have ht2 : Integrable (fun a => (t a) ^ 2) ν := ht.int2
  have hst2 : Integrable (fun a => (s a) ^ 2 - (t a) ^ 2) ν := hs2.sub ht2
  have h1 :
      |popM2Attr ν s - popM2Attr ν t|
        =
      |∫ a, ((s a) ^ 2 - (t a) ^ 2) ∂ν| := by
    simp [popM2Attr, integral_sub, hs2, ht2]
  have h2 :
      |∫ a, ((s a) ^ 2 - (t a) ^ 2) ∂ν|
        ≤
      ∫ a, |(s a) ^ 2 - (t a) ^ 2| ∂ν := by
    simpa using
      (abs_integral_le_integral_abs (f := fun a => (s a) ^ 2 - (t a) ^ 2) (μ := ν))
  have h3 :
      ∫ a, |(s a) ^ 2 - (t a) ^ 2| ∂ν
        ≤
      2 * C * ε := by
    have hst2_abs : Integrable (fun a => |(s a) ^ 2 - (t a) ^ 2|) ν := hst2.abs
    have hC_int : Integrable (fun _ : Attr => 2 * C * ε) ν := integrable_const _
    have hle := integral_mono_ae hst2_abs hC_int hAE
    have hconst : ∫ a, 2 * C * ε ∂ν = 2 * C * ε := by
      simp
    simpa [hconst] using hle
  simpa [h1] using (le_trans h2 h3)

theorem popVarAttr_diff_le_of_approx_ae
    (hs : PopulationMomentAssumptions (ν := ν) s)
    (ht : PopulationMomentAssumptions (ν := ν) t)
    (hBoundS : BoundedAE (ν := ν) s C)
    (hBoundT : BoundedAE (ν := ν) t C)
    (hApprox : ApproxInvarianceAE (ν := ν) s t ε)
    (hε : 0 ≤ ε) :
    |popVarAttr ν s - popVarAttr ν t| ≤ 4 * C * ε := by
  have hmean_diff :
      |popMeanAttr ν s - popMeanAttr ν t| ≤ ε :=
    popMeanAttr_diff_le_of_approx_ae (ν := ν) (s := s) (t := t)
      hs.int1 ht.int1 hApprox
  have hmean_s :
      |popMeanAttr ν s| ≤ C :=
    popMeanAttr_abs_le_of_bounded_ae (ν := ν) (s := s)
      hs.int1 hBoundS
  have hmean_t :
      |popMeanAttr ν t| ≤ C :=
    popMeanAttr_abs_le_of_bounded_ae (ν := ν) (s := t)
      ht.int1 hBoundT
  have hmean_sq :
      |(popMeanAttr ν s) ^ 2 - (popMeanAttr ν t) ^ 2| ≤ 2 * C * ε := by
    have hsum : |popMeanAttr ν s + popMeanAttr ν t| ≤
        |popMeanAttr ν s| + |popMeanAttr ν t| := by
      simpa using (abs_add_le (popMeanAttr ν s) (popMeanAttr ν t))
    have hfact :
        (popMeanAttr ν s) ^ 2 - (popMeanAttr ν t) ^ 2
          =
        (popMeanAttr ν s - popMeanAttr ν t)
          * (popMeanAttr ν s + popMeanAttr ν t) := by
      ring
    have hmul :
        |(popMeanAttr ν s) ^ 2 - (popMeanAttr ν t) ^ 2|
          =
        |popMeanAttr ν s - popMeanAttr ν t|
          * |popMeanAttr ν s + popMeanAttr ν t| := by
      simp [hfact, abs_mul]
    calc
      |(popMeanAttr ν s) ^ 2 - (popMeanAttr ν t) ^ 2|
          = |popMeanAttr ν s - popMeanAttr ν t|
              * |popMeanAttr ν s + popMeanAttr ν t| := hmul
      _   ≤ ε * (|popMeanAttr ν s| + |popMeanAttr ν t|) := by
              have hnonneg : 0 ≤ |popMeanAttr ν s + popMeanAttr ν t| := abs_nonneg _
              exact mul_le_mul hmean_diff hsum hnonneg hε
      _   ≤ ε * (C + C) := by
              have hsum_le : |popMeanAttr ν s| + |popMeanAttr ν t| ≤ C + C := by nlinarith
              exact mul_le_mul_of_nonneg_left hsum_le hε
      _   = 2 * C * ε := by ring
  have hM2 :
      |popM2Attr ν s - popM2Attr ν t| ≤ 2 * C * ε :=
    popM2Attr_diff_le_of_approx_ae (ν := ν) (s := s) (t := t)
      hs ht hBoundS hBoundT hApprox hε
  have hvar :
      popVarAttr ν s - popVarAttr ν t
        =
      (popM2Attr ν s - popM2Attr ν t)
        - ((popMeanAttr ν s) ^ 2 - (popMeanAttr ν t) ^ 2) := by
    simp [popVarAttr, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have htriangle :
      |popVarAttr ν s - popVarAttr ν t|
        ≤ |popM2Attr ν s - popM2Attr ν t|
            + |(popMeanAttr ν t) ^ 2 - (popMeanAttr ν s) ^ 2| := by
    have h :=
      abs_add_le (popM2Attr ν s - popM2Attr ν t)
        (-(popMeanAttr ν s ^ 2 - popMeanAttr ν t ^ 2))
    simpa [hvar, sub_eq_add_neg, abs_neg, abs_sub_comm,
      add_comm, add_left_comm, add_assoc] using h
  have hsum : |popM2Attr ν s - popM2Attr ν t|
        + |(popMeanAttr ν t) ^ 2 - (popMeanAttr ν s) ^ 2|
          ≤ 4 * C * ε := by
    have hmean_sq' :
        |(popMeanAttr ν t) ^ 2 - (popMeanAttr ν s) ^ 2| ≤ 2 * C * ε := by
      simpa [abs_sub_comm] using hmean_sq
    nlinarith [hM2, hmean_sq']
  exact le_trans htriangle hsum

theorem popSDAttr_diff_le_of_approx_ae
    (hs : PopulationMomentAssumptions (ν := ν) s)
    (ht : PopulationMomentAssumptions (ν := ν) t)
    (hBoundS : BoundedAE (ν := ν) s C)
    (hBoundT : BoundedAE (ν := ν) t C)
    (hApprox : ApproxInvarianceAE (ν := ν) s t ε)
    (hε : 0 ≤ ε)
    (hVarS : 0 ≤ popVarAttr ν s) (hVarT : 0 ≤ popVarAttr ν t) :
    |popSDAttr ν s - popSDAttr ν t| ≤ Real.sqrt (4 * C * ε) := by
  have hvar :
      |popVarAttr ν s - popVarAttr ν t| ≤ 4 * C * ε :=
    popVarAttr_diff_le_of_approx_ae (ν := ν) (s := s) (t := t)
      hs ht hBoundS hBoundT hApprox hε
  have hsd :
      |popSDAttr ν s - popSDAttr ν t|
        ≤ Real.sqrt |popVarAttr ν s - popVarAttr ν t| := by
    simpa [popSDAttr] using
      (abs_sqrt_sub_sqrt_le_sqrt_abs_sub (a := popVarAttr ν s) (b := popVarAttr ν t)
        hVarS hVarT)
  have hsqrt :
      Real.sqrt |popVarAttr ν s - popVarAttr ν t|
        ≤ Real.sqrt (4 * C * ε) := by
    apply Real.sqrt_le_sqrt
    exact hvar
  exact le_trans hsd hsqrt

end ApproximateMoments

end Approximate

end ConjointSD
