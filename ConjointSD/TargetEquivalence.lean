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

section L2Centering

lemma popVarAttr_eq_integral_centered
    (hs : Integrable s ν)
    (hs2 : Integrable (fun a => (s a) ^ 2) ν) :
    popVarAttr ν s = ∫ a, (s a - popMeanAttr ν s) ^ 2 ∂ν := by
  set μs : ℝ := popMeanAttr ν s
  have hmul : Integrable (fun a => (2 * μs) * s a) ν := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hs.mul_const (2 * μs)
  have hconst : Integrable (fun _ : Attr => μs ^ 2) ν := integrable_const _
  have hsum :
      Integrable (fun a => (s a) ^ 2 - (2 * μs) * s a + μs ^ 2) ν := by
    exact (hs2.sub hmul).add hconst
  have hpoint :
      ∀ᵐ a ∂ν, (s a - μs) ^ 2 = (s a) ^ 2 - (2 * μs) * s a + μs ^ 2 := by
    refine Eventually.of_forall ?_
    intro a
    ring
  have hcenter :
      ∫ a, (s a - μs) ^ 2 ∂ν
        = ∫ a, (s a) ^ 2 - (2 * μs) * s a + μs ^ 2 ∂ν := by
    exact integral_congr_ae hpoint
  have hsub :
      ∫ a, (s a) ^ 2 - (2 * μs) * s a ∂ν
        =
      ∫ a, (s a) ^ 2 ∂ν - ∫ a, (2 * μs) * s a ∂ν := by
    simpa [sub_eq_add_neg] using
      (integral_sub (μ := ν)
        (f := fun a => (s a) ^ 2) (g := fun a => (2 * μs) * s a) hs2 hmul)
  have hmul_int :
      ∫ a, (2 * μs) * s a ∂ν = 2 * μs * ∫ a, s a ∂ν := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (integral_const_mul (μ := ν) (2 * μs) (fun a => s a))
  have hsum_int :
      ∫ a, (s a) ^ 2 - (2 * μs) * s a + μs ^ 2 ∂ν
        =
      ∫ a, (s a) ^ 2 - (2 * μs) * s a ∂ν + ∫ a, μs ^ 2 ∂ν := by
    have hleft : Integrable (fun a => (s a) ^ 2 - (2 * μs) * s a) ν := hs2.sub hmul
    simpa [add_assoc] using
      (integral_add (μ := ν)
        (f := fun a => (s a) ^ 2 - (2 * μs) * s a)
        (g := fun _ : Attr => μs ^ 2) hleft hconst)
  have hmean : ∫ a, s a ∂ν = μs := by
    simp [μs, popMeanAttr]
  have hconst_int : ∫ a, μs ^ 2 ∂ν = μs ^ 2 := by
    simp
  have hcalc :
      ∫ a, (s a - μs) ^ 2 ∂ν = ∫ a, (s a) ^ 2 ∂ν - μs ^ 2 := by
    calc
      ∫ a, (s a - μs) ^ 2 ∂ν
          = ∫ a, (s a) ^ 2 - (2 * μs) * s a + μs ^ 2 ∂ν := by
              exact hcenter
      _ = (∫ a, (s a) ^ 2 - (2 * μs) * s a ∂ν) + ∫ a, μs ^ 2 ∂ν := by
              exact hsum_int
      _ = (∫ a, (s a) ^ 2 ∂ν - ∫ a, (2 * μs) * s a ∂ν) + μs ^ 2 := by
              simp [hconst_int, hsub]
      _ = (∫ a, (s a) ^ 2 ∂ν - 2 * μs * ∫ a, s a ∂ν) + μs ^ 2 := by
              simpa [hmul_int]
      _ = ∫ a, (s a) ^ 2 ∂ν - 2 * μs * ∫ a, s a ∂ν + μs ^ 2 := by
              ring
      _ = ∫ a, (s a) ^ 2 ∂ν - μs ^ 2 := by
              have hring :
                  ∫ a, (s a) ^ 2 ∂ν - 2 * μs * μs + μs ^ 2
                    = ∫ a, (s a) ^ 2 ∂ν - μs ^ 2 := by
                ring
              simpa [hmean] using hring
  have hmean_sq : (∫ a, s a ∂ν) ^ 2 = μs ^ 2 := by
    simp [μs, popMeanAttr]
  calc
    popVarAttr ν s = ∫ a, (s a) ^ 2 ∂ν - μs ^ 2 := by
      simp [popVarAttr, popM2Attr, popMeanAttr, hmean_sq, μs]
    _ = ∫ a, (s a - μs) ^ 2 ∂ν := by
      symm
      exact hcalc

lemma popSDAttr_eq_l2_centered
    (hs : Integrable s ν)
    (hs2 : Integrable (fun a => (s a) ^ 2) ν) :
    popSDAttr ν s = Real.sqrt (∫ a, |s a - popMeanAttr ν s| ^ 2 ∂ν) := by
  have hvar :
      popVarAttr ν s = ∫ a, (s a - popMeanAttr ν s) ^ 2 ∂ν :=
    popVarAttr_eq_integral_centered (ν := ν) (s := s) hs hs2
  have habs :
      (∫ a, |s a - popMeanAttr ν s| ^ 2 ∂ν)
        = ∫ a, (s a - popMeanAttr ν s) ^ 2 ∂ν := by
    simp [abs_sq]
  simp [popSDAttr, hvar, habs]

end L2Centering

section L2Triangle

lemma l2_centered_triangle_eLpNorm
    (hMem : MemLp (fun a => s a - t a) (2 : ENNReal) ν) :
    ENNReal.toReal
        (eLpNorm (fun a => (s a - popMeanAttr ν s) - (t a - popMeanAttr ν t)) 2 ν)
      ≤
    ENNReal.toReal (eLpNorm (fun a => s a - t a) 2 ν)
      + ENNReal.toReal (eLpNorm (fun _ : Attr => popMeanAttr ν s - popMeanAttr ν t) 2 ν) := by
  set c : ℝ := popMeanAttr ν s - popMeanAttr ν t
  have hconst : MemLp (fun _ : Attr => c) (2 : ENNReal) ν := by
    simpa using (memLp_const (μ := ν) (p := (2 : ENNReal)) (c := c))
  have htri :
      eLpNorm (fun a => (s a - t a) - c) 2 ν
        ≤
      eLpNorm (fun a => s a - t a) 2 ν + eLpNorm (fun _ : Attr => c) 2 ν := by
    have h :=
      eLpNorm_sub_le (μ := ν) (p := (2 : ENNReal))
        (f := fun a => s a - t a)
        (g := fun _ : Attr => c)
        (hf := hMem.aestronglyMeasurable)
        (hg := hconst.aestronglyMeasurable)
        (hp := by norm_num)
    simpa using h
  have hsum_ne_top :
      eLpNorm (fun a => s a - t a) 2 ν
        + eLpNorm (fun _ : Attr => c) 2 ν ≠ (⊤ : ENNReal) := by
    exact ne_of_lt (ENNReal.add_lt_top.2 ⟨hMem.2, hconst.2⟩)
  have hmono :
      ENNReal.toReal (eLpNorm (fun a => (s a - t a) - c) 2 ν)
        ≤
      ENNReal.toReal
        (eLpNorm (fun a => s a - t a) 2 ν + eLpNorm (fun _ : Attr => c) 2 ν) := by
    exact ENNReal.toReal_mono hsum_ne_top htri
  have hsum :
      ENNReal.toReal
          (eLpNorm (fun a => s a - t a) 2 ν + eLpNorm (fun _ : Attr => c) 2 ν)
        =
      ENNReal.toReal (eLpNorm (fun a => s a - t a) 2 ν)
        + ENNReal.toReal (eLpNorm (fun _ : Attr => c) 2 ν) := by
    exact ENNReal.toReal_add (ne_of_lt hMem.2) (ne_of_lt hconst.2)
  have hrewrite :
      (fun a => (s a - t a) - c) =
        fun a => (s a - popMeanAttr ν s) - (t a - popMeanAttr ν t) := by
    funext a
    simp [c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [hsum, hrewrite, c] using hmono

end L2Triangle

end ApproximateMoments

section L2IntegralBridge

lemma sqrt_integral_sq_eq_eLpNorm
    (hs : MemLp s (2 : ENNReal) ν) :
    Real.sqrt (∫ a, |s a| ^ 2 ∂ν)
      =
    ENNReal.toReal (eLpNorm s (2 : ENNReal) ν) := by
  have h0 : (2 : ENNReal) ≠ 0 := by norm_num
  have htop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
  have hnorm :
      eLpNorm s (2 : ENNReal) ν
        =
      ENNReal.ofReal ((∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))) := by
    simpa using
      (MemLp.eLpNorm_eq_integral_rpow_norm (μ := ν) (f := s) (p := (2 : ENNReal)) h0 htop hs)
  have htoReal :
      ENNReal.toReal (eLpNorm s (2 : ENNReal) ν)
        =
      (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
    have hnonneg_int : 0 ≤ ∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν := by
      refine integral_nonneg_of_ae ?_
      refine Eventually.of_forall ?_
      intro a
      exact by positivity
    have hnonneg : 0 ≤ (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
      exact Real.rpow_nonneg hnonneg_int _
    calc
      ENNReal.toReal (eLpNorm s (2 : ENNReal) ν)
          = ENNReal.toReal (ENNReal.ofReal ((∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)))) := by
              simpa [hnorm]
      _ = (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
              exact ENNReal.toReal_ofReal hnonneg
  have hnorm_abs :
      (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
        =
      (∫ a, |s a| ^ 2 ∂ν) ^ (1 / (2 : ℝ)) := by
    simp [Real.norm_eq_abs]
  have hsqrt :
      Real.sqrt (∫ a, |s a| ^ 2 ∂ν) = (∫ a, |s a| ^ 2 ∂ν) ^ (1 / (2 : ℝ)) := by
    simp [Real.sqrt_eq_rpow]
  calc
    Real.sqrt (∫ a, |s a| ^ 2 ∂ν)
        = (∫ a, |s a| ^ 2 ∂ν) ^ (1 / (2 : ℝ)) := hsqrt
    _ = (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
          simpa [hnorm_abs] using rfl
    _ = ENNReal.toReal (eLpNorm s (2 : ENNReal) ν) := by
          symm
          exact htoReal

end L2IntegralBridge

section ApproximateMoments

variable [IsProbabilityMeasure ν]

theorem popSDAttr_diff_le_of_L2Approx
    (hs : PopulationMomentAssumptions (ν := ν) s)
    (ht : PopulationMomentAssumptions (ν := ν) t)
    (hL2 : L2Approx (ν := ν) (gModel := s) (gTarget := t) δ) :
    |popSDAttr ν s - popSDAttr ν t| ≤ 2 * δ := by
  set μs : ℝ := popMeanAttr ν s
  set μt : ℝ := popMeanAttr ν t
  have hs_mem : MemLp s (2 : ENNReal) ν := by
    have hs_meas : AEStronglyMeasurable s ν := hs.int1.aestronglyMeasurable
    have hs_mem' : MemLp s (2 : ENNReal) ν :=
      (memLp_two_iff_integrable_sq hs_meas).2 hs.int2
    simpa using hs_mem'
  have ht_mem : MemLp t (2 : ENNReal) ν := by
    have ht_meas : AEStronglyMeasurable t ν := ht.int1.aestronglyMeasurable
    have ht_mem' : MemLp t (2 : ENNReal) ν :=
      (memLp_two_iff_integrable_sq ht_meas).2 ht.int2
    simpa using ht_mem'
  have hcenter_s : MemLp (fun a => s a - μs) (2 : ENNReal) ν := by
    simpa using hs_mem.sub (memLp_const (μ := ν) (p := (2 : ENNReal)) (c := μs))
  have hcenter_t : MemLp (fun a => t a - μt) (2 : ENNReal) ν := by
    simpa using ht_mem.sub (memLp_const (μ := ν) (p := (2 : ENNReal)) (c := μt))
  have hcenter_diff : MemLp (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν := by
    simpa using hcenter_s.sub hcenter_t
  have hs_center :
      popSDAttr ν s =
        ENNReal.toReal (eLpNorm (fun a => s a - μs) (2 : ENNReal) ν) := by
    have hsd :=
      popSDAttr_eq_l2_centered (ν := ν) (s := s) hs.int1 hs.int2
    have hsd' :
        popSDAttr ν s = Real.sqrt (∫ a, |s a - μs| ^ 2 ∂ν) := by
      simpa [μs] using hsd
    have hbridge :=
      sqrt_integral_sq_eq_eLpNorm (ν := ν) (s := fun a => s a - μs) hcenter_s
    simpa [μs] using (hsd'.trans hbridge)
  have ht_center :
      popSDAttr ν t =
        ENNReal.toReal (eLpNorm (fun a => t a - μt) (2 : ENNReal) ν) := by
    have hsd :=
      popSDAttr_eq_l2_centered (ν := ν) (s := t) ht.int1 ht.int2
    have hsd' :
        popSDAttr ν t = Real.sqrt (∫ a, |t a - μt| ^ 2 ∂ν) := by
      simpa [μt] using hsd
    have hbridge :=
      sqrt_integral_sq_eq_eLpNorm (ν := ν) (s := fun a => t a - μt) hcenter_t
    simpa [μt] using (hsd'.trans hbridge)
  have htri1 :
      ENNReal.toReal (eLpNorm (fun a => s a - μs) (2 : ENNReal) ν)
        ≤
      ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν)
        + ENNReal.toReal (eLpNorm (fun a => t a - μt) (2 : ENNReal) ν) := by
    have h :=
      eLpNorm_add_le (μ := ν) (p := (2 : ENNReal))
        (f := fun a => (s a - μs) - (t a - μt))
        (g := fun a => t a - μt)
        (hf := hcenter_diff.aestronglyMeasurable)
        (hg := hcenter_t.aestronglyMeasurable)
        (hp1 := by norm_num)
    have hsum_ne_top :
        eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν
          + eLpNorm (fun a => t a - μt) (2 : ENNReal) ν ≠ (⊤ : ENNReal) := by
      exact ne_of_lt (ENNReal.add_lt_top.2 ⟨hcenter_diff.2, hcenter_t.2⟩)
    have hmono :
        ENNReal.toReal
            (eLpNorm (fun a => (s a - μs) - (t a - μt) + (t a - μt)) (2 : ENNReal) ν)
          ≤
        ENNReal.toReal
            (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν
              + eLpNorm (fun a => t a - μt) (2 : ENNReal) ν) := by
      exact ENNReal.toReal_mono hsum_ne_top h
    have hsum :
        ENNReal.toReal
            (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν
              + eLpNorm (fun a => t a - μt) (2 : ENNReal) ν)
          =
        ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν)
          + ENNReal.toReal (eLpNorm (fun a => t a - μt) (2 : ENNReal) ν) := by
      exact ENNReal.toReal_add (ne_of_lt hcenter_diff.2) (ne_of_lt hcenter_t.2)
    have hrewrite :
        (fun a => (s a - μs) - (t a - μt) + (t a - μt)) = fun a => s a - μs := by
      funext a
      ring
    simpa [hsum, hrewrite] using hmono
  have htri2 :
      ENNReal.toReal (eLpNorm (fun a => t a - μt) (2 : ENNReal) ν)
        ≤
      ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν)
        + ENNReal.toReal (eLpNorm (fun a => s a - μs) (2 : ENNReal) ν) := by
    have h :=
      eLpNorm_add_le (μ := ν) (p := (2 : ENNReal))
        (f := fun a => (t a - μt) - (s a - μs))
        (g := fun a => s a - μs)
        (hf := (hcenter_t.sub hcenter_s).aestronglyMeasurable)
        (hg := hcenter_s.aestronglyMeasurable)
        (hp1 := by norm_num)
    have hsum_ne_top :
        eLpNorm (fun a => (t a - μt) - (s a - μs)) (2 : ENNReal) ν
          + eLpNorm (fun a => s a - μs) (2 : ENNReal) ν ≠ (⊤ : ENNReal) := by
      exact ne_of_lt (ENNReal.add_lt_top.2 ⟨(hcenter_t.sub hcenter_s).2, hcenter_s.2⟩)
    have hmono :
        ENNReal.toReal
            (eLpNorm (fun a => (t a - μt) - (s a - μs) + (s a - μs)) (2 : ENNReal) ν)
          ≤
        ENNReal.toReal
            (eLpNorm (fun a => (t a - μt) - (s a - μs)) (2 : ENNReal) ν
              + eLpNorm (fun a => s a - μs) (2 : ENNReal) ν) := by
      exact ENNReal.toReal_mono hsum_ne_top h
    have hsum :
        ENNReal.toReal
            (eLpNorm (fun a => (t a - μt) - (s a - μs)) (2 : ENNReal) ν
              + eLpNorm (fun a => s a - μs) (2 : ENNReal) ν)
          =
        ENNReal.toReal (eLpNorm (fun a => (t a - μt) - (s a - μs)) (2 : ENNReal) ν)
          + ENNReal.toReal (eLpNorm (fun a => s a - μs) (2 : ENNReal) ν) := by
      exact ENNReal.toReal_add (ne_of_lt (hcenter_t.sub hcenter_s).2) (ne_of_lt hcenter_s.2)
    have hrewrite :
        (fun a => (t a - μt) - (s a - μs) + (s a - μs)) = fun a => t a - μt := by
      funext a
      ring
    have htri2' :
        ENNReal.toReal (eLpNorm (fun a => t a - μt) (2 : ENNReal) ν)
          ≤
        ENNReal.toReal (eLpNorm (fun a => (t a - μt) - (s a - μs)) (2 : ENNReal) ν)
          + ENNReal.toReal (eLpNorm (fun a => s a - μs) (2 : ENNReal) ν) := by
      simpa [hsum, hrewrite] using hmono
    have hswap :
        eLpNorm (fun a => (t a - μt) - (s a - μs)) (2 : ENNReal) ν
          =
        eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν := by
      simpa [Pi.sub_apply] using
        (eLpNorm_sub_comm
          (f := fun a => t a - μt) (g := fun a => s a - μs) (p := (2 : ENNReal)) (μ := ν))
    simpa [hswap] using htri2'
  have hsd_le :
      |popSDAttr ν s - popSDAttr ν t|
        ≤ ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν) := by
    have h1 :
        popSDAttr ν s
          ≤ popSDAttr ν t
              + ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν) := by
      simpa [hs_center, ht_center, add_comm, add_left_comm, add_assoc] using htri1
    have h2 :
        popSDAttr ν t
          ≤ popSDAttr ν s
              + ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν) := by
      simpa [hs_center, ht_center, add_comm, add_left_comm, add_assoc] using htri2
    have h1' : popSDAttr ν s - popSDAttr ν t
        ≤ ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν) := by
      linarith
    have h2' : popSDAttr ν t - popSDAttr ν s
        ≤ ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν) := by
      linarith
    exact (abs_sub_le_iff).2 ⟨h1', h2'⟩
  have htri_centered :
      ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν)
        ≤
      ENNReal.toReal (eLpNorm (fun a => s a - t a) (2 : ENNReal) ν)
        + ENNReal.toReal (eLpNorm (fun _ : Attr => μs - μt) (2 : ENNReal) ν) := by
    have hMem : MemLp (fun a => s a - t a) (2 : ENNReal) ν := by
      simpa using hL2.1
    simpa [μs, μt] using (l2_centered_triangle_eLpNorm (ν := ν) (s := s) (t := t) hMem)
  have hconst :
      ENNReal.toReal (eLpNorm (fun _ : Attr => μs - μt) (2 : ENNReal) ν) = |μs - μt| := by
    have h0 : (2 : ENNReal) ≠ 0 := by norm_num
    have htop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    have hμ : (ν Set.univ) = 1 := by
      simpa using (measure_univ : ν Set.univ = 1)
    have hconst' :=
      eLpNorm_const' (μ := ν) (p := (2 : ENNReal)) (c := μs - μt) h0 htop
    calc
      ENNReal.toReal (eLpNorm (fun _ : Attr => μs - μt) (2 : ENNReal) ν)
          = ENNReal.toReal (‖μs - μt‖ₑ * ν Set.univ ^ (1 / ENNReal.toReal (2 : ENNReal))) := by
              simpa [hconst']
      _ = ENNReal.toReal (‖μs - μt‖ₑ) := by
              simp [hμ]
      _ = |μs - μt| := by
              simp [Real.enorm_eq_ofReal_abs]
  have hmean :
      |μs - μt| ≤ δ :=
    popMeanAttr_diff_le_of_L2Approx (ν := ν) (s := s) (t := t) hs.int1 ht.int1 hL2
  have hnorm_st :
      ENNReal.toReal (eLpNorm (fun a => s a - t a) (2 : ENNReal) ν) ≤ δ := by
    have hMem : MemLp (fun a => s a - t a) (2 : ENNReal) ν := by
      simpa using hL2.1
    have hbridge :=
      sqrt_integral_sq_eq_eLpNorm (ν := ν) (s := fun a => s a - t a) hMem
    have hbridge' :
        Real.sqrt (∫ a, (s a - t a) ^ 2 ∂ν)
          = ENNReal.toReal (eLpNorm (fun a => s a - t a) (2 : ENNReal) ν) := by
      simpa [abs_sq] using hbridge
    have hL2' : Real.sqrt (∫ a, (s a - t a) ^ 2 ∂ν) ≤ δ := by
      simpa [abs_sq] using hL2.2
    simpa [hbridge'] using hL2'
  have hle :
      ENNReal.toReal (eLpNorm (fun a => (s a - μs) - (t a - μt)) (2 : ENNReal) ν)
        ≤ 2 * δ := by
    have hmean' : ENNReal.toReal (eLpNorm (fun _ : Attr => μs - μt) (2 : ENNReal) ν) ≤ δ := by
      simpa [hconst] using hmean
    nlinarith [htri_centered, hnorm_st, hmean']
  exact le_trans hsd_le hle

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
