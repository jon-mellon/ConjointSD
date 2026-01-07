import Mathlib
import ConjointSD.Transport
import ConjointSD.Assumptions
import ConjointSD.ApproxAssumptions

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ConjointSD

/-!
## Approximate target bounds (misspecification)
-/

section Approximate

variable {Attr : Type*} [MeasurableSpace Attr]
variable (ν_pop : Measure Attr)
variable {s t u : Attr → ℝ}

section ApproximateMoments

variable [IsProbabilityMeasure ν_pop]

section L2Centering

lemma attrVar_eq_integral_centered
    (hs : Integrable s ν_pop)
    (hs2 : Integrable (fun a => (s a) ^ 2) ν_pop) :
    attrVar ν_pop s = ∫ a, (s a - attrMean ν_pop s) ^ 2 ∂ν_pop := by
  set ηs : ℝ := attrMean ν_pop s
  have hmul : Integrable (fun a => (2 * ηs) * s a) ν_pop := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hs.mul_const (2 * ηs)
  have hconst : Integrable (fun _ : Attr => ηs ^ 2) ν_pop := integrable_const _
  have hsum :
      Integrable (fun a => (s a) ^ 2 - (2 * ηs) * s a + ηs ^ 2) ν_pop := by
    exact (hs2.sub hmul).add hconst
  have hpoint :
      ∀ᵐ a ∂ν_pop, (s a - ηs) ^ 2 = (s a) ^ 2 - (2 * ηs) * s a + ηs ^ 2 := by
    refine Eventually.of_forall ?_
    intro a
    ring
  have hcenter :
      ∫ a, (s a - ηs) ^ 2 ∂ν_pop
        = ∫ a, (s a) ^ 2 - (2 * ηs) * s a + ηs ^ 2 ∂ν_pop := by
    exact integral_congr_ae hpoint
  have hsub :
      ∫ a, (s a) ^ 2 - (2 * ηs) * s a ∂ν_pop
        =
      ∫ a, (s a) ^ 2 ∂ν_pop - ∫ a, (2 * ηs) * s a ∂ν_pop := by
    simpa [sub_eq_add_neg] using
      (integral_sub (μ := ν_pop)
        (f := fun a => (s a) ^ 2) (g := fun a => (2 * ηs) * s a) hs2 hmul)
  have hmul_int :
      ∫ a, (2 * ηs) * s a ∂ν_pop = 2 * ηs * ∫ a, s a ∂ν_pop := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (integral_const_mul (μ := ν_pop) (2 * ηs) (fun a => s a))
  have hsum_int :
      ∫ a, (s a) ^ 2 - (2 * ηs) * s a + ηs ^ 2 ∂ν_pop
        =
      ∫ a, (s a) ^ 2 - (2 * ηs) * s a ∂ν_pop + ∫ a, ηs ^ 2 ∂ν_pop := by
    have hleft : Integrable (fun a => (s a) ^ 2 - (2 * ηs) * s a) ν_pop := hs2.sub hmul
    simpa [add_assoc] using
      (integral_add (μ := ν_pop)
        (f := fun a => (s a) ^ 2 - (2 * ηs) * s a)
        (g := fun _ : Attr => ηs ^ 2) hleft hconst)
  have hmean : ∫ a, s a ∂ν_pop = ηs := by
    simp [ηs, attrMean]
  have hconst_int : ∫ a, ηs ^ 2 ∂ν_pop = ηs ^ 2 := by
    simp
  have hcalc :
      ∫ a, (s a - ηs) ^ 2 ∂ν_pop = ∫ a, (s a) ^ 2 ∂ν_pop - ηs ^ 2 := by
    calc
      ∫ a, (s a - ηs) ^ 2 ∂ν_pop
          = ∫ a, (s a) ^ 2 - (2 * ηs) * s a + ηs ^ 2 ∂ν_pop := by
              exact hcenter
      _ = (∫ a, (s a) ^ 2 - (2 * ηs) * s a ∂ν_pop) + ∫ a, ηs ^ 2 ∂ν_pop := by
              exact hsum_int
      _ = (∫ a, (s a) ^ 2 ∂ν_pop - ∫ a, (2 * ηs) * s a ∂ν_pop) + ηs ^ 2 := by
              simp [hconst_int, hsub]
      _ = (∫ a, (s a) ^ 2 ∂ν_pop - 2 * ηs * ∫ a, s a ∂ν_pop) + ηs ^ 2 := by
              simp [hmul_int]
      _ = ∫ a, (s a) ^ 2 ∂ν_pop - 2 * ηs * ∫ a, s a ∂ν_pop + ηs ^ 2 := by
              ring
      _ = ∫ a, (s a) ^ 2 ∂ν_pop - ηs ^ 2 := by
              have hring :
                  ∫ a, (s a) ^ 2 ∂ν_pop - 2 * ηs * ηs + ηs ^ 2
                    = ∫ a, (s a) ^ 2 ∂ν_pop - ηs ^ 2 := by
                ring
              simpa [hmean] using hring
  have hmean_sq : (∫ a, s a ∂ν_pop) ^ 2 = ηs ^ 2 := by
    simp [ηs, attrMean]
  calc
    attrVar ν_pop s = ∫ a, (s a) ^ 2 ∂ν_pop - ηs ^ 2 := by
      simp [attrVar, attrM2, attrMean, hmean_sq, ηs]
    _ = ∫ a, (s a - ηs) ^ 2 ∂ν_pop := by
      symm
      exact hcalc

lemma attrSD_eq_l2_centered
    (hs : Integrable s ν_pop)
    (hs2 : Integrable (fun a => (s a) ^ 2) ν_pop) :
    attrSD ν_pop s = Real.sqrt (∫ a, |s a - attrMean ν_pop s| ^ 2 ∂ν_pop) := by
  have hvar :
      attrVar ν_pop s = ∫ a, (s a - attrMean ν_pop s) ^ 2 ∂ν_pop :=
    attrVar_eq_integral_centered (ν_pop := ν_pop) (s := s) hs hs2
  calc
    attrSD ν_pop s = Real.sqrt (∫ a, (s a - attrMean ν_pop s) ^ 2 ∂ν_pop) := by
      simp [attrSD, hvar]
    _ = Real.sqrt (∫ a, |s a - attrMean ν_pop s| ^ 2 ∂ν_pop) := by
      simp

end L2Centering

section L2Triangle

lemma l2_centered_triangle_eLpNorm
    (hMem : MemLp (fun a => s a - t a) (2 : ENNReal) ν_pop) :
    ENNReal.toReal
        (eLpNorm (fun a => (s a - attrMean ν_pop s) - (t a - attrMean ν_pop t)) 2 ν_pop)
      ≤
    ENNReal.toReal (eLpNorm (fun a => s a - t a) 2 ν_pop)
      + ENNReal.toReal (eLpNorm (fun _ : Attr => attrMean ν_pop s - attrMean ν_pop t) 2 ν_pop) := by
  set c : ℝ := attrMean ν_pop s - attrMean ν_pop t
  have hconst : MemLp (fun _ : Attr => c) (2 : ENNReal) ν_pop := by
    simpa using (memLp_const (μ := ν_pop) (p := (2 : ENNReal)) (c := c))
  have htri :
      eLpNorm (fun a => (s a - t a) - c) 2 ν_pop
        ≤
      eLpNorm (fun a => s a - t a) 2 ν_pop + eLpNorm (fun _ : Attr => c) 2 ν_pop := by
    have h :=
      eLpNorm_sub_le (μ := ν_pop) (p := (2 : ENNReal))
        (f := fun a => s a - t a)
        (g := fun _ : Attr => c)
        (hf := hMem.aestronglyMeasurable)
        (hg := hconst.aestronglyMeasurable)
        (hp := by norm_num)
    simpa using h
  have hsum_ne_top :
      eLpNorm (fun a => s a - t a) 2 ν_pop
        + eLpNorm (fun _ : Attr => c) 2 ν_pop ≠ (⊤ : ENNReal) := by
    exact ne_of_lt (ENNReal.add_lt_top.2 ⟨hMem.2, hconst.2⟩)
  have hmono :
      ENNReal.toReal (eLpNorm (fun a => (s a - t a) - c) 2 ν_pop)
        ≤
      ENNReal.toReal
        (eLpNorm (fun a => s a - t a) 2 ν_pop + eLpNorm (fun _ : Attr => c) 2 ν_pop) := by
    exact ENNReal.toReal_mono hsum_ne_top htri
  have hsum :
      ENNReal.toReal
          (eLpNorm (fun a => s a - t a) 2 ν_pop + eLpNorm (fun _ : Attr => c) 2 ν_pop)
        =
      ENNReal.toReal (eLpNorm (fun a => s a - t a) 2 ν_pop)
        + ENNReal.toReal (eLpNorm (fun _ : Attr => c) 2 ν_pop) := by
    exact ENNReal.toReal_add (ne_of_lt hMem.2) (ne_of_lt hconst.2)
  have hrewrite :
      (fun a => (s a - t a) - c) =
        fun a => (s a - attrMean ν_pop s) - (t a - attrMean ν_pop t) := by
    funext a
    simp [c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [hsum, hrewrite, c] using hmono

end L2Triangle

end ApproximateMoments

section L2IntegralBridge

lemma sqrt_integral_sq_eq_eLpNorm
    (hs : MemLp s (2 : ENNReal) ν_pop) :
    Real.sqrt (∫ a, |s a| ^ 2 ∂ν_pop)
      =
    ENNReal.toReal (eLpNorm s (2 : ENNReal) ν_pop) := by
  have h0 : (2 : ENNReal) ≠ 0 := by norm_num
  have htop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
  have hnorm :
      eLpNorm s (2 : ENNReal) ν_pop
        =
      ENNReal.ofReal ((∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν_pop) ^ (1 / (2 : ℝ))) := by
    simpa using
      (MemLp.eLpNorm_eq_integral_rpow_norm (μ := ν_pop) (f := s) (p := (2 : ENNReal)) h0 htop hs)
  have htoReal :
      ENNReal.toReal (eLpNorm s (2 : ENNReal) ν_pop)
        =
      (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν_pop) ^ (1 / (2 : ℝ)) := by
    have hnonneg_int : 0 ≤ ∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν_pop := by
      refine integral_nonneg_of_ae ?_
      refine Eventually.of_forall ?_
      intro a
      exact by positivity
    have hnonneg : 0 ≤ (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν_pop) ^ (1 / (2 : ℝ)) := by
      exact Real.rpow_nonneg hnonneg_int _
    calc
      ENNReal.toReal (eLpNorm s (2 : ENNReal) ν_pop)
          = ENNReal.toReal (ENNReal.ofReal ((∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν_pop) ^ (1 / (2 : ℝ)))) := by
              simp [hnorm]
      _ = (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν_pop) ^ (1 / (2 : ℝ)) := by
              exact ENNReal.toReal_ofReal hnonneg
  have hsqrt :
      Real.sqrt (∫ a, |s a| ^ 2 ∂ν_pop) = (∫ a, |s a| ^ 2 ∂ν_pop) ^ (1 / (2 : ℝ)) := by
    simp [Real.sqrt_eq_rpow]
  calc
    Real.sqrt (∫ a, |s a| ^ 2 ∂ν_pop)
        = (∫ a, |s a| ^ 2 ∂ν_pop) ^ (1 / (2 : ℝ)) := hsqrt
    _ = (∫ a, ‖s a‖ ^ (2 : ℝ) ∂ν_pop) ^ (1 / (2 : ℝ)) := by
          simp [Real.norm_eq_abs]
    _ = ENNReal.toReal (eLpNorm s (2 : ENNReal) ν_pop) := by
          symm
          exact htoReal

end L2IntegralBridge

section ApproximateMoments

variable [IsProbabilityMeasure ν_pop]

theorem attrMean_abs_le_of_bounded_ae
    (hs : Integrable s ν_pop)
    (hBound : BoundedAE (ν_pop := ν_pop) s C) :
    |attrMean ν_pop s| ≤ C := by
  have h1 : |∫ a, s a ∂ν_pop| ≤ ∫ a, |s a| ∂ν_pop := by
    simpa using (abs_integral_le_integral_abs (f := s) (μ := ν_pop))
  have h2 : ∫ a, |s a| ∂ν_pop ≤ ∫ a, C ∂ν_pop := by
    have hs_abs : Integrable (fun a => |s a|) ν_pop := hs.abs
    have hC_int : Integrable (fun _ : Attr => C) ν_pop := integrable_const _
    exact integral_mono_ae hs_abs hC_int hBound
  have hconst : ∫ a, C ∂ν_pop = C := by
    simp
  simpa [attrMean, hconst] using (le_trans h1 h2)

theorem attrMean_diff_le_of_approx_ae
    (hs : Integrable s ν_pop)
    (ht : Integrable t ν_pop)
    (hApprox : ApproxInvarianceAE (ν_pop := ν_pop) s t ε) :
    |attrMean ν_pop s - attrMean ν_pop t| ≤ ε := by
  have hst : Integrable (fun a => s a - t a) ν_pop := hs.sub ht
  have h1 :
      |attrMean ν_pop s - attrMean ν_pop t|
        =
      |∫ a, (s a - t a) ∂ν_pop| := by
    simp [attrMean, integral_sub, hs, ht]
  have h2 : |∫ a, (s a - t a) ∂ν_pop| ≤ ∫ a, |s a - t a| ∂ν_pop := by
    simpa using
      (abs_integral_le_integral_abs (f := fun a => s a - t a) (μ := ν_pop))
  have h3 : ∫ a, |s a - t a| ∂ν_pop ≤ ε := by
    have hst_abs : Integrable (fun a => |s a - t a|) ν_pop := hst.abs
    have hε_int : Integrable (fun _ : Attr => ε) ν_pop := integrable_const _
    have hle := integral_mono_ae hst_abs hε_int hApprox
    have hconst : ∫ a, ε ∂ν_pop = ε := by
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

theorem attrM2_diff_le_of_approx_ae
    (hs : AttrMomentAssumptions (ν_pop := ν_pop) s)
    (ht : AttrMomentAssumptions (ν_pop := ν_pop) t)
    (hBoundS : BoundedAE (ν_pop := ν_pop) s C)
    (hBoundT : BoundedAE (ν_pop := ν_pop) t C)
    (hApprox : ApproxInvarianceAE (ν_pop := ν_pop) s t ε)
    (hε : 0 ≤ ε) :
    |attrM2 ν_pop s - attrM2 ν_pop t| ≤ 2 * C * ε := by
  have hAE :
      ∀ᵐ a ∂ν_pop, |(s a) ^ 2 - (t a) ^ 2| ≤ 2 * C * ε := by
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
  have hs2 : Integrable (fun a => (s a) ^ 2) ν_pop := hs.int2
  have ht2 : Integrable (fun a => (t a) ^ 2) ν_pop := ht.int2
  have hst2 : Integrable (fun a => (s a) ^ 2 - (t a) ^ 2) ν_pop := hs2.sub ht2
  have h1 :
      |attrM2 ν_pop s - attrM2 ν_pop t|
        =
      |∫ a, ((s a) ^ 2 - (t a) ^ 2) ∂ν_pop| := by
    simp [attrM2, integral_sub, hs2, ht2]
  have h2 :
      |∫ a, ((s a) ^ 2 - (t a) ^ 2) ∂ν_pop|
        ≤
      ∫ a, |(s a) ^ 2 - (t a) ^ 2| ∂ν_pop := by
    simpa using
      (abs_integral_le_integral_abs (f := fun a => (s a) ^ 2 - (t a) ^ 2) (μ := ν_pop))
  have h3 :
      ∫ a, |(s a) ^ 2 - (t a) ^ 2| ∂ν_pop
        ≤
      2 * C * ε := by
    have hst2_abs : Integrable (fun a => |(s a) ^ 2 - (t a) ^ 2|) ν_pop := hst2.abs
    have hC_int : Integrable (fun _ : Attr => 2 * C * ε) ν_pop := integrable_const _
    have hle := integral_mono_ae hst2_abs hC_int hAE
    have hconst : ∫ a, 2 * C * ε ∂ν_pop = 2 * C * ε := by
      simp
    simpa [hconst] using hle
  simpa [h1] using (le_trans h2 h3)

theorem attrVar_diff_le_of_approx_ae
    (hs : AttrMomentAssumptions (ν_pop := ν_pop) s)
    (ht : AttrMomentAssumptions (ν_pop := ν_pop) t)
    (hBoundS : BoundedAE (ν_pop := ν_pop) s C)
    (hBoundT : BoundedAE (ν_pop := ν_pop) t C)
    (hApprox : ApproxInvarianceAE (ν_pop := ν_pop) s t ε)
    (hε : 0 ≤ ε) :
    |attrVar ν_pop s - attrVar ν_pop t| ≤ 4 * C * ε := by
  have hmean_diff :
      |attrMean ν_pop s - attrMean ν_pop t| ≤ ε :=
    attrMean_diff_le_of_approx_ae (ν_pop := ν_pop) (s := s) (t := t)
      hs.int1 ht.int1 hApprox
  have hmean_s :
      |attrMean ν_pop s| ≤ C :=
    attrMean_abs_le_of_bounded_ae (ν_pop := ν_pop) (s := s)
      hs.int1 hBoundS
  have hmean_t :
      |attrMean ν_pop t| ≤ C :=
    attrMean_abs_le_of_bounded_ae (ν_pop := ν_pop) (s := t)
      ht.int1 hBoundT
  have hmean_sq :
      |(attrMean ν_pop s) ^ 2 - (attrMean ν_pop t) ^ 2| ≤ 2 * C * ε := by
    have hsum : |attrMean ν_pop s + attrMean ν_pop t| ≤
        |attrMean ν_pop s| + |attrMean ν_pop t| := by
      simpa using (abs_add_le (attrMean ν_pop s) (attrMean ν_pop t))
    have hfact :
        (attrMean ν_pop s) ^ 2 - (attrMean ν_pop t) ^ 2
          =
        (attrMean ν_pop s - attrMean ν_pop t)
          * (attrMean ν_pop s + attrMean ν_pop t) := by
      ring
    have hmul :
        |(attrMean ν_pop s) ^ 2 - (attrMean ν_pop t) ^ 2|
          =
        |attrMean ν_pop s - attrMean ν_pop t|
          * |attrMean ν_pop s + attrMean ν_pop t| := by
      simp [hfact, abs_mul]
    calc
      |(attrMean ν_pop s) ^ 2 - (attrMean ν_pop t) ^ 2|
          = |attrMean ν_pop s - attrMean ν_pop t|
              * |attrMean ν_pop s + attrMean ν_pop t| := hmul
      _   ≤ ε * (|attrMean ν_pop s| + |attrMean ν_pop t|) := by
              have hnonneg : 0 ≤ |attrMean ν_pop s + attrMean ν_pop t| := abs_nonneg _
              exact mul_le_mul hmean_diff hsum hnonneg hε
      _   ≤ ε * (C + C) := by
              have hsum_le : |attrMean ν_pop s| + |attrMean ν_pop t| ≤ C + C := by nlinarith
              exact mul_le_mul_of_nonneg_left hsum_le hε
      _   = 2 * C * ε := by ring
  have hM2 :
      |attrM2 ν_pop s - attrM2 ν_pop t| ≤ 2 * C * ε :=
    attrM2_diff_le_of_approx_ae (ν_pop := ν_pop) (s := s) (t := t)
      hs ht hBoundS hBoundT hApprox hε
  have hvar :
      attrVar ν_pop s - attrVar ν_pop t
        =
      (attrM2 ν_pop s - attrM2 ν_pop t)
        - ((attrMean ν_pop s) ^ 2 - (attrMean ν_pop t) ^ 2) := by
    simp [attrVar, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have htriangle :
      |attrVar ν_pop s - attrVar ν_pop t|
        ≤ |attrM2 ν_pop s - attrM2 ν_pop t|
            + |(attrMean ν_pop t) ^ 2 - (attrMean ν_pop s) ^ 2| := by
    have h :=
      abs_add_le (attrM2 ν_pop s - attrM2 ν_pop t)
        (-(attrMean ν_pop s ^ 2 - attrMean ν_pop t ^ 2))
    simpa [hvar, sub_eq_add_neg, abs_neg, abs_sub_comm,
      add_comm, add_left_comm, add_assoc] using h
  have hsum : |attrM2 ν_pop s - attrM2 ν_pop t|
        + |(attrMean ν_pop t) ^ 2 - (attrMean ν_pop s) ^ 2|
          ≤ 4 * C * ε := by
    have hmean_sq' :
        |(attrMean ν_pop t) ^ 2 - (attrMean ν_pop s) ^ 2| ≤ 2 * C * ε := by
      simpa [abs_sub_comm] using hmean_sq
    nlinarith [hM2, hmean_sq']
  exact le_trans htriangle hsum

theorem attrSD_diff_le_of_approx_ae
    (hs : AttrMomentAssumptions (ν_pop := ν_pop) s)
    (ht : AttrMomentAssumptions (ν_pop := ν_pop) t)
    (hBoundS : BoundedAE (ν_pop := ν_pop) s C)
    (hBoundT : BoundedAE (ν_pop := ν_pop) t C)
    (hApprox : ApproxInvarianceAE (ν_pop := ν_pop) s t ε)
    (hε : 0 ≤ ε)
    (hVarS : 0 ≤ attrVar ν_pop s) (hVarT : 0 ≤ attrVar ν_pop t) :
    |attrSD ν_pop s - attrSD ν_pop t| ≤ Real.sqrt (4 * C * ε) := by
  have hvar :
      |attrVar ν_pop s - attrVar ν_pop t| ≤ 4 * C * ε :=
    attrVar_diff_le_of_approx_ae (ν_pop := ν_pop) (s := s) (t := t)
      hs ht hBoundS hBoundT hApprox hε
  have hsd :
      |attrSD ν_pop s - attrSD ν_pop t|
        ≤ Real.sqrt |attrVar ν_pop s - attrVar ν_pop t| := by
    simpa [attrSD] using
      (abs_sqrt_sub_sqrt_le_sqrt_abs_sub (a := attrVar ν_pop s) (b := attrVar ν_pop t)
        hVarS hVarT)
  have hsqrt :
      Real.sqrt |attrVar ν_pop s - attrVar ν_pop t|
        ≤ Real.sqrt (4 * C * ε) := by
    apply Real.sqrt_le_sqrt
    exact hvar
  exact le_trans hsd hsqrt

end ApproximateMoments

end Approximate

end ConjointSD
