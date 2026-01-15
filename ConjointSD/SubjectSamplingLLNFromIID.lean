import Mathlib
import ConjointSD.Assumptions
import ConjointSD.SDDecompositionFromConjoint

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section SubjectSampling

variable {Ω Person Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Person]
variable [MeasurableSpace Attr]

omit [MeasurableSpace Attr] in
theorem subject_lln_gPop_of_iid
    {μexp : Measure Ω} {μpop : Measure Person}
    [IsProbabilityMeasure μpop]
    {R : ℕ → Ω → Person} {gP : Person → Attr → ℝ}
    (hIID : SubjectSamplingIID (μexp := μexp) (μpop := μpop) (R := R))
    (hScore : SubjectScoreAssumptions (μpop := μpop) (gP := gP)) :
    ∀ x,
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n => gHatSubject (R := R) (gP := gP) n x ω)
          atTop
          (nhds (gPop (μpop := μpop) gP x)) := by
  intro x
  classical
  let X : ℕ → Ω → ℝ := fun n ω => gP (R n ω) x
  have hmeas_g : Measurable (fun p => gP p x) := hScore.meas_gP x
  have hint_map : Integrable (fun p => gP p x) (Measure.map (R 0) μexp) := by
    have hbound : ∃ C, 0 ≤ C ∧ ∀ p, |gP p x| ≤ C := hScore.bound_gP x
    have hint : Integrable (fun p => gP p x) μpop :=
      integrable_of_bounded (μexp := μpop) hmeas_g hbound
    simpa [hIID.identR 0] using hint
  have hint : Integrable (X 0) μexp := by
    simpa [X] using hint_map.comp_measurable (hIID.measR 0)
  have hindep : Pairwise (fun i j => IndepFun (X i) (X j) μexp) := by
    intro i j hij
    have hR : IndepFun (R i) (R j) μexp := hIID.indepR hij
    exact hR.comp hmeas_g hmeas_g
  have hident : ∀ i, IdentDistrib (X i) (X 0) μexp μexp := by
    intro i
    have hmap :
        Measure.map (R i) μexp = Measure.map (R 0) μexp := by
      simp [hIID.identR i, hIID.identR 0]
    have hIdentR : IdentDistrib (R i) (R 0) μexp μexp :=
      { aemeasurable_fst := (hIID.measR i).aemeasurable
        aemeasurable_snd := (hIID.measR 0).aemeasurable
        map_eq := hmap }
    exact hIdentR.comp hmeas_g
  have hstrong :
      ∀ᵐ ω ∂μexp,
        Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n)
          atTop
          (nhds (μexp[X 0])) :=
    strong_law_ae_real X hint hindep hident
  have hmean : μexp[X 0] = gPop (μpop := μpop) gP x := by
    have hmap : Measure.map (R 0) μexp = μpop := hIID.identR 0
    have hmap_integral :
        (∫ p, gP p x ∂Measure.map (R 0) μexp)
          =
        (∫ ω, gP (R 0 ω) x ∂μexp) := by
      simpa using
        (integral_map (μ := μexp) (φ := R 0)
          (hφ := (hIID.measR 0).aemeasurable)
          (f := fun p => gP p x)
          (hfm := hmeas_g.aestronglyMeasurable))
    calc
      μexp[X 0]
          =
        (∫ ω, gP (R 0 ω) x ∂μexp) := by rfl
      _ =
        (∫ p, gP p x ∂Measure.map (R 0) μexp) := hmap_integral.symm
      _ = gPop (μpop := μpop) gP x := by
        simp [gPop, hmap]
  filter_upwards [hstrong] with ω hω
  have hω' :
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n)
        atTop
        (nhds (gPop (μpop := μpop) gP x)) := by
    simpa [hmean] using hω
  simpa [gHatSubject, X, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hω'

theorem subjectSamplingLLN_of_iid_of_lln_gStar
    {μexp : Measure Ω} [IsProbabilityMeasure μexp]
    {ν_pop : Measure Attr} {μpop : Measure Person} [IsProbabilityMeasure μpop]
    {R : ℕ → Ω → Person} {gP : Person → Attr → ℝ} {Y : Attr → Ω → ℝ}
    (hIID : SubjectSamplingIID (μexp := μexp) (μpop := μpop) (R := R))
    (hScore : SubjectScoreAssumptions (μpop := μpop) (gP := gP))
    (hStar : SubjectSamplingLLNStar
      (μexp := μexp) (ν_pop := ν_pop) (μpop := μpop) (R := R) (gP := gP) (Y := Y)) :
    SubjectSamplingLLN
      (μexp := μexp) (ν_pop := ν_pop) (μpop := μpop) (R := R) (gP := gP) (Y := Y) := by
  refine { lln_gStar := hStar.lln_gStar, lln_gPop := ?_ }
  exact subject_lln_gPop_of_iid (hIID := hIID) (hScore := hScore)

theorem subject_lln_pointwise_eq_of_iid
    {μexp : Measure Ω} [IsProbabilityMeasure μexp]
    {ν_pop : Measure Attr} {μpop : Measure Person} [IsProbabilityMeasure μpop]
    {R : ℕ → Ω → Person} {gP : Person → Attr → ℝ} {Y : Attr → Ω → ℝ}
    (hIID : SubjectSamplingIID (μexp := μexp) (μpop := μpop) (R := R))
    (hScore : SubjectScoreAssumptions (μpop := μpop) (gP := gP))
    (hStar : SubjectSamplingLLNStar
      (μexp := μexp) (ν_pop := ν_pop) (μpop := μpop) (R := R) (gP := gP) (Y := Y)) :
    ∀ x, gStar (μexp := μexp) (Y := Y) x = gPop (μpop := μpop) gP x := by
  classical
  intro x
  have hStarLLN := hStar.lln_gStar x
  have hPopLLN := subject_lln_gPop_of_iid (hIID := hIID) (hScore := hScore) x
  by_contra hne
  have hboth :
      ∀ᵐ ω ∂μexp,
        Tendsto
            (fun n => gHatSubject (R := R) (gP := gP) n x ω)
            atTop
            (nhds (gStar (μexp := μexp) (Y := Y) x))
          ∧
        Tendsto
            (fun n => gHatSubject (R := R) (gP := gP) n x ω)
            atTop
            (nhds (gPop (μpop := μpop) gP x)) :=
    hStarLLN.and hPopLLN
  have hfalse : ∀ᵐ _ω ∂μexp, False := by
    refine hboth.mono ?_
    intro ω hω
    exact hne (tendsto_nhds_unique hω.1 hω.2)
  have hzero_univ : μexp Set.univ = 0 := by
    have hfalse' : μexp { ω | ¬False } = 0 := (MeasureTheory.ae_iff).1 hfalse
    convert hfalse' using 1; simp
  have hone : μexp Set.univ = 1 := by
    exact measure_univ
  exact zero_ne_one (hzero_univ.symm.trans hone)

theorem subject_lln_ae_eq_of_iid
    {μexp : Measure Ω} [IsProbabilityMeasure μexp]
    {ν_pop : Measure Attr} {μpop : Measure Person} [IsProbabilityMeasure μpop]
    {R : ℕ → Ω → Person} {gP : Person → Attr → ℝ} {Y : Attr → Ω → ℝ}
    (hIID : SubjectSamplingIID (μexp := μexp) (μpop := μpop) (R := R))
    (hScore : SubjectScoreAssumptions (μpop := μpop) (gP := gP))
    (hStar : SubjectSamplingLLNStar
      (μexp := μexp) (ν_pop := ν_pop) (μpop := μpop) (R := R) (gP := gP) (Y := Y)) :
    ∀ᵐ x ∂ν_pop, gStar (μexp := μexp) (Y := Y) x = gPop (μpop := μpop) gP x := by
  refine ae_of_all _ ?_
  intro x
  exact subject_lln_pointwise_eq_of_iid (hIID := hIID) (hScore := hScore) (hStar := hStar) x

end SubjectSampling

end ConjointSD
