import ConjointSD.PredictedSD
import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]

/-!
Simplification: bounded scores give the integrability assumptions automatically.
-/

/-- Bounded measurable real functions are integrable under a finite measure. -/
lemma integrable_of_bounded
    (μexp : Measure Ω) [IsFiniteMeasure μexp] {f : Ω → ℝ}
    (hmeas : Measurable f) (hbound : ∃ C, 0 ≤ C ∧ ∀ ω, |f ω| ≤ C) :
    Integrable f μexp := by
  obtain ⟨C, hC0, hC⟩ := hbound
  refine Integrable.of_bound (hf := hmeas.aestronglyMeasurable) C ?_
  refine ae_of_all μexp ?_
  intro ω
  have hC' := hC ω
  simpa [Real.norm_eq_abs] using hC'

lemma scoreAssumptions_of_bounded
    [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (hPop : DesignAttrIID (κ := μexp) A)
    (hMeas : Measurable g)
    (hBound : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ScoreAssumptions (κ := μexp) A g := by
  obtain ⟨C, hC0, hC⟩ := hBound
  have hmeasA0 : Measurable (A 0) := hPop.measA 0
  have hmeas_gA0 : Measurable (fun ω => g (A 0 ω)) := hMeas.comp hmeasA0
  have hbound_gA0 : ∃ C, 0 ≤ C ∧ ∀ ω, |g (A 0 ω)| ≤ C := by
    refine ⟨C, hC0, ?_⟩
    intro ω
    exact hC (A 0 ω)
  have hint_gA0 : Integrable (fun ω => g (A 0 ω)) μexp :=
    integrable_of_bounded (μexp := μexp) hmeas_gA0 hbound_gA0
  have hmeas_sq : Measurable (fun ω => (g (A 0 ω)) ^ 2) := by
    simpa [pow_two] using (hmeas_gA0.mul hmeas_gA0)
  have hbound_sq : ∃ C2, 0 ≤ C2 ∧ ∀ ω, |(g (A 0 ω)) ^ 2| ≤ C2 := by
    refine ⟨C ^ 2, ?_, ?_⟩
    · nlinarith
    · intro ω
      have hCω : |g (A 0 ω)| ≤ C := hC (A 0 ω)
      have hmul : |g (A 0 ω)| * |g (A 0 ω)| ≤ C * C :=
        mul_le_mul hCω hCω (abs_nonneg _) hC0
      simpa [pow_two, abs_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hint_sq : Integrable (fun ω => (g (A 0 ω)) ^ 2) μexp :=
    integrable_of_bounded (μexp := μexp) hmeas_sq hbound_sq
  exact ⟨hPop, hMeas, hint_sq⟩

lemma meanHatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (h : ScoreAssumptions (κ := μexp) A g) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => meanHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := g)))) := by
  let Z : ℕ → Ω → ℝ := Zcomp (A := A) (g := g)
  have hInd : Pairwise (fun i j => IndepFun (Z i) (Z j) μexp) := by
    intro i j hij
    have hijA : IndepFun (A i) (A j) μexp := h.designAttrIID.indepA hij
    have : IndepFun (g ∘ (A i)) (g ∘ (A j)) μexp :=
      hijA.comp h.meas_g h.meas_g
    simpa [Z, Zcomp, Function.comp] using this
  have hId : ∀ i, IdentDistrib (Z i) (Z 0) μexp μexp := by
    intro i
    have hiA : IdentDistrib (A i) (A 0) μexp μexp := h.designAttrIID.identA i
    have : IdentDistrib (g ∘ (A i)) (g ∘ (A 0)) μexp μexp :=
      hiA.comp h.meas_g
    simpa [Z, Zcomp, Function.comp] using this
  have hInt : Integrable (Z 0) μexp := by
    simpa [Z, Zcomp] using h.int_g0
  simpa [meanHatZ, designMeanZ, Z] using
    (ProbabilityTheory.strong_law_ae (μ := μexp) (X := Z) hInt hInd hId)

lemma m2HatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (h : ScoreAssumptions (κ := μexp) A g) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => m2HatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designM2Z (κ := μexp) (Z := Zcomp (A := A) (g := g)))) := by
  let Z : ℕ → Ω → ℝ := Zcomp (A := A) (g := g)
  let Zsq : ℕ → Ω → ℝ := fun i ω => (Z i ω) ^ 2
  have hInt : Integrable (Zsq 0) μexp := by
    simpa [Z, Zcomp, Zsq] using h.int_g0_sq
  have hInd : Pairwise (fun i j => IndepFun (Zsq i) (Zsq j) μexp) := by
    intro i j hij
    have hijA : IndepFun (A i) (A j) μexp := h.designAttrIID.indepA hij
    have hijZ : IndepFun (g ∘ (A i)) (g ∘ (A j)) μexp :=
      hijA.comp h.meas_g h.meas_g
    have : IndepFun ((fun x : ℝ => x ^ 2) ∘ (g ∘ (A i)))
        ((fun x : ℝ => x ^ 2) ∘ (g ∘ (A j))) μexp :=
      hijZ.comp measurable_sq measurable_sq
    simpa [Z, Zcomp, Zsq, Function.comp] using this
  have hId : ∀ i, IdentDistrib (Zsq i) (Zsq 0) μexp μexp := by
    intro i
    have hiA : IdentDistrib (A i) (A 0) μexp μexp := h.designAttrIID.identA i
    have hiZ : IdentDistrib (g ∘ (A i)) (g ∘ (A 0)) μexp μexp :=
      hiA.comp h.meas_g
    have : IdentDistrib ((fun x : ℝ => x ^ 2) ∘ (g ∘ (A i)))
        ((fun x : ℝ => x ^ 2) ∘ (g ∘ (A 0))) μexp μexp :=
      hiZ.comp measurable_sq
    simpa [Z, Zcomp, Zsq, Function.comp] using this
  have hslln :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n : ℕ =>
            ((n : ℝ)⁻¹) • (Finset.sum (Finset.range n) fun i => Zsq i ω))
          atTop
          (nhds (∫ ω, Zsq 0 ω ∂μexp)) :=
    ProbabilityTheory.strong_law_ae (μ := μexp) (X := Zsq) hInt hInd hId
  simpa [m2HatZ, designM2Z, Zsq] using hslln

lemma rmseHatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (h : ScoreAssumptions (κ := μexp) A g) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => rmseHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designRMSEZ (κ := μexp) (Z := Zcomp (A := A) (g := g)))) := by
  have hm2 := m2HatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := g) h
  refine hm2.mono ?_
  intro ω hm2ω
  have hsqrt :
      Tendsto Real.sqrt (nhds (designM2Z (κ := μexp) (Z := Zcomp (A := A) (g := g))))
        (nhds (Real.sqrt (designM2Z (κ := μexp) (Z := Zcomp (A := A) (g := g))))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  simpa [rmseHatZ, designRMSEZ] using (hsqrt.comp hm2ω)

lemma varHatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (h : ScoreAssumptions (κ := μexp) A g) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => varHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designVarZ (κ := μexp) (Z := Zcomp (A := A) (g := g)))) := by
  have hmean := meanHatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := g) h
  have hm2 := m2HatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := g) h
  refine (hmean.and hm2).mono ?_
  intro ω hω
  rcases hω with ⟨hmeanω, hm2ω⟩
  have hmean2 :
      Tendsto (fun n : ℕ => (meanHatZ (Z := Zcomp (A := A) (g := g)) n ω) ^ 2) atTop
        (nhds ((designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := g))) ^ 2)) := by
    simpa [pow_two] using (hmeanω.mul hmeanω)
  have :
      Tendsto
        (fun n : ℕ =>
          m2HatZ (Z := Zcomp (A := A) (g := g)) n ω
            - (meanHatZ (Z := Zcomp (A := A) (g := g)) n ω) ^ 2)
        atTop
        (nhds
          (designM2Z (κ := μexp) (Z := Zcomp (A := A) (g := g))
            - (designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := g))) ^ 2)) :=
    hm2ω.sub hmean2
  simpa [varHatZ, designVarZ] using this

theorem sdHatZ_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (h : ScoreAssumptions (κ := μexp) A g) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designSDZ (κ := μexp) (Zcomp (A := A) (g := g)))) := by
  have hvar := varHatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := g) h
  refine hvar.mono ?_
  intro ω hω
  have hsqrt :
      Tendsto Real.sqrt
        (nhds (designVarZ (κ := μexp) (Z := Zcomp (A := A) (g := g))))
        (nhds (Real.sqrt (designVarZ (κ := μexp) (Z := Zcomp (A := A) (g := g))))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  simpa [sdHatZ, designSDZ] using (hsqrt.comp hω)

lemma meanHatZW_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (w g : Attr → ℝ)
    (hWZ : ScoreAssumptions (κ := μexp) A (fun a => w a * g a))
    (hW : ScoreAssumptions (κ := μexp) A w)
    (hW0 : designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := w)) ≠ 0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ =>
          meanHatZW (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w)) n ω)
        atTop
        (nhds
          (designMeanZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w)))) := by
  have hmeanWZ :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n : ℕ =>
            meanHatZ
                (Z := fun i ω =>
                  Wcomp (A := A) (w := w) i ω * Zcomp (A := A) (g := g) i ω) n ω)
          atTop
          (nhds
            (designMeanZ (κ := μexp)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω * Zcomp (A := A) (g := g) i ω))) := by
    simpa [Wcomp, Zcomp] using
      meanHatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := fun a => w a * g a) hWZ
  have hmeanW :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n : ℕ => meanHatZ (Z := Wcomp (A := A) (w := w)) n ω)
          atTop
          (nhds (designMeanZ (κ := μexp) (Z := Wcomp (A := A) (w := w)))) := by
    simpa [Wcomp, Zcomp] using
      meanHatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := w) hW
  refine (hmeanWZ.and hmeanW).mono ?_
  intro ω hω
  rcases hω with ⟨hWZω, hWω⟩
  have hpair :
      Tendsto
        (fun n : ℕ =>
          (meanHatZ (Z := fun i ω => Wcomp (A := A) (w := w) i ω * Zcomp (A := A) (g := g) i ω) n ω,
            meanHatZ (Z := Wcomp (A := A) (w := w)) n ω))
        atTop
        (nhds
          (designMeanZ (κ := μexp)
            (Z := fun i ω => Wcomp (A := A) (w := w) i ω * Zcomp (A := A) (g := g) i ω),
           designMeanZ (κ := μexp) (Z := Wcomp (A := A) (w := w)))) := by
    simpa [nhds_prod_eq] using hWZω.prodMk hWω
  have hcont :
      ContinuousAt (fun p : ℝ × ℝ => p.1 / p.2)
        (designMeanZ (κ := μexp)
            (Z := fun i ω =>
              Wcomp (A := A) (w := w) i ω * Zcomp (A := A) (g := g) i ω),
          designMeanZ (κ := μexp) (Z := Wcomp (A := A) (w := w))) :=
    (ContinuousAt.div continuousAt_fst continuousAt_snd hW0)
  have hdiv := hcont.tendsto.comp hpair
  simpa [meanHatZW, designMeanZW] using hdiv

lemma m2HatZW_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (w g : Attr → ℝ)
    (hWZ2 : ScoreAssumptions (κ := μexp) A (fun a => w a * (g a) ^ 2))
    (hW : ScoreAssumptions (κ := μexp) A w)
    (hW0 : designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := w)) ≠ 0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ =>
          m2HatZW (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w)) n ω)
        atTop
        (nhds
          (designM2ZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w)))) := by
  have hmeanWZ2 :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n : ℕ =>
            meanHatZ
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω * (Zcomp (A := A) (g := g) i ω) ^ 2) n ω)
          atTop
          (nhds
            (designMeanZ (κ := μexp)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω * (Zcomp (A := A) (g := g) i ω) ^ 2))) := by
    simpa [Wcomp, Zcomp] using
      meanHatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := fun a => w a * (g a) ^ 2) hWZ2
  have hmeanW :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n : ℕ => meanHatZ (Z := Wcomp (A := A) (w := w)) n ω)
          atTop
          (nhds (designMeanZ (κ := μexp) (Z := Wcomp (A := A) (w := w)))) := by
    simpa [Wcomp, Zcomp] using
      meanHatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := w) hW
  refine (hmeanWZ2.and hmeanW).mono ?_
  intro ω hω
  rcases hω with ⟨hWZ2ω, hWω⟩
  have hpair :
      Tendsto
        (fun n : ℕ =>
          (meanHatZ
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω * (Zcomp (A := A) (g := g) i ω) ^ 2) n ω,
            meanHatZ (Z := Wcomp (A := A) (w := w)) n ω))
        atTop
        (nhds
          (designMeanZ (κ := μexp)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω * (Zcomp (A := A) (g := g) i ω) ^ 2),
            designMeanZ (κ := μexp) (Z := Wcomp (A := A) (w := w)))) := by
    simpa [nhds_prod_eq] using hWZ2ω.prodMk hWω
  have hcont :
      ContinuousAt (fun p : ℝ × ℝ => p.1 / p.2)
        (designMeanZ (κ := μexp)
            (Z := fun i ω =>
              Wcomp (A := A) (w := w) i ω * (Zcomp (A := A) (g := g) i ω) ^ 2),
          designMeanZ (κ := μexp) (Z := Wcomp (A := A) (w := w))) :=
    (ContinuousAt.div continuousAt_fst continuousAt_snd hW0)
  have hdiv := hcont.tendsto.comp hpair
  simpa [m2HatZW, designM2ZW] using hdiv

lemma varHatZW_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (w g : Attr → ℝ)
    (hWZ : ScoreAssumptions (κ := μexp) A (fun a => w a * g a))
    (hWZ2 : ScoreAssumptions (κ := μexp) A (fun a => w a * (g a) ^ 2))
    (hW : ScoreAssumptions (κ := μexp) A w)
    (hW0 : designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := w)) ≠ 0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ =>
          varHatZW (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w)) n ω)
        atTop
        (nhds
          (designVarZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w)))) := by
  have hmean :=
    meanHatZW_tendsto_ae_of_score (μexp := μexp) (A := A) (w := w) (g := g) hWZ hW hW0
  have hm2 :=
    m2HatZW_tendsto_ae_of_score (μexp := μexp) (A := A) (w := w) (g := g) hWZ2 hW hW0
  refine (hmean.and hm2).mono ?_
  intro ω hω
  rcases hω with ⟨hmeanω, hm2ω⟩
  have hmean2 :
      Tendsto
        (fun n : ℕ =>
          (meanHatZW (Z := Zcomp (A := A) (g := g))
              (W := Wcomp (A := A) (w := w)) n ω) ^ 2)
        atTop
        (nhds
          ((designMeanZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
              (W := Wcomp (A := A) (w := w))) ^ 2)) := by
    simpa [pow_two] using (hmeanω.mul hmeanω)
  have :
      Tendsto
        (fun n : ℕ =>
          m2HatZW (Z := Zcomp (A := A) (g := g))
              (W := Wcomp (A := A) (w := w)) n ω
            - (meanHatZW (Z := Zcomp (A := A) (g := g))
                (W := Wcomp (A := A) (w := w)) n ω) ^ 2)
        atTop
        (nhds
          (designM2ZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
              (W := Wcomp (A := A) (w := w))
            - (designMeanZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
                (W := Wcomp (A := A) (w := w))) ^ 2)) :=
    hm2ω.sub hmean2
  simpa [varHatZW, designVarZW] using this

theorem sdHatZW_tendsto_ae_of_score [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (w g : Attr → ℝ)
    (hWZ : ScoreAssumptions (κ := μexp) A (fun a => w a * g a))
    (hWZ2 : ScoreAssumptions (κ := μexp) A (fun a => w a * (g a) ^ 2))
    (hW : ScoreAssumptions (κ := μexp) A w)
    (hW0 : designMeanZ (κ := μexp) (Z := Zcomp (A := A) (g := w)) ≠ 0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ =>
          sdHatZW (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w)) n ω)
        atTop
        (nhds
          (designSDZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w)))) := by
  have hvar :=
    varHatZW_tendsto_ae_of_score (μexp := μexp) (A := A) (w := w) (g := g) hWZ hWZ2 hW hW0
  refine hvar.mono ?_
  intro ω hω
  have hsqrt :
      Tendsto Real.sqrt
        (nhds
          (designVarZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
            (W := Wcomp (A := A) (w := w))))
        (nhds
          (Real.sqrt
            (designVarZW (κ := μexp) (Z := Zcomp (A := A) (g := g))
              (W := Wcomp (A := A) (w := w))))) :=
    (Real.continuous_sqrt.continuousAt).tendsto
  simpa [sdHatZW, designSDZW] using (hsqrt.comp hω)

/-- Consistency of the plug-in SD for a single component scoring rule g. -/
theorem sd_component_consistent [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (h : ScoreAssumptions (κ := μexp) A g) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designSDZ (κ := μexp) (Zcomp (A := A) (g := g)))) := by
  simpa using sdHatZ_tendsto_ae_of_score (μexp := μexp) (A := A) (g := g) h

theorem sd_component_consistent_of_bounded [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (hPop : DesignAttrIID (κ := μexp) A)
    (hMeas : Measurable g)
    (hBound : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (designSDZ (κ := μexp) (Zcomp (A := A) (g := g)))) := by
  have hScore :
      ScoreAssumptions (κ := μexp) (A := A) (g := g) :=
    scoreAssumptions_of_bounded
      (μexp := μexp) (A := A) (g := g) (hPop := hPop) (hMeas := hMeas) (hBound := hBound)
  exact sd_component_consistent (μexp := μexp) (A := A) (g := g) hScore

/-!
Finite-family “decomposition”: blocks/buckets b : B each have a scoring rule g b.
We prove consistency of the plug-in SD for each block, and allow boundedness to
discharge the integrability requirements automatically.
-/

variable {B : Type*}

/-- SD consistency for any chosen block b. -/
theorem sd_block_consistent [ProbMeasureAssumptions μexp]
    (A : ℕ → Ω → Attr) (g : B → Attr → ℝ)
    (h : DecompAssumptions (κ := μexp) (B := B) A g)
    (b : B) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g b)) n ω)
        atTop
        (nhds (designSDZ (κ := μexp) (Zcomp (A := A) (g := g b)))) := by
  have hb : ScoreAssumptions (κ := μexp) (A := A) (g := g b) :=
    scoreAssumptions_of_bounded
      (μexp := μexp) (A := A) (g := g b)
      (hPop := h.designAttrIID) (hMeas := h.meas_g b) (hBound := h.bound_g b)
  exact sd_component_consistent (μexp := μexp) (A := A) (g := g b) hb

end ConjointSD
