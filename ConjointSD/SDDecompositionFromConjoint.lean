import ConjointSD.PredictedSD

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]

/-- i.i.d.-type assumptions on the population-record process A. -/
structure PopIID (A : ℕ → Ω → Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) μ)
  identA : ∀ i, IdentDistrib (A i) (A 0) μ μ

/-- Induced real-valued process from population records via a scoring function g. -/
def Zcomp (A : ℕ → Ω → Attr) (g : Attr → ℝ) : ℕ → Ω → ℝ :=
  fun i ω => g (A i ω)

/-- Sufficient conditions to use `sdHatZ_tendsto_ae` on the induced score process. -/
structure ScoreAssumptions (A : ℕ → Ω → Attr) (g : Attr → ℝ) : Prop where
  popiid : PopIID (μ := μ) A
  meas_g : Measurable g
  int_g0 : Integrable (fun ω => g (A 0 ω)) μ
  int_g0_sq : Integrable (fun ω => (g (A 0 ω)) ^ 2) μ

/-!
Simplification: bounded scores give the integrability assumptions automatically.
-/

/-- Bounded measurable real functions are integrable under a finite measure. -/
lemma integrable_of_bounded
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hmeas : Measurable f) (hbound : ∃ C, 0 ≤ C ∧ ∀ ω, |f ω| ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC0, hC⟩ := hbound
  refine Integrable.of_bound (hf := hmeas.aestronglyMeasurable) C ?_
  refine ae_of_all μ ?_
  intro ω
  have hC' := hC ω
  simpa [Real.norm_eq_abs] using hC'

lemma scoreAssumptions_of_bounded
    [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (hPop : PopIID (μ := μ) A)
    (hMeas : Measurable g)
    (hBound : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ScoreAssumptions (μ := μ) A g := by
  obtain ⟨C, hC0, hC⟩ := hBound
  have hmeasA0 : Measurable (A 0) := hPop.measA 0
  have hmeas_gA0 : Measurable (fun ω => g (A 0 ω)) := hMeas.comp hmeasA0
  have hbound_gA0 : ∃ C, 0 ≤ C ∧ ∀ ω, |g (A 0 ω)| ≤ C := by
    refine ⟨C, hC0, ?_⟩
    intro ω
    exact hC (A 0 ω)
  have hint_gA0 : Integrable (fun ω => g (A 0 ω)) μ :=
    integrable_of_bounded (μ := μ) hmeas_gA0 hbound_gA0
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
  have hint_sq : Integrable (fun ω => (g (A 0 ω)) ^ 2) μ :=
    integrable_of_bounded (μ := μ) hmeas_sq hbound_sq
  exact ⟨hPop, hMeas, hint_gA0, hint_sq⟩

/-- From `ScoreAssumptions`, derive `IIDAssumptions` for Z := Zcomp A g. -/
lemma iidAssumptions_Zcomp [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (h : ScoreAssumptions (μ := μ) A g) :
    IIDAssumptions (μ := μ) (Zcomp (A := A) (g := g)) := by
  let Z : ℕ → Ω → ℝ := Zcomp (A := A) (g := g)
  refine ⟨?intZ, ?indepZ, ?identZ, ?intZ2⟩
  · simpa [Z, Zcomp] using h.int_g0
  · intro i j hij
    have hijA : IndepFun (A i) (A j) μ := h.popiid.indepA hij
    have : IndepFun (g ∘ (A i)) (g ∘ (A j)) μ :=
      hijA.comp h.meas_g h.meas_g
    simpa [Z, Zcomp, Function.comp] using this
  · intro i
    have hiA : IdentDistrib (A i) (A 0) μ μ := h.popiid.identA i
    have : IdentDistrib (g ∘ (A i)) (g ∘ (A 0)) μ μ :=
      hiA.comp h.meas_g
    simpa [Z, Zcomp, Function.comp] using this
  · simpa [Z, Zcomp] using h.int_g0_sq

/-- Consistency of the plug-in SD for a single component scoring rule g. -/
theorem sd_component_consistent [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (h : ScoreAssumptions (μ := μ) A g) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (popSDZ (μ := μ) (Zcomp (A := A) (g := g)))) := by
  have hIID : IIDAssumptions (μ := μ) (Zcomp (A := A) (g := g)) :=
    iidAssumptions_Zcomp (μ := μ) (A := A) (g := g) h
  simpa using (sdHatZ_tendsto_ae (μ := μ) (Z := Zcomp (A := A) (g := g)) hIID)

theorem sd_component_consistent_of_bounded [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr) (g : Attr → ℝ)
    (hPop : PopIID (μ := μ) A)
    (hMeas : Measurable g)
    (hBound : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g)) n ω)
        atTop
        (nhds (popSDZ (μ := μ) (Zcomp (A := A) (g := g)))) := by
  have hScore :
      ScoreAssumptions (μ := μ) (A := A) (g := g) :=
    scoreAssumptions_of_bounded
      (μ := μ) (A := A) (g := g) (hPop := hPop) (hMeas := hMeas) (hBound := hBound)
  exact sd_component_consistent (μ := μ) (A := A) (g := g) hScore

/-!
Finite-family “decomposition”: blocks/buckets b : B each have a scoring rule g b.
We prove consistency of the plug-in SD for each block, and allow boundedness to
discharge the integrability requirements automatically.
-/

variable {B : Type*}

/-- Bundle assumptions for all blocks at once. -/
structure DecompAssumptions (A : ℕ → Ω → Attr) (g : B → Attr → ℝ) : Prop where
  popiid : PopIID (μ := μ) A
  meas_g : ∀ b, Measurable (g b)
  bound_g : ∀ b, ∃ C, 0 ≤ C ∧ ∀ a, |g b a| ≤ C

/-- SD consistency for any chosen block b. -/
theorem sd_block_consistent [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Attr) (g : B → Attr → ℝ)
    (h : DecompAssumptions (μ := μ) (B := B) A g)
    (b : B) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g b)) n ω)
        atTop
        (nhds (popSDZ (μ := μ) (Zcomp (A := A) (g := g b)))) := by
  have hb : ScoreAssumptions (μ := μ) (A := A) (g := g b) :=
    scoreAssumptions_of_bounded
      (μ := μ) (A := A) (g := g b)
      (hPop := h.popiid) (hMeas := h.meas_g b) (hBound := h.bound_g b)
  exact sd_component_consistent (μ := μ) (A := A) (g := g b) hb

end ConjointSD
