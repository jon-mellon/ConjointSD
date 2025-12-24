import ConjointSD.PredictedSD

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

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

/-- From `ScoreAssumptions`, derive `IIDAssumptions` for Z := Zcomp A g. -/
lemma iidAssumptions_Zcomp
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
theorem sd_component_consistent
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

/-!
Finite-family “decomposition”: blocks/buckets b : B each have a scoring rule g b.
We prove consistency of the plug-in SD for each block.
-/

variable {B : Type*} [Fintype B]

/-- Bundle assumptions for all blocks at once. -/
structure DecompAssumptions (A : ℕ → Ω → Attr) (g : B → Attr → ℝ) : Prop where
  popiid : PopIID (μ := μ) A
  meas_g : ∀ b, Measurable (g b)
  int_g0 : ∀ b, Integrable (fun ω => g b (A 0 ω)) μ
  int_g0_sq : ∀ b, Integrable (fun ω => (g b (A 0 ω)) ^ 2) μ

/-- SD consistency for any chosen block b. -/
theorem sd_block_consistent
    (A : ℕ → Ω → Attr) (g : B → Attr → ℝ)
    (h : DecompAssumptions (μ := μ) (B := B) A g)
    (b : B) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => sdHatZ (Z := Zcomp (A := A) (g := g b)) n ω)
        atTop
        (nhds (popSDZ (μ := μ) (Zcomp (A := A) (g := g b)))) := by
  have hb : ScoreAssumptions (μ := μ) (A := A) (g := g b) := by
    refine ⟨?popiid, ?meas, ?int0, ?int0sq⟩
    · exact h.popiid
    · exact h.meas_g b
    · exact h.int_g0 b
    · exact h.int_g0_sq b
  exact sd_component_consistent (μ := μ) (A := A) (g := g b) hb

end ConjointSD
