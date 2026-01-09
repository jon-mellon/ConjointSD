import Mathlib
import ConjointSD.Defs

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
open scoped Topology

noncomputable section
namespace ConjointSD

/-!
# Assumption packages

All assumption structures/props are centralized here for easier auditing.
Core definitions they depend on live in `ConjointSD.Defs`.
-/

section Transport

variable {Attr : Type*} [MeasurableSpace Attr]

/-!
Notation: throughout this file, `ν_pop` always denotes the target human population
attribute distribution. Use `xiAttr` (generic) or `kappaDesign` (design pushforward)
for non-target attribute laws.
-/

/-- Uniform bound on a score function, ν_pop-a.e. -/
def BoundedAE (ν_pop : Measure Attr) (s : Attr → ℝ) (C : ℝ) : Prop :=
  ∀ᵐ a ∂ν_pop, |s a| ≤ C

/-- Convenient moment conditions on `s` under the target-population
attribute distribution `ν_pop`. -/
structure AttrMomentAssumptions (ν_pop : Measure Attr) [IsProbabilityMeasure ν_pop]
    (s : Attr → ℝ) : Prop where
  aemeas : AEMeasurable s ν_pop
  bound : ∃ C, 0 ≤ C ∧ BoundedAE ν_pop s C

namespace AttrMomentAssumptions

theorem int2 {ν_pop : Measure Attr} [IsProbabilityMeasure ν_pop] {s : Attr → ℝ}
    (hs : AttrMomentAssumptions (ν_pop := ν_pop) s) :
    Integrable (fun a => (s a) ^ 2) ν_pop := by
  obtain ⟨C, hC0, hC⟩ := hs.bound
  have hs_meas : AEStronglyMeasurable s ν_pop := hs.aemeas.aestronglyMeasurable
  have hs_meas_sq : AEStronglyMeasurable (fun a => (s a) ^ 2) ν_pop := by
    simpa [pow_two] using hs_meas.mul hs_meas
  refine Integrable.of_bound (hf := hs_meas_sq) (C ^ 2) ?_
  refine hC.mono ?_
  intro a ha
  have hmul : |s a| * |s a| ≤ C * C :=
    mul_le_mul ha ha (abs_nonneg _) hC0
  calc
    ‖(s a) ^ 2‖ = |(s a) ^ 2| := rfl
    _ = |s a| * |s a| := by simp [pow_two, abs_mul]
    _ ≤ C ^ 2 := by simpa [pow_two] using hmul

theorem int1 {ν_pop : Measure Attr} [IsProbabilityMeasure ν_pop] {s : Attr → ℝ}
    (hs : AttrMomentAssumptions (ν_pop := ν_pop) s) : Integrable s ν_pop := by
  have hs_meas : AEStronglyMeasurable s ν_pop := hs.aemeas.aestronglyMeasurable
  have hs_mem2 : MemLp s (2 : ENNReal) ν_pop :=
    (memLp_two_iff_integrable_sq hs_meas).2 hs.int2
  have hs_mem1 : MemLp s (1 : ENNReal) ν_pop := hs_mem2.mono_exponent (by norm_num)
  exact (memLp_one_iff_integrable).1 hs_mem1

end AttrMomentAssumptions

end Transport

section Positivity

/-- Bundle positivity of ε. -/
structure EpsilonAssumptions (ε : ℝ) : Prop where
  pos : 0 < ε

end Positivity

section SDDecomposition

variable {Ω : Type*} [MeasurableSpace Ω]
variable (κ : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]

/--
i.i.d.-type assumptions on the attribute-record process A under the experimental
design distribution.
-/
structure DesignAttrIID (A : ℕ → Ω → Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) κ)
  identA : ∀ i, IdentDistrib (A i) (A 0) κ κ

/--
i.i.d.-type assumptions on the attribute-record process A under the evaluation
distribution. This is intentionally distinct from `DesignAttrIID` so evaluation
sampling can be assumed independently of design randomization.
-/
structure EvalAttrIID (A : ℕ → Ω → Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) κ)
  identA : ∀ i, IdentDistrib (A i) (A 0) κ κ

variable {B : Type*}

end SDDecomposition

section SampleSplitting

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/--
Evaluation assumptions under boundedness, for a fixed training index `m`.
-/
structure SplitEvalAssumptionsBounded
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ) (m : ℕ) : Prop where
  hIID : EvalAttrIID (κ := ρ) A
  hMeasG : Measurable (gHat g θhat m)
  hBoundG : ∃ C, 0 ≤ C ∧ ∀ a, |gHat g θhat m a| ≤ C

end SampleSplitting

section SubjectSampling

variable {Ω Person Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Person]
variable [MeasurableSpace Attr]

/-- IID experiment-subject sampling from the population law. -/
structure SubjectSamplingIID
    (μexp : Measure Ω) (μpop : Measure Person) (R : ℕ → Ω → Person) : Prop where
  measR : ∀ i, Measurable (R i)
  indepR : Pairwise (fun i j => IndepFun (R i) (R j) μexp)
  identR : ∀ i, Measure.map (R i) μexp = μpop

/-- Measurability/boundedness conditions for subject-level scores under `μpop`. -/
structure SubjectScoreAssumptions
    (μpop : Measure Person) (gP : Person → Attr → ℝ) : Prop where
  meas_gP : ∀ x, Measurable (fun p => gP p x)
  bound_gP : ∀ x, ∃ C, 0 ≤ C ∧ ∀ p, |gP p x| ≤ C

/--
Pointwise LLN for experiment-subject scores, with an explicit transport target
`gPop` and a link to the experimental estimand `gStar`.
-/
structure SubjectSamplingLLN
    (μexp : Measure Ω) (ν_pop : Measure Attr) (μpop : Measure Person)
    (R : ℕ → Ω → Person) (gP : Person → Attr → ℝ) (Y : Attr → Ω → ℝ) : Prop where
  lln_gStar :
    ∀ x,
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n => gHatSubject (R := R) (gP := gP) n x ω)
          atTop
          (nhds (gStar (μexp := μexp) (Y := Y) x))
  lln_gPop :
    ∀ x,
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n => gHatSubject (R := R) (gP := gP) n x ω)
          atTop
          (nhds (gPop (μpop := μpop) gP x))

/-- LLN assumption for experiment-subject averages converging to `gStar`. -/
structure SubjectSamplingLLNStar
    (μexp : Measure Ω) (ν_pop : Measure Attr) (μpop : Measure Person)
    (R : ℕ → Ω → Person) (gP : Person → Attr → ℝ) (Y : Attr → Ω → ℝ) : Prop where
  lln_gStar :
    ∀ x,
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n => gHatSubject (R := R) (gP := gP) n x ω)
          atTop
          (nhds (gStar (μexp := μexp) (Y := Y) x))

end SubjectSampling

section PaperOLSDesign

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable [DecidableEq (PaperTerm Main Inter)]

/--
Observation-noise assumptions for OLS cross moments: the feature-weighted
noise averages converge to zero along sample paths.

This is a mean-zero/noise-LLN condition relative to the true score `gStar`,
stated directly in terms of the empirical cross term.
-/
structure ObservationNoiseAssumptions
    (μexp : Measure Ω) [IsProbabilityMeasure μexp]
    {Term : Type*}
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : ℕ → Ω → ℝ)
    (φ : Term → Attr → ℝ) : Prop where
  condMean_zero :
    ∀ i a,
      condMean (κ := μexp)
          (fun ω => Yobs i ω - gStar (μexp := μexp) (Y := Y) (A i ω))
          (eventX (X := A i) a)
        = 0
  noise_lln :
    ∀ i,
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n : ℕ =>
            ((n : ℝ)⁻¹) *
              ∑ k ∈ Finset.range n,
                φ i (A k ω)
                  * (Yobs k ω - gStar (μexp := μexp) (Y := Y) (A k ω)))
          atTop
          (nhds 0)

/--
Paper OLS design-side assumptions that are sufficient to derive the LLN hypotheses
for the Gram and cross moments used in OLS consistency.

These bundle measurability/boundedness of the paper feature map and boundedness
of the conjoint causal estimand `gStar`. The design IID assumption is kept
separate (as `DesignAttrIID`) and passed explicitly to lemmas that need it.
-/
structure PaperOLSDesignAssumptions
    (μexp : Measure Ω) [IsProbabilityMeasure μexp]
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : ℕ → Ω → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  obs_noise :
    ObservationNoiseAssumptions
      (μexp := μexp) (A := A) (Y := Y) (Yobs := Yobs)
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
  meas_fMain : ∀ m, Measurable (fMain m)
  meas_fInter : ∀ i, Measurable (fInter i)
  bound_fMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C
  bound_fInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C
  meas_gStar : Measurable (gStar (μexp := μexp) (Y := Y))
  bound_gStar : ∃ C, 0 ≤ C ∧ ∀ a, |gStar (μexp := μexp) (Y := Y) a| ≤ C

/-!
Additional design-side assumptions used to derive full-rank and identification
properties for the paper OLS model.
-/

structure PaperOLSFullRankAssumptions
    (xiAttr : Measure Attr)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  gram_isUnit :
    IsUnit
      (attrGram
        (xiAttr := xiAttr)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))

end PaperOLSDesign

section EvaluationSampling

variable {Attr : Type*} [MeasurableSpace Attr]

/--
Evaluation sample is an IID draw from the target population attribute law `ν_pop`:
the evaluation attribute distribution equals `ν_pop`.
-/
structure EvalAttrLawEqPop
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (ν_pop : Measure Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) ρ)
  identA : ∀ i, Measure.map (A i) ρ = ν_pop

end EvaluationSampling

section ConjointIdentification

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω)
variable {Attr : Type*} [MeasurableSpace Attr]

/--
Randomization mechanism for an attribute stream `A i`.

Each draw `A i` is generated by a measurable function of a randomization variable `U i`,
the randomization variables are i.i.d. across indices, and each `U i` is independent
of every potential outcome `Y x`.
-/
structure ConjointRandomizationStream
    [MeasurableSpace Attr] (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ) : Prop where
  exists_randomization :
    ∃ (R : Type 0) (_ : MeasurableSpace R) (U : ℕ → Ω → R) (f : R → Attr),
      (∀ i, Measurable (U i)) ∧
      Measurable f ∧
      (∀ i, A i = fun ω => f (U i ω)) ∧
      Pairwise (fun i j => IndepFun (U i) (U j) μexp) ∧
      (∀ i, IdentDistrib (U i) (U 0) μexp μexp) ∧
      ∀ i x, (fun ω => U i ω) ⟂ᵢ[μexp] (fun ω => Y x ω)

end ConjointIdentification

section ConjointIdentificationLemmas

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
variable (μexp : Measure Ω)

lemma DesignAttrIID.of_randomization_stream
    {A : ℕ → Ω → Attr} {Y : Attr → Ω → ℝ}
    (h : ConjointRandomizationStream (μexp := μexp) (A := A) (Y := Y)) :
    DesignAttrIID (κ := μexp) A := by
  rcases h.exists_randomization with
    ⟨R, instR, U, f, hmeasU, hmeasf, hAeq, hindep, hident, hUindepY⟩
  letI : MeasurableSpace R := instR
  refine
    { measA := ?_
      indepA := ?_
      identA := ?_ }
  · intro i
    simpa [hAeq i] using hmeasf.comp (hmeasU i)
  · intro i j hij
    have hU : IndepFun (U i) (U j) μexp := hindep hij
    have hA :
        IndepFun (fun ω => f (U i ω)) (fun ω => f (U j ω)) μexp :=
      hU.comp hmeasf hmeasf
    simpa [hAeq i, hAeq j] using hA
  · intro i
    have hU : IdentDistrib (U i) (U 0) μexp μexp := hident i
    have hA : IdentDistrib (fun ω => f (U i ω)) (fun ω => f (U 0 ω)) μexp μexp :=
      hU.comp hmeasf
    simpa [hAeq i, hAeq 0] using hA

end ConjointIdentificationLemmas


section WellSpecifiedFromNoInteractions

variable {Ω : Type*} [MeasurableSpace Ω]
variable {K : Type*} {V : K → Type*} [Fintype K]

/-!
## “No interactions” as exact additivity of the conjoint estimand `gStar`
-/

variable {Term : Type*} [Fintype Term]

/--
Main-effect term representability: whenever the true conjoint estimand is additive,
the term features can represent that specific additive surface.
-/
def MainEffectsRepresentable
    (μexp : Measure Ω) (Y : Profile K V → Ω → ℝ)
    (φ : Term → Profile K V → ℝ) : Prop :=
  ∀ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    (∀ x : Profile K V, gStar (μexp := μexp) (Y := Y) x = α0 + ∑ k : K, main k (x k)) →
    ∃ β : Term → ℝ,
      ∀ x : Profile K V,
        gLin (Attr := Profile K V) (Term := Term) (β := β) (φ := φ) x
          =
        α0 + ∑ k : K, main k (x k)

/-- “No interactions”: there exist `α0` and main effects `main` giving exact additivity. -/
def NoInteractions
    (μexp : Measure Ω) (Y : Profile K V → Ω → ℝ) : Prop :=
  ∃ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V, gStar (μexp := μexp) (Y := Y) x = α0 + ∑ k : K, main k (x k)

end WellSpecifiedFromNoInteractions

end ConjointSD
