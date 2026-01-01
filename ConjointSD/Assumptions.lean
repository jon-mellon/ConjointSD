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

section BasicMeasure

variable {α : Type*} [MeasurableSpace α]

/-- Bundled probability-measure assumption (used to avoid standalone `IsProbabilityMeasure`). -/
class ProbMeasureAssumptions (μ : Measure α) : Prop where
  isProb : IsProbabilityMeasure μ

attribute [instance] ProbMeasureAssumptions.isProb

end BasicMeasure

section Transport

variable {Attr : Type*} [MeasurableSpace Attr]

/-- Convenient moment conditions on `s` under an attribute distribution `ν`. -/
structure AttrMomentAssumptions (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (s : Attr → ℝ) : Prop where
  aemeas : AEMeasurable s ν
  int2 : Integrable (fun a => (s a) ^ 2) ν

namespace AttrMomentAssumptions

theorem int1 {ν : Measure Attr} [ProbMeasureAssumptions ν] {s : Attr → ℝ}
    (hs : AttrMomentAssumptions (ν := ν) s) : Integrable s ν := by
  have hs_meas : AEStronglyMeasurable s ν := hs.aemeas.aestronglyMeasurable
  have hs_mem2 : MemLp s (2 : ENNReal) ν :=
    (memLp_two_iff_integrable_sq hs_meas).2 hs.int2
  have hs_mem1 : MemLp s (1 : ENNReal) ν := hs_mem2.mono_exponent (by norm_num)
  exact (memLp_one_iff_integrable).1 hs_mem1

end AttrMomentAssumptions

/--
Invariance only on attribute-distribution support (AE under `ν`): `gExp = gPop` holds
`ν`-almost everywhere.
This is often the right minimal transport condition.
-/
def InvarianceAE (ν : Measure Attr) (gExp gPop : Attr → ℝ) : Prop :=
  ∀ᵐ x ∂ν, gExp x = gPop x

end Transport

section Positivity

/-- Bundle positivity of ε. -/
structure EpsilonAssumptions (ε : ℝ) : Prop where
  pos : 0 < ε

end Positivity

section SDDecomposition

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]

/--
i.i.d.-type assumptions on the attribute-record process A under the experimental
design distribution.
-/
structure DesignAttrIID (A : ℕ → Ω → Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) μ)
  identA : ∀ i, IdentDistrib (A i) (A 0) μ μ

/-- Sufficient conditions to use score-based SD consistency lemmas on the induced score process. -/
structure ScoreAssumptions (A : ℕ → Ω → Attr) (g : Attr → ℝ) [ProbMeasureAssumptions μ] :
    Prop where
  designAttrIID : DesignAttrIID (μ := μ) A
  meas_g : Measurable g
  int_g0_sq : Integrable (fun ω => (g (A 0 ω)) ^ 2) μ

namespace ScoreAssumptions

theorem int_g0 {μ : Measure Ω} [ProbMeasureAssumptions μ] {Attr : Type*} [MeasurableSpace Attr]
    {A : ℕ → Ω → Attr} {g : Attr → ℝ} (h : ScoreAssumptions (μ := μ) (A := A) g) :
    Integrable (fun ω => g (A 0 ω)) μ := by
  have hmeasA0 : Measurable (A 0) := h.designAttrIID.measA 0
  have hmeas : AEStronglyMeasurable (fun ω => g (A 0 ω)) μ :=
    (h.meas_g.comp hmeasA0).aestronglyMeasurable
  have hmem2 : MemLp (fun ω => g (A 0 ω)) (2 : ENNReal) μ :=
    (memLp_two_iff_integrable_sq hmeas).2 h.int_g0_sq
  have hmem1 : MemLp (fun ω => g (A 0 ω)) (1 : ENNReal) μ := hmem2.mono_exponent (by norm_num)
  exact (memLp_one_iff_integrable).1 hmem1

end ScoreAssumptions

variable {B : Type*}

/-- Bundle assumptions for all blocks at once. -/
structure DecompAssumptions (A : ℕ → Ω → Attr) (g : B → Attr → ℝ) : Prop where
  designAttrIID : DesignAttrIID (μ := μ) A
  meas_g : ∀ b, Measurable (g b)
  bound_g : ∀ b, ∃ C, 0 ≤ C ∧ ∀ a, |g b a| ≤ C

end SDDecomposition

section SampleSplitting

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/--
Assumptions needed to evaluate the empirical SD of the score `gHat g θhat m`
on draws `A n` from the evaluation process.
-/
structure SplitEvalAssumptions
    (μ : Measure Ω) [ProbMeasureAssumptions μ] (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hScore : ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m)

/--
Weighted-evaluation assumptions for a fixed training index `m`.

These package the IID/integrability conditions needed to apply weighted LLNs.
-/
structure SplitEvalWeightAssumptions
    (μ : Measure Ω) [ProbMeasureAssumptions μ] (A : ℕ → Ω → Attr)
    (w : Attr → ℝ) (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hScore : ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m)
  hWeight : ScoreAssumptions (μ := μ) (A := A) (g := w)
  hWeightScore :
    ScoreAssumptions (μ := μ) (A := A)
      (g := fun a => w a * gHat g θhat m a)
  hWeightScoreSq :
    ScoreAssumptions (μ := μ) (A := A)
      (g := fun a => w a * (gHat g θhat m a) ^ 2)
  hW0 :
    designMeanZ (μ := μ) (Z := Zcomp (A := A) (g := w)) ≠ 0

/-- Boundedness-based assumptions for evaluation at a fixed training index `m`. -/
structure SplitEvalAssumptionsBounded
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hMeas : Measurable (gHat g θhat m)
  hBound : ∃ C, 0 ≤ C ∧ ∀ a, |gHat g θhat m a| ≤ C

end SampleSplitting

section RegressionConsistencyBridge

variable {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]

/--
Continuity assumptions for the induced attribute-distribution functionals at θ0.

These are the “plug point” for regression theory: later you discharge them using
dominated convergence / continuity of link / bounded features / etc.
-/
structure FunctionalContinuityAssumptions
    (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) : Prop where
  cont_mean : ContinuousAt (attrMeanΘ (ν := ν) g) θ0
  cont_m2   : ContinuousAt (attrM2Θ   (ν := ν) g) θ0

/-- Continuity assumptions for each block score at `θ0`. -/
structure BlockFunctionalContinuityAssumptions
    {B : Type*}
    (ν : Measure Attr) (gB : B → Θ → Attr → ℝ) (θ0 : Θ) : Prop where
  cont : ∀ b : B,
    FunctionalContinuityAssumptions (ν := ν) (blockScoreΘ (gB := gB) b) θ0

end RegressionConsistencyBridge

section RegressionEstimator

universe u v

/-- OLS moment assumptions with explicit limits for the inverse Gram and cross moments. -/
structure OLSMomentAssumptions {Attr : Type u} {Term : Type v}
    [Fintype Term] [DecidableEq Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ) : Type (max u v) where
  /-- Limit of the inverse Gram matrix entries. -/
  gramInvLimit : Matrix Term Term ℝ
  /-- Limit of the cross-moment vector entries. -/
  crossLimit : Term → ℝ
  gramInv_tendsto :
    ∀ i j,
      Tendsto
        (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j)
        atTop
        (nhds (gramInvLimit i j))
  cross_tendsto :
    ∀ i,
      Tendsto
        (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i)
        atTop
        (nhds (crossLimit i))
  theta0_eq : θ0 = gramInvLimit.mulVec crossLimit

/--
Moment assumptions stated against the attribute-distribution Gram/cross moments.
These encode the LLN and identifiability conditions typically used for OLS consistency.
-/
structure OLSMomentAssumptionsOfAttr {Attr : Type u} {Term : Type v}
    [MeasurableSpace Attr] [Fintype Term] [DecidableEq Term]
    (ν : Measure Attr)
    (A : ℕ → Attr) (Y : ℕ → ℝ)
    (g : Attr → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ) : Prop where
  gramInv_tendsto :
    ∀ i j,
      Tendsto
        (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j)
        atTop
        (nhds ((attrGram (ν := ν) (φ := φ))⁻¹ i j))
  cross_tendsto :
    ∀ i,
      Tendsto
        (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i)
        atTop
        (nhds (attrCross (ν := ν) (g := g) (φ := φ) i))
  theta0_eq :
    θ0 = (attrGram (ν := ν) (φ := φ))⁻¹.mulVec (attrCross (ν := ν) (g := g) (φ := φ))

end RegressionEstimator

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
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    {Term : Type*}
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : ℕ → Ω → ℝ)
    (φ : Term → Attr → ℝ) : Prop where
  condMean_zero :
    ∀ i a,
      condMean (μ := μ)
          (fun ω => Yobs i ω - gStar (μ := μ) (Y := Y) (A i ω))
          (eventX (X := A i) a)
        = 0
  noise_lln :
    ∀ i,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            ((n : ℝ)⁻¹) *
              ∑ k ∈ Finset.range n,
                φ i (A k ω)
                  * (Yobs k ω - gStar (μ := μ) (Y := Y) (A k ω)))
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
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (A : ℕ → Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : ℕ → Ω → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  obs_noise :
    ObservationNoiseAssumptions
      (μ := μ) (A := A) (Y := Y) (Yobs := Yobs)
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
  meas_fMain : ∀ m, Measurable (fMain m)
  meas_fInter : ∀ i, Measurable (fInter i)
  bound_fMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C
  bound_fInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C
  meas_gStar : Measurable (gStar (μ := μ) (Y := Y))
  bound_gStar : ∃ C, 0 ≤ C ∧ ∀ a, |gStar (μ := μ) (Y := Y) a| ≤ C

/-!
Additional design-side assumptions used to derive full-rank and identification
properties for the paper OLS model.
-/

structure PaperOLSFullRankAssumptions
    (ν : Measure Attr)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  gram_isUnit :
    IsUnit
      (attrGram
        (ν := ν)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))

structure PaperOLSPosDefAssumptions
    (ν : Measure Attr)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  gram_posdef :
    (attrGram
        (ν := ν)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).PosDef

structure PaperOLSOrthogonalAssumptions
    (ν : Measure Attr)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  gram_diag :
    ∀ i j, i ≠ j →
      attrMean
          (ν := ν)
          (fun a =>
            φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
              *
            φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)
        = 0
  gram_pos :
    ∀ i,
      attrMean
          (ν := ν)
          (fun a =>
            φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
              *
            φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
        ≠ 0

end PaperOLSDesign

section SurveyWeights

variable {Attr : Type*} [MeasurableSpace Attr]

/--
Evaluation-weight moment matching: weighted moments of the evaluation draw
match target human population moments under `ν`.

This is a transport-style assumption that links the evaluation sample
(`A 0` under `μ`) to the population distribution `ν` without requiring full
law equality.
-/
structure EvalWeightMatchesAttrMoments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (ν : Measure Attr) (w s : Attr → ℝ) : Prop where
  measA0 : Measurable (A 0)
  mean_eq :
    (∫ a, w a * s a ∂Measure.map (A 0) μ) / (∫ a, w a ∂Measure.map (A 0) μ)
      =
    attrMean ν s
  m2_eq :
    (∫ a, w a * (s a) ^ 2 ∂Measure.map (A 0) μ) / (∫ a, w a ∂Measure.map (A 0) μ)
      =
    attrM2 ν s

end SurveyWeights

section ConjointIdentification

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)
variable {Attr : Type*} [MeasurableSpace Attr]

/--
Assumption 2 (no profile-order effects within a task): permuting the order of
profiles within a task does not change the task-level potential outcome.
-/
structure NoProfileOrderEffects
    {Task J Attr : Type*} (Y : Task → OrderedProfiles J Attr → Ω → ℝ) : Prop where
  permute : ∀ k t (π : Equiv.Perm J), Y k (permuteProfiles π t) = Y k t

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
      Pairwise (fun i j => IndepFun (U i) (U j) μ) ∧
      (∀ i, IdentDistrib (U i) (U 0) μ μ) ∧
      ∀ i x, (fun ω => U i ω) ⟂ᵢ[μ] (fun ω => Y x ω)

/-- Randomized-assignment assumptions that imply the `rand` factorization. -/
structure ConjointIdRandomized
    [MeasurableSpace Attr] (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    [ProbMeasureAssumptions μ] : Prop where
  measX : Measurable X
  measYobs : Measurable Yobs
  measY : ∀ x, Measurable (Y x)
  consistency : ∀ ω, Yobs ω = Y (X ω) ω
  bounded :
    ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Y x ω| ≤ C
  ignorability : ∀ x, (fun ω => X ω) ⟂ᵢ[μ] (fun ω => Y x ω)

end ConjointIdentification

section ConjointIdentificationLemmas

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
variable (μ : Measure Ω)

lemma DesignAttrIID.of_randomization_stream
    {A : ℕ → Ω → Attr} {Y : Attr → Ω → ℝ}
    (h : ConjointRandomizationStream (μ := μ) (A := A) (Y := Y)) :
    DesignAttrIID (μ := μ) A := by
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
    have hU : IndepFun (U i) (U j) μ := hindep hij
    have hA :
        IndepFun (fun ω => f (U i ω)) (fun ω => f (U j ω)) μ :=
      hU.comp hmeasf hmeasf
    simpa [hAeq i, hAeq j] using hA
  · intro i
    have hU : IdentDistrib (U i) (U 0) μ μ := hident i
    have hA : IdentDistrib (fun ω => f (U i ω)) (fun ω => f (U 0 ω)) μ μ :=
      hU.comp hmeasf
    simpa [hAeq i, hAeq 0] using hA

end ConjointIdentificationLemmas

section ApproximateOracle

variable {Attr : Type*} [MeasurableSpace Attr]

/--
Two-stage approximation: a flexible score `gFlex` approximates the true target,
and the model score `gModel` approximates `gFlex`, both ν-a.e.
-/
def ApproxOracleAE
    (ν : Measure Attr)
    (gModel gFlex gStar : Attr → ℝ) (δModel δOracle : ℝ) : Prop :=
  (∀ᵐ x ∂ν, |gModel x - gFlex x| ≤ δModel) ∧
  (∀ᵐ x ∂ν, |gFlex x - gStar x| ≤ δOracle)

/--
L2-style approximation: the model score differs from the target by at most delta in mean-square.
-/
def L2Approx
    (ν : Measure Attr)
    (gModel gTarget : Attr → ℝ) (δ : ℝ) : Prop :=
  MemLp (fun a => gModel a - gTarget a) (ENNReal.ofReal 2) ν ∧
  Real.sqrt (∫ a, |gModel a - gTarget a| ^ 2 ∂ν) ≤ δ

end ApproximateOracle

section WellSpecifiedFromNoInteractions

variable {Ω : Type*} [MeasurableSpace Ω]
variable {K : Type*} {V : K → Type*} [Fintype K]

/-!
## “No interactions” as exact additivity of the conjoint estimand `gStar`
-/

variable {Term : Type*} [Fintype Term]

/--
Full main-effect term set: any additive main-effect surface can be expressed by
`gLin` with the given term features.
-/
def FullMainEffectsTerms
    (φ : Term → Profile K V → ℝ) : Prop :=
  ∀ (μ0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∃ β : Term → ℝ,
      ∀ x : Profile K V,
        gLin (Attr := Profile K V) (Term := Term) (β := β) (φ := φ) x
          =
        μ0 + ∑ k : K, main k (x k)

/-- “No interactions”: there exist `μ0` and main effects `main` giving exact additivity. -/
def NoInteractions
    (μ : Measure Ω) (Y : Profile K V → Ω → ℝ) : Prop :=
  ∃ (μ0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V, gStar (μ := μ) (Y := Y) x = μ0 + ∑ k : K, main k (x k)

/-- Approximate additivity: `gStar` is within ε of an additive main-effects surface. -/
def ApproxNoInteractions
    (μ : Measure Ω) (Y : Profile K V → Ω → ℝ) (ε : ℝ) : Prop :=
  ∃ (μ0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V,
      |gStar (μ := μ) (Y := Y) x - (μ0 + ∑ k : K, main k (x k))| ≤ ε

end WellSpecifiedFromNoInteractions

end ConjointSD
