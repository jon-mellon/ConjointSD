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
class ProbMeasureAssumptions (κ : Measure α) : Prop where
  isProb : IsProbabilityMeasure κ

attribute [instance] ProbMeasureAssumptions.isProb

end BasicMeasure

section Transport

variable {Attr : Type*} [MeasurableSpace Attr]

/-!
Notation: throughout this file, `ν` always denotes the target human population
attribute distribution. Use `xiAttr` (generic) or `kappaDesign` (design pushforward)
for non-target attribute laws.
-/

/-- Convenient moment conditions on `s` under the target-population attribute distribution `ν`. -/
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
Invariance only on target-population attribute support (AE under `ν`): the experimental
score agrees with the target-population score `gPop` `ν`-almost everywhere.
This is the minimal transport condition used to link experiment to population.
-/
def InvarianceAE (ν : Measure Attr) (gExp gPop : Attr → ℝ) : Prop :=
  ∀ᵐ x ∂ν, gExp x = gPop x

/-- Approximate invariance on attribute-distribution support: `|s - t| ≤ ε` ν-a.e. -/
def ApproxInvarianceAE (ν : Measure Attr) (s t : Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ᵐ a ∂ν, |s a - t a| ≤ ε

/-- Uniform bound on a score function, ν-a.e. -/
def BoundedAE (ν : Measure Attr) (s : Attr → ℝ) (C : ℝ) : Prop :=
  ∀ᵐ a ∂ν, |s a| ≤ C

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

/-- Score-level measurability and second-moment conditions under the design law. -/
structure ScoreAssumptions (A : ℕ → Ω → Attr) (g : Attr → ℝ) [ProbMeasureAssumptions κ] :
    Prop where
  meas_g : Measurable g
  int_g0_sq : Integrable (fun ω => (g (A 0 ω)) ^ 2) κ

namespace ScoreAssumptions

theorem int_g0 {κ : Measure Ω} [ProbMeasureAssumptions κ] {Attr : Type*} [MeasurableSpace Attr]
    {A : ℕ → Ω → Attr} {g : Attr → ℝ}
    (hIID : DesignAttrIID (κ := κ) A)
    (h : ScoreAssumptions (κ := κ) (A := A) g) :
    Integrable (fun ω => g (A 0 ω)) κ := by
  have hmeasA0 : Measurable (A 0) := hIID.measA 0
  have hmeas : AEStronglyMeasurable (fun ω => g (A 0 ω)) κ :=
    (h.meas_g.comp hmeasA0).aestronglyMeasurable
  have hmem2 : MemLp (fun ω => g (A 0 ω)) (2 : ENNReal) κ :=
    (memLp_two_iff_integrable_sq hmeas).2 h.int_g0_sq
  have hmem1 : MemLp (fun ω => g (A 0 ω)) (1 : ENNReal) κ := hmem2.mono_exponent (by norm_num)
  exact (memLp_one_iff_integrable).1 hmem1

end ScoreAssumptions

variable {B : Type*}

/-- Bundle assumptions for all blocks at once. -/
structure DecompAssumptions (A : ℕ → Ω → Attr) (g : B → Attr → ℝ) : Prop where
  designAttrIID : DesignAttrIID (κ := κ) A
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
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ] (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hIID : EvalAttrIID (κ := ρ) A
  hScore : ScoreAssumptions (κ := ρ) (A := A) (g := gHat g θhat m)

/--
Weighted-evaluation assumptions for a fixed training index `m`.

These package the IID/integrability conditions needed to apply weighted LLNs.
-/
structure SplitEvalWeightAssumptions
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ] (A : ℕ → Ω → Attr)
    (w : Attr → ℝ) (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hIID : EvalAttrIID (κ := ρ) A
  hScore : ScoreAssumptions (κ := ρ) (A := A) (g := gHat g θhat m)
  hWeight : ScoreAssumptions (κ := ρ) (A := A) (g := w)
  hWeightScore :
    ScoreAssumptions (κ := ρ) (A := A)
      (g := fun a => w a * gHat g θhat m a)
  hWeightScoreSq :
    ScoreAssumptions (κ := ρ) (A := A)
      (g := fun a => w a * (gHat g θhat m a) ^ 2)
  hW0 :
    designMeanZ (κ := ρ) (Z := Zcomp (A := A) (g := w)) ≠ 0

/-- Weighted-evaluation assumptions without IID, for cases where IID is derived. -/
structure SplitEvalWeightAssumptionsNoIID
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ] (A : ℕ → Ω → Attr)
    (w : Attr → ℝ) (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hScore : ScoreAssumptions (κ := ρ) (A := A) (g := gHat g θhat m)
  hWeight : ScoreAssumptions (κ := ρ) (A := A) (g := w)
  hWeightScore :
    ScoreAssumptions (κ := ρ) (A := A)
      (g := fun a => w a * gHat g θhat m a)
  hWeightScoreSq :
    ScoreAssumptions (κ := ρ) (A := A)
      (g := fun a => w a * (gHat g θhat m a) ^ 2)
  hW0 :
    designMeanZ (κ := ρ) (Z := Zcomp (A := A) (g := w)) ≠ 0

/-- Boundedness-based assumptions for evaluation at a fixed training index `m`. -/
structure SplitEvalAssumptionsBounded
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hMeas : Measurable (gHat g θhat m)
  hBound : ∃ C, 0 ≤ C ∧ ∀ a, |gHat g θhat m a| ≤ C

end SampleSplitting

section RegressionConsistencyBridge

variable {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]

/--
Continuity assumptions for the induced attribute-distribution functionals at θ0.

Here `xiAttr` is whichever attribute distribution governs the target moments in the
surrounding result (design-law when estimating, population-law when transporting).
These are the “plug point” for regression theory: later you discharge them using
dominated convergence / continuity of link / bounded features / etc.
-/
structure FunctionalContinuityAssumptions
    (xiAttr : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) : Prop where
  cont_mean : ContinuousAt (attrMeanΘ (xiAttr := xiAttr) g) θ0
  cont_m2   : ContinuousAt (attrM2Θ   (xiAttr := xiAttr) g) θ0

/--
Direct plug-in moment convergence assumptions for a score `g θhat n` under `ν`.
This is the Route-1 input for sequential consistency: mean and second moment converge
without invoking parameter continuity.
-/
structure PlugInMomentAssumptions
    (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ) : Prop where
  mean_tendsto :
    Tendsto
      (fun n => attrMean ν (gHat g θhat n))
      atTop
      (nhds (attrMean ν (g θ0)))
  m2_tendsto :
    Tendsto
      (fun n => attrM2 ν (gHat g θhat n))
      atTop
      (nhds (attrM2 ν (g θ0)))

/-- Continuity assumptions for each block score at `θ0`. -/
structure BlockFunctionalContinuityAssumptions
    {B : Type*}
    (xiAttr : Measure Attr) (gB : B → Θ → Attr → ℝ) (θ0 : Θ) : Prop where
  cont : ∀ b : B,
    FunctionalContinuityAssumptions (xiAttr := xiAttr) (blockScoreΘ (gB := gB) b) θ0

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

/--
Moment assumptions stated against the attribute-distribution Gram/cross moments.
Here `xiAttr` names the attribute distribution used in the limit (design-law for fitting,
population-law for transported targets). These encode the LLN and identifiability
conditions typically used for OLS consistency.
-/
structure OLSMomentAssumptionsOfAttr {Attr : Type u} {Term : Type v}
    [MeasurableSpace Attr] [Fintype Term] [DecidableEq Term]
    (xiAttr : Measure Attr)
    (A : ℕ → Attr) (Y : ℕ → ℝ)
    (g : Attr → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ) : Prop where
  gramInv_tendsto :
    ∀ i j,
      Tendsto
        (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j)
        atTop
        (nhds ((attrGram (xiAttr := xiAttr) (φ := φ))⁻¹ i j))
  cross_tendsto :
    ∀ i,
      Tendsto
        (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i)
        atTop
        (nhds (attrCross (xiAttr := xiAttr) (g := g) (φ := φ) i))

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
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
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
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
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

structure PaperOLSPosDefAssumptions
    (xiAttr : Measure Attr)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  gram_posdef :
    (attrGram
        (xiAttr := xiAttr)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).PosDef

structure PaperOLSOrthogonalAssumptions
    (xiAttr : Measure Attr)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop where
  gram_diag :
    ∀ i j, i ≠ j →
      attrMean
          (xiAttr := xiAttr)
          (fun a =>
            φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
              *
            φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)
        = 0
  gram_pos :
    ∀ i,
      attrMean
          (xiAttr := xiAttr)
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
(`A 0` under the evaluation law `ρ`) to the population distribution `ν`
without requiring full law equality.
-/
structure EvalWeightMatchesPopMoments
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (A : ℕ → Ω → Attr)
    (ν : Measure Attr) (w s : Attr → ℝ) : Prop where
  measA0 : Measurable (A 0)
  mean_eq :
    (∫ a, w a * s a ∂kappaDesign (κ := ρ) (A := A)) /
      (∫ a, w a ∂kappaDesign (κ := ρ) (A := A))
      =
    attrMean ν s
  m2_eq :
    (∫ a, w a * (s a) ^ 2 ∂kappaDesign (κ := ρ) (A := A)) /
      (∫ a, w a ∂kappaDesign (κ := ρ) (A := A))
      =
    attrM2 ν s

end SurveyWeights

section ConjointIdentification

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω)
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
      Pairwise (fun i j => IndepFun (U i) (U j) μexp) ∧
      (∀ i, IdentDistrib (U i) (U 0) μexp μexp) ∧
      ∀ i x, (fun ω => U i ω) ⟂ᵢ[μexp] (fun ω => Y x ω)

/-- Randomized-assignment assumptions that imply the `rand` factorization. -/
structure ConjointIdRandomized
    [MeasurableSpace Attr] (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    [ProbMeasureAssumptions μexp] : Prop where
  measX : Measurable X
  measYobs : Measurable Yobs
  measY : ∀ x, Measurable (Y x)
  consistency : ∀ ω, Yobs ω = Y (X ω) ω
  bounded :
    ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Y x ω| ≤ C
  ignorability : ∀ x, (fun ω => X ω) ⟂ᵢ[μexp] (fun ω => Y x ω)

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

section ApproximateOracle

variable {Attr : Type*} [MeasurableSpace Attr]

/--
Two-stage approximation: a flexible score `gFlex` approximates the experimental
causal score `gStar`, and the model score `gModel` approximates `gFlex`, both ν-a.e.
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
  ∀ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
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

/-- Approximate additivity: `gStar` is within ε of an additive main-effects surface. -/
def ApproxNoInteractions
    (μexp : Measure Ω) (Y : Profile K V → Ω → ℝ) (ε : ℝ) : Prop :=
  ∃ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V,
      |gStar (μexp := μexp) (Y := Y) x - (α0 + ∑ k : K, main k (x k))| ≤ ε

end WellSpecifiedFromNoInteractions

end ConjointSD
