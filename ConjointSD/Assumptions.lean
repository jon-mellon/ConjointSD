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

section MapLaw

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]

/-- Bundle measurability of `A 0` with its pushforward law. -/
structure MapLawAssumptions (μ : Measure Ω) (A : ℕ → Ω → Attr) (ν : Measure Attr) : Prop where
  measA0 : Measurable (A 0)
  map_eq : Measure.map (A 0) μ = ν

end MapLaw

section Convergence

variable {Θ : Type*} [TopologicalSpace Θ]

/-- Bundle convergence of an estimator sequence. -/
structure ThetaTendstoAssumptions (θhat : ℕ → Θ) (θ0 : Θ) : Prop where
  tendsto : Tendsto θhat atTop (nhds θ0)

end Convergence

section Positivity

/-- Bundle positivity of ε. -/
structure EpsilonAssumptions (ε : ℝ) : Prop where
  pos : 0 < ε

end Positivity

section PredictedSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

/-- IID + moment assumptions for applying the strong law to Z and Z^2. -/
structure IIDAssumptions (Z : ℕ → Ω → ℝ) [ProbMeasureAssumptions μ] : Prop where
  indep : Pairwise (fun i j => IndepFun (Z i) (Z j) μ)
  ident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ
  intZ2 : Integrable (fun ω => (Z 0 ω) ^ 2) μ

namespace IIDAssumptions

theorem intZ {μ : Measure Ω} [ProbMeasureAssumptions μ] {Z : ℕ → Ω → ℝ}
    (h : IIDAssumptions (μ := μ) Z) : Integrable (Z 0) μ := by
  have hmeas : AEStronglyMeasurable (Z 0) μ :=
    (h.ident 0).aemeasurable_fst.aestronglyMeasurable
  have hmem2 : MemLp (Z 0) (2 : ENNReal) μ :=
    (memLp_two_iff_integrable_sq hmeas).2 h.intZ2
  have hmem1 : MemLp (Z 0) (1 : ENNReal) μ := hmem2.mono_exponent (by norm_num)
  exact (memLp_one_iff_integrable).1 hmem1

end IIDAssumptions

end PredictedSD

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

/-- Sufficient conditions to use `sdHatZ_tendsto_ae` on the induced score process. -/
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

section EstimatedG

variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/--
Assumptions ensuring replacing oracle `g θ0` with estimated `g (θhat n)` does not change
target human population moments (under the attribute distribution `ν`) in the limit.

Minimal version: assume convergence of mean and second moment; derive var and sd.
-/
structure GEstimationAssumptions
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ) : Prop where
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

end EstimatedG

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

/-- Boundedness-based assumptions for evaluation at a fixed training index `m`. -/
structure SplitEvalAssumptionsBounded
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hPop : DesignAttrIID (μ := μ) A
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

/--
Assumptions used to prove consistency of the OLS estimator sequence.
This packages the convergence `θhat → θ0`; the remaining statistical conditions
can be discharged for the paper's design in a dedicated instantiation.
-/
structure OLSConsistencyAssumptions {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ)
    (θ0 : Term → ℝ) (ols : OLSSequence (A := A) (Y := Y) (φ := φ)) : Prop where
  tendsto_theta : Tendsto ols.θhat atTop (nhds θ0)

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

section SurveyWeights

variable {Attr : Type*} [MeasurableSpace Attr]

/-- Assumptions ensuring weighted moments are well-defined and nondegenerate. -/
structure WeightAssumptions (ν : Measure Attr) (w s : Attr → ℝ) : Prop where
  nonneg : ∀ᵐ a ∂ν, 0 ≤ w a
  intW   : Integrable w ν
  intWs  : Integrable (fun a => w a * s a) ν
  intWs2 : Integrable (fun a => w a * (s a) ^ 2) ν
  mass_pos : 0 < ∫ a, w a ∂ν

/--
Moment-matching assumption: weighted mean and second moment equal target human
population moments.
-/
structure WeightMatchesAttrMoments (ν : Measure Attr) (w s : Attr → ℝ) : Prop where
  mean_eq :
    (∫ a, w a * s a ∂ν) / (∫ a, w a ∂ν) = attrMean ν s
  m2_eq :
    (∫ a, w a * (s a) ^ 2 ∂ν) / (∫ a, w a ∂ν) = attrM2 ν s

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

section ModelBridge

section ParametricMainInteractions

variable {Ω Attr : Type*} [MeasurableSpace Ω]

variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]

/--
Assumption: the causal estimand is exactly the paper’s parametric model
(`β0` + main effects + listed interactions).
-/
def ParametricMainInteractions (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (β0 : ℝ) (βMain : Main → ℝ) (βInter : Inter → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) : Prop :=
  ∀ x,
    gStar (μ := μ) (Y := Y) x
      =
    β0 + (∑ m, βMain m * fMain m x) + (∑ i, βInter i * fInter i x)

end ParametricMainInteractions

end ModelBridge

section AdditiveProjectionOracle

variable {Attr Term : Type*} [MeasurableSpace Attr] [Fintype Term]

/--
Additive projection oracle: the oracle score decomposes into a linear-in-terms
component plus a residual orthogonal (in L2) to each term feature.
-/
def AdditiveProjectionOracle
    (ν : Measure Attr)
    (gOracle : Attr → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (r : Attr → ℝ) : Prop :=
  (∀ x, gOracle x = gLin (β := β) (φ := φ) x + r x) ∧
  (∀ t, Integrable (fun x => r x * φ t x) ν) ∧
  (∀ t, ∫ x, r x * φ t x ∂ν = 0)

end AdditiveProjectionOracle

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
