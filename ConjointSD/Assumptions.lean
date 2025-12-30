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

/-- Convenient moment conditions on `s` under a population measure `ν`. -/
structure PopulationMomentAssumptions (ν : Measure Attr) (s : Attr → ℝ) : Prop where
  int1 : Integrable s ν
  int2 : Integrable (fun a => (s a) ^ 2) ν

/--
Invariance only on population support (AE under `ν`): `gExp = gPop` holds `ν`-almost everywhere.
This is often the right minimal transport condition.
-/
def InvarianceAE (ν : Measure Attr) (gExp gPop : Attr → ℝ) : Prop :=
  ∀ᵐ x ∂ν, gExp x = gPop x

end Transport

section BasicMeasure

variable {α : Type*} [MeasurableSpace α]

/-- Bundled probability-measure assumption (used to avoid standalone `IsProbabilityMeasure`). -/
class ProbMeasureAssumptions (μ : Measure α) : Prop where
  isProb : IsProbabilityMeasure μ

attribute [instance] ProbMeasureAssumptions.isProb

end BasicMeasure

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
structure IIDAssumptions (Z : ℕ → Ω → ℝ) : Prop where
  intZ  : Integrable (Z 0) μ
  indep : Pairwise (fun i j => IndepFun (Z i) (Z j) μ)
  ident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ
  intZ2 : Integrable (fun ω => (Z 0 ω) ^ 2) μ

end PredictedSD

section SDDecomposition

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

variable {Attr : Type*} [MeasurableSpace Attr]

/-- i.i.d.-type assumptions on the population-record process A. -/
structure PopIID (A : ℕ → Ω → Attr) : Prop where
  measA : ∀ i, Measurable (A i)
  indepA : Pairwise (fun i j => IndepFun (A i) (A j) μ)
  identA : ∀ i, IdentDistrib (A i) (A 0) μ μ

/-- Sufficient conditions to use `sdHatZ_tendsto_ae` on the induced score process. -/
structure ScoreAssumptions (A : ℕ → Ω → Attr) (g : Attr → ℝ) : Prop where
  popiid : PopIID (μ := μ) A
  meas_g : Measurable g
  int_g0 : Integrable (fun ω => g (A 0 ω)) μ
  int_g0_sq : Integrable (fun ω => (g (A 0 ω)) ^ 2) μ

variable {B : Type*}

/-- Bundle assumptions for all blocks at once. -/
structure DecompAssumptions (A : ℕ → Ω → Attr) (g : B → Attr → ℝ) : Prop where
  popiid : PopIID (μ := μ) A
  meas_g : ∀ b, Measurable (g b)
  bound_g : ∀ b, ∃ C, 0 ≤ C ∧ ∀ a, |g b a| ≤ C

end SDDecomposition

section VarianceDecomposition

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

variable {Attr : Type*}
variable {B : Type*} [Fintype B]

/-- Integrability assumptions for block functions and their products. -/
structure BlockIntegrable (A : ℕ → Ω → Attr) (g : B → Attr → ℝ) : Prop where
  intX : ∀ b, Integrable (fun ω => g b (A 0 ω)) μ
  intMul : ∀ b c, Integrable (fun ω => g b (A 0 ω) * g c (A 0 ω)) μ

end VarianceDecomposition

section EstimatedG

variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/--
Assumptions ensuring replacing oracle `g θ0` with estimated `g (θhat n)` does not change
target population moments (under ν) in the limit.

Minimal version: assume convergence of mean and second moment; derive var and sd.
-/
structure GEstimationAssumptions
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ) : Prop where
  mean_tendsto :
      Tendsto
        (fun n => popMeanAttr ν (gHat g θhat n))
        atTop
        (nhds (popMeanAttr ν (g θ0)))

  m2_tendsto :
      Tendsto
        (fun n => popM2Attr ν (gHat g θhat n))
        atTop
        (nhds (popM2Attr ν (g θ0)))

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
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hScore : ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m)

/-- Boundedness-based assumptions for evaluation at a fixed training index `m`. -/
structure SplitEvalAssumptionsBounded
    (μ : Measure Ω) (A : ℕ → Ω → Attr)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ) : Prop where
  hPop : PopIID (μ := μ) A
  hMeas : Measurable (gHat g θhat m)
  hBound : ∃ C, 0 ≤ C ∧ ∀ a, |gHat g θhat m a| ≤ C

end SampleSplitting

section RegressionConsistencyBridge

variable {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]

/--
Continuity assumptions for the induced population functionals at θ0.

These are the “plug point” for regression theory: later you discharge them using
dominated convergence / continuity of link / bounded features / etc.
-/
structure FunctionalContinuityAssumptions
    (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) : Prop where
  cont_mean : ContinuousAt (popMeanΘ (ν := ν) g) θ0
  cont_m2   : ContinuousAt (popM2Θ   (ν := ν) g) θ0

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
Moment assumptions stated against the population Gram/cross moments.
These encode the LLN and identifiability conditions typically used for OLS consistency.
-/
structure OLSMomentAssumptionsOfPop {Attr : Type u} {Term : Type v}
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
        (nhds ((popGram (ν := ν) (φ := φ))⁻¹ i j))
  cross_tendsto :
    ∀ i,
      Tendsto
        (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i)
        atTop
        (nhds (popCross (ν := ν) (g := g) (φ := φ) i))
  theta0_eq :
    θ0 = (popGram (ν := ν) (φ := φ))⁻¹.mulVec (popCross (ν := ν) (g := g) (φ := φ))

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

/-- Moment-matching assumption: weighted mean and second moment equal population moments. -/
structure WeightMatchesPopMoments (ν : Measure Attr) (w s : Attr → ℝ) : Prop where
  mean_eq :
    (∫ a, w a * s a ∂ν) / (∫ a, w a ∂ν) = popMeanAttr ν s
  m2_eq :
    (∫ a, w a * (s a) ^ 2 ∂ν) / (∫ a, w a ∂ν) = popM2Attr ν s

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
Randomization mechanism for the profile assignment.

We model `X` as a measurable function of a randomization variable `U` that is
independent of every potential outcome `Y x`.
-/
structure ConjointRandomizationMechanism
    [MeasurableSpace Attr] (X : Ω → Attr) (Y : Attr → Ω → ℝ) : Prop where
  exists_randomization :
    ∃ (R : Type 0) (_ : MeasurableSpace R) (U : Ω → R) (f : R → Attr),
      Measurable U ∧
      Measurable f ∧
      X = (fun ω => f (U ω)) ∧
      ∀ x, (fun ω => U ω) ⟂ᵢ[μ] (fun ω => Y x ω)

/--
Identification assumptions for the single-profile abstraction.

`rand` is written in a “factorization” form in ℝ (via `.toReal`) so we can avoid
conditional-expectation infrastructure: it directly implies that conditioning on `{X=x0}`
does not change the mean of `Y x`.

Measurability of `Yobs` and each `Y x` is included to make the key AE-restrict step compile.
-/
structure ConjointIdAssumptions
    [MeasurableSpace Attr] (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ) :
    Prop where
  measYobs : Measurable Yobs
  measY : ∀ x, Measurable (Y x)
  consistency : ∀ ω, Yobs ω = Y (X ω) ω
  rand :
    ∀ x x0,
      (∫ ω, Y x ω ∂(μ.restrict (eventX (X := X) x0)))
        = (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ)

/-- Randomized-assignment assumptions that imply the `rand` factorization. -/
structure ConjointIdRandomized
    [MeasurableSpace Attr] (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ) :
    Prop where
  measX : Measurable X
  measYobs : Measurable Yobs
  measY : ∀ x, Measurable (Y x)
  consistency : ∀ ω, Yobs ω = Y (X ω) ω
  integrableY : ∀ x, Integrable (fun ω => Y x ω) μ
  bounded :
    ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Y x ω| ≤ C
  ignorability : ∀ x, (fun ω => X ω) ⟂ᵢ[μ] (fun ω => Y x ω)

/--
Single-shot assignment design:
- `ν` is the assignment law for `X` (every singleton has positive mass),
- `X` is measurable with `Measure.map X μ = ν`,
- outcomes are measurable/consistent and uniformly bounded,
- strong ignorability holds by design (independence of `X` and each potential outcome).

These hypotheses are enough to derive `ConjointIdRandomized`.
-/
structure ConjointSingleShotDesign
    (ν : Measure Attr)
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ) : Prop where
  rand : ConjointRandomizationMechanism (μ := μ) (X := X) (Y := Y)
  lawX : Measure.map X μ = ν
  ν_pos : ∀ x, ν {x} ≠ 0
  measYobs : Measurable Yobs
  measY : ∀ x, Measurable (Y x)
  consistency : ∀ ω, Yobs ω = Y (X ω) ω
  bounded :
    ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Y x ω| ≤ C

end ConjointIdentification

section ModelBridge

variable {Ω Attr Term : Type*} [MeasurableSpace Ω] [Fintype Term]

/-- Well-specification: the causal estimand lies in the linear-in-terms model class. -/
def WellSpecified
    (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) : Prop :=
  ∀ x, gLin (β := β) (φ := φ) x = gStar (μ := μ) (Y := Y) x

/-- Approximate well-specification: the estimand is within ε of the linear-in-terms model. -/
def ApproxWellSpecified
    (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ x, |gLin (β := β) (φ := φ) x - gStar (μ := μ) (Y := Y) x| ≤ ε

/-- Approximate well-specification on population support (ν-a.e.). -/
def ApproxWellSpecifiedAE
    {Attr : Type*} [MeasurableSpace Attr]
    (ν : Measure Attr) (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ) : Prop :=
  ∀ᵐ x ∂ν, |gLin (β := β) (φ := φ) x - gStar (μ := μ) (Y := Y) x| ≤ ε


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

/-- “No interactions”: there exist `μ0` and main effects `main` giving exact additivity. -/
def NoInteractions
    (μ : Measure Ω) (Y : Profile K V → Ω → ℝ) : Prop :=
  ∃ (μ0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V, gStar (μ := μ) (Y := Y) x = μ0 + ∑ k : K, main k (x k)

end WellSpecifiedFromNoInteractions

section PaperOLSConsistency

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable [DecidableEq (PaperTerm Main Inter)]

variable (μ : Measure Ω) [ProbMeasureAssumptions μ]
variable (ν : Measure Attr) [ProbMeasureAssumptions ν]

variable (Y : Attr → Ω → ℝ)
variable (A : ℕ → Attr) (Yobs : ℕ → ℝ)

variable (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)

/-- Entrywise LLN for Gram and cross moments (deterministic sequence). -/
structure PaperOLSLLNA
    (A : ℕ → Attr) (Yobs : ℕ → ℝ) : Prop where
  gram_tendsto :
    ∀ i j,
      Tendsto
        (fun n =>
          gramMatrix
            (A := A)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i j)
        atTop
        (nhds
          (popGram
            (ν := ν)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j))
  cross_tendsto :
    ∀ i,
      Tendsto
        (fun n =>
          crossVec
            (A := A) (Y := Yobs)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i)
        atTop
        (nhds
          (popCross
            (ν := ν)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))

/-- Stability assumption: inverse Gram entries converge to the inverse population Gram. -/
structure PaperOLSInverseStability
    (A : ℕ → Attr) : Prop where
  gramInv_tendsto :
    ∀ i j,
      Tendsto
        (fun n =>
          (gramMatrix
            (A := A)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)⁻¹ i j)
        atTop
        (nhds
          ((popGram
            (ν := ν)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j))

/-- Identifiability: the population normal equations determine `θ0`. -/
def PaperOLSIdentifiability (θ0 : PaperTerm Main Inter → ℝ) : Prop :=
  θ0 =
    (popGram
      (ν := ν)
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
      (popCross
        (ν := ν)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))

/--
Moment assumptions for the paper OLS estimator at the sample-path level.

This is the LLN/identifiability package: for almost every ω, the empirical Gram
and cross moments converge to their population targets for `gStar`.
-/
def PaperOLSMomentAssumptions
    (μ : Measure Ω) (ν : Measure Attr)
    (Y : Attr → Ω → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)
    (θ0 : PaperTerm Main Inter → ℝ)
    (Aω : ℕ → Ω → Attr) (Yobsω : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ,
    OLSMomentAssumptionsOfPop
      (ν := ν)
      (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
      (g := gStar (μ := μ) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      θ0

end PaperOLSConsistency

end ConjointSD
