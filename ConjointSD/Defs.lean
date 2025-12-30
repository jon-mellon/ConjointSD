import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

/-!
# Shared definitions

This file centralizes core definitions that are depended on by the project's
assumption packages. Assumption structures/props live in `ConjointSD.Assumptions`.
-/

section ModelBridge

universe u v

/-- An additive linear-in-terms score function. -/
def gLin {Attr Term : Type*} [Fintype Term]
    (β : Term → ℝ) (φ : Term → Attr → ℝ) : Attr → ℝ :=
  fun a => ∑ t, β t * φ t a

/-- Profiles are a product of all relevant attributes: `Attr := ∀ k, V k`. -/
abbrev Profile (K : Type u) (V : K → Type v) : Type (max u v) :=
  ∀ k : K, V k

section ParametricMainInteractions

variable {Attr : Type*}
variable {Main Inter : Type*}

/-- Term set used in the paper: intercept, one term for each main effect, and one per
interaction. -/
abbrev PaperTerm (Main Inter : Type*) := Option (Sum Main Inter)

/-- Coefficient map matching the paper’s term set. -/
def βPaper (β0 : ℝ) (βMain : Main → ℝ) (βInter : Inter → ℝ) :
    PaperTerm Main Inter → ℝ
  | none => β0
  | some (Sum.inl m) => βMain m
  | some (Sum.inr i) => βInter i

/-- Feature map matching the paper’s term set. -/
def φPaper (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) :
    PaperTerm Main Inter → Attr → ℝ
  | none => fun _ => 1
  | some (Sum.inl m) => fMain m
  | some (Sum.inr i) => fInter i

end ParametricMainInteractions

end ModelBridge

section ConjointOrder

universe u v

variable {J : Type u} {Attr : Type v}

/-- Ordered profile list for a task with `J` profile slots. -/
abbrev OrderedProfiles (J : Type u) (Attr : Type v) : Type (max u v) := J → Attr

/-- Permute an ordered profile list by a permutation of slots. -/
def permuteProfiles (π : Equiv.Perm J) (t : OrderedProfiles J Attr) :
    OrderedProfiles J Attr :=
  fun j => t (π j)

end ConjointOrder

section PredictedSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

/-- Empirical mean: (1/n) • ∑_{i<n} Z i ω. -/
def meanHatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) • (Finset.sum (Finset.range n) fun i => Z i ω)

/-- Empirical second moment: (1/n) • ∑_{i<n} (Z i ω)^2. -/
def m2HatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) • (Finset.sum (Finset.range n) fun i => (Z i ω) ^ 2)

/-- Plug-in empirical variance proxy: m2Hat - (meanHat)^2. -/
def varHatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  m2HatZ (Z := Z) n ω - (meanHatZ (Z := Z) n ω) ^ 2

/-- Plug-in empirical SD proxy: √(varHat). -/
def sdHatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (varHatZ (Z := Z) n ω)

/-- Empirical RMSE proxy: √(m2Hat). -/
def rmseHatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (m2HatZ (Z := Z) n ω)

/-- Population mean: ∫ Z 0 dμ. -/
def popMeanZ (Z : ℕ → Ω → ℝ) : ℝ :=
  ∫ ω, Z 0 ω ∂μ

/-- Population second moment: ∫ (Z 0)^2 dμ. -/
def popM2Z (Z : ℕ → Ω → ℝ) : ℝ :=
  ∫ ω, (Z 0 ω) ^ 2 ∂μ

/-- Population variance proxy: E[Z^2] - (E[Z])^2. -/
def popVarZ (Z : ℕ → Ω → ℝ) : ℝ :=
  popM2Z (μ := μ) Z - (popMeanZ (μ := μ) Z) ^ 2

/-- Population SD proxy: √(popVar). -/
def popSDZ (Z : ℕ → Ω → ℝ) : ℝ :=
  Real.sqrt (popVarZ (μ := μ) Z)

/-- Population RMSE proxy: √(popM2). -/
def popRMSEZ (Z : ℕ → Ω → ℝ) : ℝ :=
  Real.sqrt (popM2Z (μ := μ) Z)

end PredictedSD

section Transport

variable {Attr : Type*} [MeasurableSpace Attr]

/-- Population mean of a score function `s : Attr → ℝ` under `ν`. -/
def popMeanAttr (ν : Measure Attr) (s : Attr → ℝ) : ℝ :=
  ∫ a, s a ∂ν

/-- Population second moment of a score function `s` under `ν`. -/
def popM2Attr (ν : Measure Attr) (s : Attr → ℝ) : ℝ :=
  ∫ a, (s a) ^ 2 ∂ν

/-- Population variance via `E[s^2] - (E[s])^2` under `ν`. -/
def popVarAttr (ν : Measure Attr) (s : Attr → ℝ) : ℝ :=
  popM2Attr (ν := ν) s - (popMeanAttr (ν := ν) s) ^ 2

/-- Population SD under `ν` (square root of `popVarAttr`). -/
def popSDAttr (ν : Measure Attr) (s : Attr → ℝ) : ℝ :=
  Real.sqrt (popVarAttr (ν := ν) s)

end Transport

section EstimatedG

variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/-- Plug-in (estimated) status function on attributes. -/
def gHat (g : Θ → Attr → ℝ) (θhat : ℕ → Θ) (n : ℕ) : Attr → ℝ :=
  fun a => g (θhat n) a

end EstimatedG

section SDDecomposition

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]

/-- Induced real-valued process from population records via a scoring function g. -/
def Zcomp (A : ℕ → Ω → Attr) (g : Attr → ℝ) : ℕ → Ω → ℝ :=
  fun i ω => g (A i ω)

end SDDecomposition

section RegressionConsistencyBridge

variable {Attr Θ : Type*} [MeasurableSpace Attr]

/-- Θ ↦ population mean induced by a parametric score `g : Θ → Attr → ℝ` under ν. -/
def popMeanΘ (ν : Measure Attr) (g : Θ → Attr → ℝ) : Θ → ℝ :=
  fun θ => popMeanAttr ν (g θ)

/-- Θ ↦ population second moment induced by `g` under ν. -/
def popM2Θ (ν : Measure Attr) (g : Θ → Attr → ℝ) : Θ → ℝ :=
  fun θ => popM2Attr ν (g θ)

/-- Block score at parameter θ for a fixed block index `b`. -/
def blockScoreΘ {B : Type*}
    (gB : B → Θ → Attr → ℝ) (b : B) : Θ → Attr → ℝ :=
  fun θ => gB b θ

end RegressionConsistencyBridge

section RegressionEstimator

universe u v

/--
Empirical squared-loss risk for a linear-in-terms model using the first `n` samples.
The `A` and `Y` sequences are the training attributes/outcomes.
-/
def empiricalRisk {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ)
    (n : ℕ) (β : Term → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (Y i - gLin (β := β) (φ := φ) (A i)) ^ 2

/--
An OLS estimator sequence for the linear-in-terms model: each `θhat n` minimizes
the empirical risk based on the first `n` samples.
-/
structure OLSSequence {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ) : Type (max u v) where
  /-- The coefficient estimate at sample size `n`. -/
  θhat : ℕ → Term → ℝ
  is_minimizer :
    ∀ n β, empiricalRisk (A := A) (Y := Y) (φ := φ) n (θhat n)
      ≤ empiricalRisk (A := A) (Y := Y) (φ := φ) n β

/--
Empirical Gram matrix of the feature map for the first `n` samples.
-/
def gramMatrix {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (φ : Term → Attr → ℝ) (n : ℕ) : Matrix Term Term ℝ :=
  by
    classical
    let _ := (inferInstance : Fintype Term)
    exact fun i j => (1 / (n : ℝ)) * ∑ k : Fin n, φ i (A k) * φ j (A k)

/--
Empirical cross-moment between features and outcomes for the first `n` samples.
-/
def crossVec {Attr : Type u} {Term : Type v} [Fintype Term]
    (A : ℕ → Attr) (Y : ℕ → ℝ) (φ : Term → Attr → ℝ) (n : ℕ) : Term → ℝ :=
  by
    classical
    let _ := (inferInstance : Fintype Term)
    exact fun i => (1 / (n : ℝ)) * ∑ k : Fin n, φ i (A k) * Y k

/--
Population Gram matrix of the feature map under a target attribute distribution `ν`.
-/
def popGram {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (ν : Measure Attr) (φ : Term → Attr → ℝ) : Matrix Term Term ℝ :=
  by
    classical
    let _ := (inferInstance : Fintype Term)
    exact fun i j => popMeanAttr ν (fun a => φ i a * φ j a)

/--
Population cross moment between features and a true outcome score `g` under `ν`.
-/
def popCross {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (ν : Measure Attr) (g : Attr → ℝ) (φ : Term → Attr → ℝ) : Term → ℝ :=
  by
    classical
    let _ := (inferInstance : Fintype Term)
    exact fun i => popMeanAttr ν (fun a => φ i a * g a)

end RegressionEstimator

section ConjointIdentification

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]

/-- Event that the shown profile equals `x`. -/
def eventX (X : Ω → Attr) (x : Attr) : Set Ω := {ω | X ω = x}

/-- Conditional mean on an event `s`: (∫ Z d(μ.restrict s)) / (μ s).toReal. -/
def condMean (μ : Measure Ω) (Z : Ω → ℝ) (s : Set Ω) : ℝ :=
  (∫ ω, Z ω ∂(μ.restrict s)) / (μ s).toReal

/-- Mean of a potential outcome under profile `x`. -/
def potMean (μ : Measure Ω) (Y : Attr → Ω → ℝ) (x : Attr) : ℝ :=
  ∫ ω, Y x ω ∂μ

/-- AMCE between profiles `x` and `x'`. -/
def amce (μ : Measure Ω) (Y : Attr → Ω → ℝ) (x x' : Attr) : ℝ :=
  potMean (μ := μ) Y x' - potMean (μ := μ) Y x

end ConjointIdentification

section ConjointEstimand

variable {Ω Attr : Type*} [MeasurableSpace Ω]

/-- Conjoint causal estimand as a function of profiles: `g⋆ x = E[Y(x)]`. -/
def gStar (μ : Measure Ω) (Y : Attr → Ω → ℝ) : Attr → ℝ :=
  fun x => potMean (μ := μ) Y x

end ConjointEstimand

end ConjointSD
