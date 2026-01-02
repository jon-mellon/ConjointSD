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

section PaperTermSet

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

end PaperTermSet

end ModelBridge

section ConjointOrder

universe u v

variable {J : Type u} {Attr : Type v}

/-- Ordered profile list for a task with `J` profile slots. -/
abbrev OrderedProfiles (J : Type u) (Attr : Type v) : Type (max u v) := J → Attr

end ConjointOrder

section PredictedSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (κ : Measure Ω)

/-- Design pushforward attribute distribution: the law of `A 0` under `κ`. -/
def kappaDesign {Attr : Type*} [MeasurableSpace Attr] (A : ℕ → Ω → Attr) : Measure Attr :=
  Measure.map (A 0) κ

/-- Empirical mean: (1/n) • ∑_{i<n} Z i ω. -/
def meanHatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) • (Finset.sum (Finset.range n) fun i => Z i ω)

/-- Empirical second moment: (1/n) • ∑_{i<n} (Z i ω)^2. -/
def m2HatZ (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) • (Finset.sum (Finset.range n) fun i => (Z i ω) ^ 2)

/-- Weights evaluated along a draw stream `A`. -/
def Wcomp {Attr : Type*} (A : ℕ → Ω → Attr) (w : Attr → ℝ) : ℕ → Ω → ℝ :=
  fun i ω => w (A i ω)

/-- Weighted empirical mean: (∑ w_i Z_i) / (∑ w_i). -/
def meanHatZW (Z W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (meanHatZ (Z := fun i ω => W i ω * Z i ω) n ω)
    / (meanHatZ (Z := W) n ω)

/-- Weighted empirical second moment: (∑ w_i Z_i^2) / (∑ w_i). -/
def m2HatZW (Z W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (meanHatZ (Z := fun i ω => W i ω * (Z i ω) ^ 2) n ω)
    / (meanHatZ (Z := W) n ω)

/-- Plug-in weighted variance proxy. -/
def varHatZW (Z W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  m2HatZW (Z := Z) (W := W) n ω - (meanHatZW (Z := Z) (W := W) n ω) ^ 2

/-- Plug-in weighted SD proxy. -/
def sdHatZW (Z W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (varHatZW (Z := Z) (W := W) n ω)

/-- Experimental design distribution mean: ∫ Z 0 dκ. -/
def designMeanZ (Z : ℕ → Ω → ℝ) : ℝ :=
  ∫ ω, Z 0 ω ∂κ

/-- Experimental design distribution second moment: ∫ (Z 0)^2 dκ. -/
def designM2Z (Z : ℕ → Ω → ℝ) : ℝ :=
  ∫ ω, (Z 0 ω) ^ 2 ∂κ

/-- Experimental design distribution variance proxy: E[Z^2] - (E[Z])^2. -/
def designVarZ (Z : ℕ → Ω → ℝ) : ℝ :=
  designM2Z (κ := κ) Z - (designMeanZ (κ := κ) Z) ^ 2

/-- Experimental design distribution SD proxy: √(designVar). -/
def designSDZ (Z : ℕ → Ω → ℝ) : ℝ :=
  Real.sqrt (designVarZ (κ := κ) Z)

/-- Weighted design mean: (∫ W0 Z0)/(∫ W0). -/
def designMeanZW (Z W : ℕ → Ω → ℝ) : ℝ :=
  (designMeanZ (κ := κ) (Z := fun i ω => W i ω * Z i ω))
    / (designMeanZ (κ := κ) (Z := W))

/-- Weighted design second moment: (∫ W0 Z0^2)/(∫ W0). -/
def designM2ZW (Z W : ℕ → Ω → ℝ) : ℝ :=
  (designMeanZ (κ := κ) (Z := fun i ω => W i ω * (Z i ω) ^ 2))
    / (designMeanZ (κ := κ) (Z := W))

/-- Weighted design variance proxy. -/
def designVarZW (Z W : ℕ → Ω → ℝ) : ℝ :=
  designM2ZW (κ := κ) (Z := Z) (W := W)
    - (designMeanZW (κ := κ) (Z := Z) (W := W)) ^ 2

/-- Weighted design SD proxy. -/
def designSDZW (Z W : ℕ → Ω → ℝ) : ℝ :=
  Real.sqrt (designVarZW (κ := κ) (Z := Z) (W := W))

end PredictedSD

section Transport

variable {Attr : Type*} [MeasurableSpace Attr]

/-- Attribute-distribution mean under `xiAttr` (generic attribute law). -/
def attrMean (xiAttr : Measure Attr) (s : Attr → ℝ) : ℝ :=
  ∫ a, s a ∂xiAttr

/-- Attribute-distribution second moment under `xiAttr`. -/
def attrM2 (xiAttr : Measure Attr) (s : Attr → ℝ) : ℝ :=
  ∫ a, (s a) ^ 2 ∂xiAttr

/-- Attribute-distribution variance via `E[s^2] - (E[s])^2` under `xiAttr`. -/
def attrVar (xiAttr : Measure Attr) (s : Attr → ℝ) : ℝ :=
  attrM2 (xiAttr := xiAttr) s - (attrMean (xiAttr := xiAttr) s) ^ 2

/-- Attribute-distribution SD under `xiAttr` (square root of `attrVar`). -/
def attrSD (xiAttr : Measure Attr) (s : Attr → ℝ) : ℝ :=
  Real.sqrt (attrVar (xiAttr := xiAttr) s)

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

/-- Induced real-valued process from attribute records via a scoring function `g`. -/
def Zcomp (A : ℕ → Ω → Attr) (g : Attr → ℝ) : ℕ → Ω → ℝ :=
  fun i ω => g (A i ω)

end SDDecomposition

section RegressionConsistencyBridge

variable {Attr Θ : Type*} [MeasurableSpace Attr]

/-- Θ ↦ attribute-distribution mean induced by `g` under `xiAttr`. -/
def attrMeanΘ (xiAttr : Measure Attr) (g : Θ → Attr → ℝ) : Θ → ℝ :=
  fun θ => attrMean xiAttr (g θ)

/-- Θ ↦ attribute-distribution second moment induced by `g` under `xiAttr`. -/
def attrM2Θ (xiAttr : Measure Attr) (g : Θ → Attr → ℝ) : Θ → ℝ :=
  fun θ => attrM2 xiAttr (g θ)

/-- Block score at parameter θ for a fixed block index `b`. -/
def blockScoreΘ {B : Type*}
    (gB : B → Θ → Attr → ℝ) (b : B) : Θ → Attr → ℝ :=
  fun θ => gB b θ

end RegressionConsistencyBridge

section RegressionEstimator

universe u v

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

/-- Attribute-distribution Gram matrix of the feature map under `xiAttr`. -/
def attrGram {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (xiAttr : Measure Attr) (φ : Term → Attr → ℝ) : Matrix Term Term ℝ :=
  by
    classical
    let _ := (inferInstance : Fintype Term)
    exact fun i j => attrMean xiAttr (fun a => φ i a * φ j a)

/-- Attribute-distribution cross moment between features and `g` under `xiAttr`. -/
def attrCross {Attr : Type u} {Term : Type v} [MeasurableSpace Attr] [Fintype Term]
    (xiAttr : Measure Attr) (g : Attr → ℝ) (φ : Term → Attr → ℝ) : Term → ℝ :=
  by
    classical
    let _ := (inferInstance : Fintype Term)
    exact fun i => attrMean xiAttr (fun a => φ i a * g a)

end RegressionEstimator

section ConjointIdentification

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]

/-- Event that the shown profile equals `x`. -/
def eventX (X : Ω → Attr) (x : Attr) : Set Ω := {ω | X ω = x}

/-- Conditional mean on an event `s`: (∫ Z d(κ.restrict s)) / (κ s).toReal. -/
def condMean (κ : Measure Ω) (Z : Ω → ℝ) (s : Set Ω) : ℝ :=
  (∫ ω, Z ω ∂(κ.restrict s)) / (κ s).toReal

/-- Mean of a potential outcome under profile `x`. -/
def potMean (κ : Measure Ω) (Y : Attr → Ω → ℝ) (x : Attr) : ℝ :=
  ∫ ω, Y x ω ∂κ

/-- AMCE between profiles `x` and `x'`. -/
def amce (κ : Measure Ω) (Y : Attr → Ω → ℝ) (x x' : Attr) : ℝ :=
  potMean (κ := κ) Y x' - potMean (κ := κ) Y x

end ConjointIdentification

section ConjointEstimand

variable {Ω Attr : Type*} [MeasurableSpace Ω]

/-- Conjoint causal estimand as a function of profiles: `g⋆ x = E[Y(x)]`. -/
def gStar (μexp : Measure Ω) (Y : Attr → Ω → ℝ) : Attr → ℝ :=
  fun x => potMean (κ := μexp) Y x

end ConjointEstimand

end ConjointSD
