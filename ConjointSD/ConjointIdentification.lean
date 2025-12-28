/-
ConjointSD/ConjointIdentification.lean
-/


import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)
variable {Attr : Type*}

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

/--
Identification assumptions for the single-profile abstraction.

`rand` is written in a “factorization” form in ℝ (via `.toReal`) so we can avoid
conditional-expectation infrastructure: it directly implies that conditioning on `{X=x0}`
does not change the mean of `Y x`.

Measurability of `Yobs` and each `Y x` is included to make the key AE-restrict step compile.
-/
structure ConjointIdAssumptions
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ) : Prop where
  measYobs : Measurable Yobs
  measY : ∀ x, Measurable (Y x)
  consistency : ∀ ω, Yobs ω = Y (X ω) ω
  positivity : ∀ x, μ (eventX (X := X) x) ≠ 0
  rand :
    ∀ x x0,
      (∫ ω, Y x ω ∂(μ.restrict (eventX (X := X) x0)))
        = (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ)

variable {μ}

/-- `(μ s).toReal ≠ 0` from `μ s ≠ 0` under a finite measure. -/
lemma toReal_ne_zero_of_ne_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Set Ω) (h : μ s ≠ 0) : (μ s).toReal ≠ 0 := by
  refine ENNReal.toReal_ne_zero.2 ?_
  refine ⟨h, ?_⟩
  simp

/-- If the factorization holds, the event-conditional mean equals the unconditional mean. -/
theorem condMean_eq_potMean_of_rand
    [IsProbabilityMeasure μ]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ)
    (x x0 : Attr)
    (hpos : μ (eventX (X := X) x0) ≠ 0)
    (hrand :
      (∫ ω, Y x ω ∂(μ.restrict (eventX (X := X) x0)))
        = (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ)) :
    condMean (μ := μ) (Y x) (eventX (X := X) x0) = potMean (μ := μ) Y x := by
  letI : IsFiniteMeasure μ := by infer_instance
  have hposR : (μ (eventX (X := X) x0)).toReal ≠ 0 :=
    toReal_ne_zero_of_ne_zero (μ := μ) (eventX (X := X) x0) hpos
  unfold condMean potMean
  -- numerator is `(μ s).toReal * (∫ Y)`; divide by `(μ s).toReal` to get `∫ Y`.
  have hμ : (μ (eventX (X := X) x0)).toReal ≠ 0 := hposR
  calc
    (∫ ω, Y x ω ∂(μ.restrict (eventX (X := X) x0)))
        / (μ (eventX (X := X) x0)).toReal
        = ((μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ))
            / (μ (eventX (X := X) x0)).toReal := by
            simp [hrand]
    _ = (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ)
            * (μ (eventX (X := X) x0)).toReal⁻¹ := by
            ring
    _ = ∫ ω, Y x ω ∂μ := by field_simp [hμ]

/--
Consistency implies: on the event `{X=x0}`, `Yobs = Y x0` holds a.e. under `μ.restrict`.

Important: in mathlib v4.26, `ae_restrict_iff` expects measurability of the *predicate-set*
`{ω | p ω}`, not measurability of the event `s`. So we prove measurability of
`{ω | Yobs ω = Y x0 ω}` from measurability of `Yobs` and `Y x0`.
-/
theorem ae_restrict_consistency [IsProbabilityMeasure μ]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (x0 : Attr)
    (hmeasYobs : Measurable Yobs)
    (hmeasYx0 : Measurable (Y x0))
    (hcons : ∀ ω, Yobs ω = Y (X ω) ω) :
    (∀ᵐ ω ∂(μ.restrict (eventX (X := X) x0)), Yobs ω = Y x0 ω) := by
  -- Measurable predicate-set needed by `ae_restrict_iff`.
  have hpred : MeasurableSet {ω : Ω | Yobs ω = Y x0 ω} := by
    have hsub : Measurable (fun ω : Ω => Yobs ω - Y x0 ω) :=
      hmeasYobs.sub hmeasYx0
    have hset :
        {ω : Ω | Yobs ω = Y x0 ω}
          = (fun ω : Ω => Yobs ω - Y x0 ω) ⁻¹' ({0} : Set ℝ) := by
      ext ω
      simp [sub_eq_zero]
    have hpre :
        MeasurableSet ((fun ω : Ω => Yobs ω - Y x0 ω) ⁻¹' ({0} : Set ℝ)) :=
      hsub (measurableSet_singleton (0 : ℝ))
    simpa [hset] using hpre
  -- Now use `ae_restrict_iff` in the direction: (ae on μ with implication) -> (ae on μ.restrict).
  refine (ae_restrict_iff (μ := μ) (s := eventX (X := X) x0)
            (p := fun ω => Yobs ω = Y x0 ω) hpred).2 ?_
  refine ae_of_all _ ?_
  intro ω hω
  -- hω : ω ∈ {ω | X ω = x0}  i.e. X ω = x0
  have hx : X ω = x0 := hω
  simp [hcons ω, hx]

/-- Identification: observed conditional mean among `X=x0` equals `E[Y(x0)]`. -/
theorem identified_potMean_from_condMean [IsProbabilityMeasure μ]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (h : ConjointIdAssumptions (μ := μ) X Y Yobs)
    (x0 : Attr) :
    condMean (μ := μ) Yobs (eventX (X := X) x0) = potMean (μ := μ) Y x0 := by
  have hae :
    (∀ᵐ ω ∂(μ.restrict (eventX (X := X) x0)), Yobs ω = Y x0 ω) :=
    ae_restrict_consistency (μ := μ) (X := X) (Y := Y) (Yobs := Yobs)
      x0 (h.measYobs) (h.measY x0) (h.consistency)
  have hint :
      (∫ ω, Yobs ω ∂(μ.restrict (eventX (X := X) x0)))
        =
      (∫ ω, Y x0 ω ∂(μ.restrict (eventX (X := X) x0))) := by
    exact integral_congr_ae hae
  have hpos : μ (eventX (X := X) x0) ≠ 0 := h.positivity x0
  have hrand :
      (∫ ω, Y x0 ω ∂(μ.restrict (eventX (X := X) x0)))
        =
      (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x0 ω ∂μ) :=
    h.rand x0 x0
  calc
    condMean (μ := μ) Yobs (eventX (X := X) x0)
        = (∫ ω, Y x0 ω ∂(μ.restrict (eventX (X := X) x0)))
            / (μ (eventX (X := X) x0)).toReal := by
              simp [condMean, hint]
    _   = potMean (μ := μ) Y x0 := by
          exact condMean_eq_potMean_of_rand (μ := μ) (X := X) (Y := Y) x0 x0 hpos hrand

/-- Identification of AMCE as a difference of observed conditional means. -/
theorem identified_amce_from_condMeans [IsProbabilityMeasure μ]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (h : ConjointIdAssumptions (μ := μ) X Y Yobs)
    (x x' : Attr) :
    (condMean (μ := μ) Yobs (eventX (X := X) x')
      - condMean (μ := μ) Yobs (eventX (X := X) x))
      =
    amce (μ := μ) Y x x' := by
  unfold amce
  have hx' :
      condMean (μ := μ) Yobs (eventX (X := X) x') = potMean (μ := μ) Y x' :=
    identified_potMean_from_condMean (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) h x'
  have hx :
      condMean (μ := μ) Yobs (eventX (X := X) x) = potMean (μ := μ) Y x :=
    identified_potMean_from_condMean (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) h x
  simp [hx', hx]

/-!
## Identified score function (design-mean) equals causal score function (potential mean)
-/

/-- Design-identified score: observed conditional mean among units with `X = x`. -/
def gExp (μ : Measure Ω) (X : Ω → Attr) (Yobs : Ω → ℝ) : Attr → ℝ :=
  fun x => condMean (μ := μ) Yobs (eventX (X := X) x)

/-- Causal score: potential-outcome mean under profile `x`. -/
def gPot (μ : Measure Ω) (Y : Attr → Ω → ℝ) : Attr → ℝ :=
  fun x => potMean (μ := μ) Y x

/--
Under the conjoint identification assumptions, the observed conditional-mean score function
equals the causal potential-mean score function (pointwise, hence as functions).
-/
theorem gExp_eq_gPot [IsProbabilityMeasure μ]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (h : ConjointIdAssumptions (μ := μ) X Y Yobs) :
    gExp (μ := μ) (X := X) (Yobs := Yobs) = gPot (μ := μ) (Y := Y) := by
  funext x
  simpa [gExp, gPot] using
    identified_potMean_from_condMean (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) h x

end ConjointSD
