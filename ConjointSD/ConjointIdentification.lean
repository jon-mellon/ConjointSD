/-
ConjointSD/ConjointIdentification.lean
-/
import ConjointSD.Assumptions

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)
variable {Attr : Type*}

variable {μ}

/-- `(μ s).toReal ≠ 0` from `μ s ≠ 0` under a finite measure. -/
lemma toReal_ne_zero_of_ne_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Set Ω) (h : μ s ≠ 0) : (μ s).toReal ≠ 0 := by
  refine ENNReal.toReal_ne_zero.2 ?_
  refine ⟨h, ?_⟩
  simp

/-- Derive the `rand` factorization from randomized strong ignorability. -/
lemma rand_from_randomized
    [IsProbabilityMeasure μ] [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (h : ConjointIdRandomized (μ := μ) (X := X) (Y := Y) (Yobs := Yobs))
    (x x0 : Attr) :
    (∫ ω, Y x ω ∂(μ.restrict (eventX (X := X) x0)))
      = (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ) := by
  classical
  -- indicator of {X = x0} as a measurable function of X
  let φ : Attr → ℝ := fun a => if a = x0 then 1 else 0
  let ind : Ω → ℝ := fun ω => φ (X ω)
  let s : Set Ω := X ⁻¹' {x0}
  have hφ_meas : Measurable φ := by
    have hconst : Measurable fun (_ : Attr) => (1 : ℝ) := by fun_prop
    simpa [φ] using hconst.indicator (measurableSet_singleton x0)
  have hset : MeasurableSet s := by
    simpa [s] using h.measX (measurableSet_singleton x0)
  have hInd_meas : AEStronglyMeasurable ind μ :=
    (hφ_meas.comp h.measX).aestronglyMeasurable
  have hY_meas : AEStronglyMeasurable (fun ω => Y x ω) μ :=
    (h.measY x).aestronglyMeasurable
  have hIndY : (ind) ⟂ᵢ[μ] (fun ω => Y x ω) :=
    (h.ignorability x).comp hφ_meas measurable_id
  have hintY : Integrable (fun ω => Y x ω) μ := h.integrableY x
  have hintInd : Integrable ind μ := by
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
    have hident :
        ind = Set.indicator s (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hX : X ω = x0
      · simp [ind, φ, s, hX]
      · simp [ind, φ, s, hX]
    simpa [hident] using hconst.indicator hset
  have hprod := hIndY.integral_fun_mul_eq_mul_integral hInd_meas hY_meas
  have hrestrict :
      (∫ ω, Y x ω ∂(μ.restrict s))
        = ∫ ω, Set.indicator s (fun ω => Y x ω) ω ∂μ := by
    have h' := integral_indicator (μ := μ) (s := s) (f := fun ω => Y x ω) hset
    simpa using h'.symm
  have hintInd' :
      ∫ ω, ind ω ∂μ = (μ s).toReal := by
    have hident :
        ind = Set.indicator s (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hX : X ω = x0
      · simp [ind, φ, s, hX]
      · simp [ind, φ, s, hX]
    calc
      ∫ ω, ind ω ∂μ = ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        simp [hident]
      _ = ∫ ω in s, (1 : ℝ) ∂μ :=
        integral_indicator (μ := μ) (s := s) (f := fun _ => (1 : ℝ)) hset
      _ = (μ s).toReal := by
        simp [integral_const, measureReal_def]
  calc
    (∫ ω, Y x ω ∂(μ.restrict s))
        = ∫ ω, Set.indicator s (fun ω => Y x ω) ω ∂μ := hrestrict
    _ = ∫ ω, ind ω * Y x ω ∂μ := by
          have hident :
              (fun ω => Set.indicator s (fun ω => Y x ω) ω)
                = (fun ω => ind ω * Y x ω) := by
              funext ω
              by_cases hX : X ω = x0
              · simp [ind, φ, s, hX]
              · simp [ind, φ, s, hX]
          simp [hident]
    _ = (∫ ω, ind ω ∂μ) * (∫ ω, Y x ω ∂μ) := by
          simpa using hprod
    _ = (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ) := by
          have hsset : s = eventX (X := X) x0 := by
            ext ω; simp [s, eventX]
          have hs : μ s = μ (eventX (X := X) x0) := by simp [hsset]
          calc
            (∫ ω, ind ω ∂μ) * (∫ ω, Y x ω ∂μ)
                = (μ s).toReal * (∫ ω, Y x ω ∂μ) := by
              simp [hintInd']
            _ = (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ) := by
              simp [hs]

lemma ConjointIdAssumptions.of_randomized
    [IsProbabilityMeasure μ] [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
    {X : Ω → Attr} {Y : Attr → Ω → ℝ} {Yobs : Ω → ℝ}
    (h : ConjointIdRandomized (μ := μ) (X := X) (Y := Y) (Yobs := Yobs)) :
    ConjointIdAssumptions (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) := by
  refine ⟨h.measYobs, h.measY, h.consistency, (by intro x; exact h.positivity x), ?_⟩
  · intro x x0
    exact rand_from_randomized (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) h x x0

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

/--
Instantiate `ConjointIdRandomized` from a single-shot assignment design (`ν` gives the law of `X`
with positive mass on each profile) plus bounded outcomes and ignorability.
-/
lemma ConjointIdRandomized.of_singleShot
    [IsProbabilityMeasure μ] [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
    {ν : Measure Attr} {X : Ω → Attr} {Y : Attr → Ω → ℝ} {Yobs : Ω → ℝ}
    (h : ConjointSingleShotDesign (μ := μ) (ν := ν) (X := X) (Y := Y) (Yobs := Yobs)) :
    ConjointIdRandomized (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) := by
  classical
  refine
    { measX := h.measX
      measYobs := h.measYobs
      measY := h.measY
      consistency := h.consistency
      positivity := ?_
      integrableY := ?_
      bounded := h.bounded
      ignorability := h.ignorability } 
  · intro x
    have hmap := congrArg (fun m => m {x}) h.lawX
    have hset : MeasurableSet ({x} : Set Attr) := measurableSet_singleton x
    have hmap_pre : Measure.map X μ {x} = μ (X ⁻¹' {x}) :=
      Measure.map_apply h.measX hset
    have hpreimage :
        μ (eventX (X := X) x) = ν {x} := by
      calc
        μ (eventX (X := X) x) = μ (X ⁻¹' {x}) := by rfl
        _ = Measure.map X μ {x} := by simpa using hmap_pre.symm
        _ = ν {x} := hmap
    simpa [hpreimage] using h.ν_pos x
  · intro x
    have hbound := h.bounded x
    have hmeas := h.measY x
    -- Probability measure ⇒ finite measure, so bounded measurable implies integrable.
    have hfin : IsFiniteMeasure μ := by infer_instance
    simpa using
      (integrable_of_bounded (μ := μ) (hmeas := hmeas) (hbound := hbound))


section
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
theorem ae_restrict_consistency
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

end

/-- Identification: observed conditional mean among `X=x0` equals `E[Y(x0)]`. -/
theorem identified_potMean_from_condMean [IsProbabilityMeasure μ] [MeasurableSpace Attr]
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
theorem identified_amce_from_condMeans [IsProbabilityMeasure μ] [MeasurableSpace Attr]
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
theorem gExp_eq_gPot [IsProbabilityMeasure μ] [MeasurableSpace Attr]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (h : ConjointIdAssumptions (μ := μ) X Y Yobs) :
    gExp (μ := μ) (X := X) (Yobs := Yobs) = gPot (μ := μ) (Y := Y) := by
  funext x
  simpa [gExp, gPot] using
    identified_potMean_from_condMean (μ := μ) (X := X) (Y := Y) (Yobs := Yobs) h x

end ConjointSD
