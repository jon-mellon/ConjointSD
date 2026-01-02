/-
ConjointSD/ConjointIdentification.lean
-/
import ConjointSD.Assumptions

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω)
variable {Attr : Type*}

variable {μexp}

/-- `(μexp s).toReal ≠ 0` from `μexp s ≠ 0` under a finite measure. -/
lemma toReal_ne_zero_of_ne_zero (μexp : Measure Ω) [IsFiniteMeasure μexp]
    (s : Set Ω) (h : μexp s ≠ 0) : (μexp s).toReal ≠ 0 := by
  refine ENNReal.toReal_ne_zero.2 ?_
  refine ⟨h, ?_⟩
  simp

/-- Derive the `rand` factorization from randomized strong ignorability. -/
lemma rand_from_randomized
    [ProbMeasureAssumptions μexp] [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (h : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (x x0 : Attr) :
    (∫ ω, Y x ω ∂(μexp.restrict (eventX (X := X) x0)))
      = (μexp (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μexp) := by
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
  have hInd_meas : AEStronglyMeasurable ind μexp :=
    (hφ_meas.comp h.measX).aestronglyMeasurable
  have hY_meas : AEStronglyMeasurable (fun ω => Y x ω) μexp :=
    (h.measY x).aestronglyMeasurable
  have hIndY : (ind) ⟂ᵢ[μexp] (fun ω => Y x ω) :=
    (h.ignorability x).comp hφ_meas measurable_id
  have hintY : Integrable (fun ω => Y x ω) μexp := by
    have _ : IsFiniteMeasure μexp := by infer_instance
    obtain ⟨C, hC0, hC⟩ := h.bounded x
    refine Integrable.of_bound (hf := (h.measY x).aestronglyMeasurable) C ?_
    refine ae_of_all μexp ?_
    intro ω
    have hCω := hC ω
    simpa [Real.norm_eq_abs] using hCω
  have hintInd : Integrable ind μexp := by
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μexp := integrable_const _
    have hident :
        ind = Set.indicator s (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hX : X ω = x0
      · simp [ind, φ, s, hX]
      · simp [ind, φ, s, hX]
    simpa [hident] using hconst.indicator hset
  have hprod := hIndY.integral_fun_mul_eq_mul_integral hInd_meas hY_meas
  have hrestrict :
      (∫ ω, Y x ω ∂(μexp.restrict s))
        = ∫ ω, Set.indicator s (fun ω => Y x ω) ω ∂μexp := by
    have h' := integral_indicator (μ := μexp) (s := s) (f := fun ω => Y x ω) hset
    simpa using h'.symm
  have hintInd' :
      ∫ ω, ind ω ∂μexp = (μexp s).toReal := by
    have hident :
        ind = Set.indicator s (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hX : X ω = x0
      · simp [ind, φ, s, hX]
      · simp [ind, φ, s, hX]
    calc
      ∫ ω, ind ω ∂μexp = ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μexp := by
        simp [hident]
      _ = ∫ ω in s, (1 : ℝ) ∂μexp :=
        integral_indicator (μ := μexp) (s := s) (f := fun _ => (1 : ℝ)) hset
      _ = (μexp s).toReal := by
        simp [integral_const, measureReal_def]
  calc
    (∫ ω, Y x ω ∂(μexp.restrict s))
        = ∫ ω, Set.indicator s (fun ω => Y x ω) ω ∂μexp := hrestrict
    _ = ∫ ω, ind ω * Y x ω ∂μexp := by
          have hident :
              (fun ω => Set.indicator s (fun ω => Y x ω) ω)
                = (fun ω => ind ω * Y x ω) := by
              funext ω
              by_cases hX : X ω = x0
              · simp [ind, φ, s, hX]
              · simp [ind, φ, s, hX]
          simp [hident]
    _ = (∫ ω, ind ω ∂μexp) * (∫ ω, Y x ω ∂μexp) := by
          simpa using hprod
    _ = (μexp (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μexp) := by
          have hsset : s = eventX (X := X) x0 := by
            ext ω; simp [s, eventX]
          have hs : μexp s = μexp (eventX (X := X) x0) := by simp [hsset]
          calc
            (∫ ω, ind ω ∂μexp) * (∫ ω, Y x ω ∂μexp)
                = (μexp s).toReal * (∫ ω, Y x ω ∂μexp) := by
              simp [hintInd']
            _ = (μexp (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μexp) := by
              simp [hs]

section
/-- If the factorization holds, the event-conditional mean equals the unconditional mean. -/
theorem condMean_eq_potMean_of_rand
    [ProbMeasureAssumptions μexp]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ)
    (x x0 : Attr)
    (hpos : μexp (eventX (X := X) x0) ≠ 0)
    (hrand :
      (∫ ω, Y x ω ∂(μexp.restrict (eventX (X := X) x0)))
        = (μexp (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μexp)) :
    condMean (κ := μexp) (Y x) (eventX (X := X) x0) = potMean (κ := μexp) Y x := by
  letI : IsFiniteMeasure μexp := by infer_instance
  have hposR : (μexp (eventX (X := X) x0)).toReal ≠ 0 :=
    toReal_ne_zero_of_ne_zero (μexp := μexp) (eventX (X := X) x0) hpos
  unfold condMean potMean
  -- numerator is `(μexp s).toReal * (∫ Y)`; divide by `(μexp s).toReal` to get `∫ Y`.
  have hμ : (μexp (eventX (X := X) x0)).toReal ≠ 0 := hposR
  calc
    (∫ ω, Y x ω ∂(μexp.restrict (eventX (X := X) x0)))
        / (μexp (eventX (X := X) x0)).toReal
        = ((μexp (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μexp))
            / (μexp (eventX (X := X) x0)).toReal := by
            simp [hrand]
    _ = (μexp (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μexp)
            * (μexp (eventX (X := X) x0)).toReal⁻¹ := by
            ring
    _ = ∫ ω, Y x ω ∂μexp := by field_simp [hμ]

/--
Consistency implies: on the event `{X=x0}`, `Yobs = Y x0` holds a.e. under `μexp.restrict`.

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
    (∀ᵐ ω ∂(μexp.restrict (eventX (X := X) x0)), Yobs ω = Y x0 ω) := by
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
  -- Now use `ae_restrict_iff` in the direction: (ae on μexp with implication) -> (ae on μexp.restrict).
  refine (ae_restrict_iff (μ := μexp) (s := eventX (X := X) x0)
            (p := fun ω => Yobs ω = Y x0 ω) hpred).2 ?_
  refine ae_of_all _ ?_
  intro ω hω
  -- hω : ω ∈ {ω | X ω = x0}  i.e. X ω = x0
  have hx : X ω = x0 := hω
  simp [hcons ω, hx]

end

/-- Identification: observed conditional mean among `X=x0` equals `E[Y(x0)]`. -/
theorem identified_potMean_from_condMean
    [ProbMeasureAssumptions μexp] [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (h : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (x0 : Attr)
    (hpos : μexp (eventX (X := X) x0) ≠ 0) :
    condMean (κ := μexp) Yobs (eventX (X := X) x0) = potMean (κ := μexp) Y x0 := by
  have hae :
    (∀ᵐ ω ∂(μexp.restrict (eventX (X := X) x0)), Yobs ω = Y x0 ω) :=
    ae_restrict_consistency (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs)
      x0 (h.measYobs) (h.measY x0) (h.consistency)
  have hint :
      (∫ ω, Yobs ω ∂(μexp.restrict (eventX (X := X) x0)))
        =
      (∫ ω, Y x0 ω ∂(μexp.restrict (eventX (X := X) x0))) := by
    exact integral_congr_ae hae
  have hrand :
      (∫ ω, Y x0 ω ∂(μexp.restrict (eventX (X := X) x0)))
        =
      (μexp (eventX (X := X) x0)).toReal * (∫ ω, Y x0 ω ∂μexp) :=
    rand_from_randomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) h x0 x0
  calc
    condMean (κ := μexp) Yobs (eventX (X := X) x0)
        = (∫ ω, Y x0 ω ∂(μexp.restrict (eventX (X := X) x0)))
            / (μexp (eventX (X := X) x0)).toReal := by
              simp [condMean, hint]
    _   = potMean (κ := μexp) Y x0 := by
          exact condMean_eq_potMean_of_rand (μexp := μexp) (X := X) (Y := Y) x0 x0 hpos hrand

/-- Identification of AMCE as a difference of observed conditional means. -/
theorem identified_amce_from_condMeans
    [ProbMeasureAssumptions μexp] [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
    (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)
    (h : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (hpos : ∀ x, μexp (eventX (X := X) x) ≠ 0)
    (x x' : Attr) :
    (condMean (κ := μexp) Yobs (eventX (X := X) x')
      - condMean (κ := μexp) Yobs (eventX (X := X) x))
      =
    amce (κ := μexp) Y x x' := by
  unfold amce
  have hx' :
      condMean (κ := μexp) Yobs (eventX (X := X) x') = potMean (κ := μexp) Y x' :=
    identified_potMean_from_condMean (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) h
      x' (hpos x')
  have hx :
      condMean (κ := μexp) Yobs (eventX (X := X) x) = potMean (κ := μexp) Y x :=
    identified_potMean_from_condMean (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) h
      x (hpos x)
  simp [hx', hx]

/-!
## Identified score function (design-mean) equals causal score function (potential mean)
-/

/-- Design-identified score: observed conditional mean among units with `X = x`. -/
def gExp (μexp : Measure Ω) (X : Ω → Attr) (Yobs : Ω → ℝ) : Attr → ℝ :=
  fun x => condMean (κ := μexp) Yobs (eventX (X := X) x)

/-- Causal score: potential-outcome mean under profile `x`. -/
def gPot (μexp : Measure Ω) (Y : Attr → Ω → ℝ) : Attr → ℝ :=
  fun x => potMean (κ := μexp) Y x

section ProfileOrder

variable {Task J Attr : Type*}

/-!
Bridge for Assumption 2: order-invariant task outcomes induce order-invariant
potential means for the ordered profile lists.
-/

def taskOutcome (k : Task) (Y : Task → OrderedProfiles J Attr → Ω → ℝ) :
    OrderedProfiles J Attr → Ω → ℝ :=
  fun t ω => Y k t ω

lemma potMean_invariant_of_noProfileOrder
    (Y : Task → OrderedProfiles J Attr → Ω → ℝ)
    (k : Task) (t : OrderedProfiles J Attr) (π : Equiv.Perm J)
    (h : NoProfileOrderEffects (Y := Y)) :
    potMean (κ := μexp) (Y := taskOutcome (Task := Task) (J := J) (Attr := Attr) k Y)
        (permuteProfiles π t)
      =
    potMean (κ := μexp) (Y := taskOutcome (Task := Task) (J := J) (Attr := Attr) k Y) t := by
  simp [potMean, taskOutcome, h.permute k t π]

end ProfileOrder

end ConjointSD
