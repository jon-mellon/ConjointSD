/-
ConjointSD/StatusConjointDesign.lean

Encode the concrete single-shot randomization used in the status conjoint:
- profile space: the 8,500 feasible attribute combinations generated for the survey,
- task slots: four persona ratings per respondent,
- design law: uniform over the pre-generated profiles,
- sample space: respondent × task slot × randomized profile, with independence from the
  potential outcomes supplied by the product structure.

The outcomes are rated on a 0–100 scale, so boundedness is discharged with that envelope.
-/

import ConjointSD.ConjointIdentification
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory ProbabilityTheory

noncomputable section
universe u
namespace ConjointSD

/-- Number of distinct feasible personas in the status conjoint (as fielded). -/
def statusProfileCount : ℕ := 8500

/-- Profile space: each element is one of the 8,500 generated personas. -/
abbrev StatusProfile : Type := Fin statusProfileCount

/-- Four rating tasks per respondent (two choice-sets of two personas). -/
def statusTaskCount : ℕ := 4
/-- Task slots per respondent (finite index set). -/
abbrev TaskSlot : Type := Fin statusTaskCount

private lemma statusProfileCount_pos : 0 < statusProfileCount := by decide
private lemma statusTaskCount_pos : 0 < statusTaskCount := by decide

instance : Nonempty StatusProfile := ⟨⟨0, by decide⟩⟩
instance : Nonempty TaskSlot := ⟨⟨0, by decide⟩⟩

/-- Uniform assignment law over the 8,500 status personas. -/
noncomputable def νStatus : Measure StatusProfile :=
  (PMF.uniformOfFintype (α := StatusProfile)).toMeasure

instance : IsProbabilityMeasure νStatus := by
  classical
  simpa [νStatus] using
    (PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype (α := StatusProfile)))

instance : ProbMeasureAssumptions νStatus := ⟨inferInstance⟩

/-- Uniform distribution over the four observed task slots. -/
noncomputable def μTask : Measure TaskSlot :=
  (PMF.uniformOfFintype (α := TaskSlot)).toMeasure

instance : IsProbabilityMeasure μTask :=
  by
    classical
    simpa [μTask] using
      (PMF.toMeasure.isProbabilityMeasure
        (PMF.uniformOfFintype (α := TaskSlot)))

instance : ProbMeasureAssumptions μTask := ⟨inferInstance⟩

/-- Sample space for one persona rating: respondent × task slot × randomized persona. -/
abbrev StatusΩ (Respondent : Type u) : Type u := (Respondent × TaskSlot) × StatusProfile

/-- Base measure on respondent × task slot (respondent measure supplied by caller). -/
noncomputable def μRT {Respondent : Type u} [MeasurableSpace Respondent]
    (μResp : Measure Respondent) : Measure (Respondent × TaskSlot) :=
  μResp.prod μTask

instance {Respondent : Type u} [MeasurableSpace Respondent]
    (μResp : Measure Respondent) [ProbMeasureAssumptions μResp] :
    IsProbabilityMeasure (μRT (μResp := μResp)) := by
  classical
  -- μRT univ = μResp univ * μTask univ = 1.
  have hμ : μResp Set.univ = 1 := measure_univ
  have htask : μTask Set.univ = 1 := measure_univ
  refine ⟨?_⟩
  have hprod := Measure.prod_prod (μ := μResp) (ν := μTask) (Set.univ) (Set.univ)
  calc
    (μRT (μResp := μResp)) Set.univ
        = μResp.prod μTask (Set.univ ×ˢ (Set.univ : Set TaskSlot)) := by
          simp [μRT, Set.univ_prod_univ]
    _ = μResp Set.univ * μTask Set.univ := hprod
    _ = 1 := by simp [hμ, htask]

instance {Respondent : Type u} [MeasurableSpace Respondent]
    (μResp : Measure Respondent) [ProbMeasureAssumptions μResp] :
    ProbMeasureAssumptions (μRT (μResp := μResp)) := ⟨inferInstance⟩

/-- Full sample-space measure for one rating: (respondent × task) × randomized persona. -/
noncomputable def μStatus {Respondent : Type u} [MeasurableSpace Respondent]
    (μResp : Measure Respondent) : Measure (StatusΩ Respondent) :=
  (μRT (μResp := μResp)).prod νStatus

instance {Respondent : Type u} [MeasurableSpace Respondent]
    (μResp : Measure Respondent) [ProbMeasureAssumptions μResp] :
    IsProbabilityMeasure (μStatus (μResp := μResp)) := by
  classical
  have hrt : (μRT (μResp := μResp)) Set.univ = 1 := measure_univ
  have hν : νStatus Set.univ = 1 := measure_univ
  refine ⟨?_⟩
  have hprod :=
    Measure.prod_prod (μ := μRT (μResp := μResp)) (ν := νStatus) (Set.univ) (Set.univ)
  calc
    (μStatus (μResp := μResp)) Set.univ
        = (μRT (μResp := μResp)).prod νStatus
            (Set.univ ×ˢ (Set.univ : Set StatusProfile)) := by
          simp [μStatus, Set.univ_prod_univ]
    _ = (μRT (μResp := μResp)) Set.univ * νStatus Set.univ := hprod
    _ = 1 := by simp [hrt, hν]

instance {Respondent : Type u} [MeasurableSpace Respondent]
    (μResp : Measure Respondent) [ProbMeasureAssumptions μResp] :
    ProbMeasureAssumptions (μStatus (μResp := μResp)) := ⟨inferInstance⟩

/-- Actual randomized assignment: pick the persona coordinate from the product space. -/
def statusX {Respondent : Type u} : StatusΩ Respondent → StatusProfile :=
  Prod.snd

/--
Potential outcomes indexed by persona, depending only on respondent and task slot.
We keep the respondent-level outcome model abstract and lift it to the full space.
-/
def statusY {Respondent : Type u} (Yresp : StatusProfile → Respondent → TaskSlot → ℝ) :
    StatusProfile → StatusΩ Respondent → ℝ :=
  fun p ω => Yresp p ω.fst.fst ω.fst.snd

/-- Observed outcome under the realized persona. -/
def statusYobs {Respondent : Type u} (Yresp : StatusProfile → Respondent → TaskSlot → ℝ) :
    StatusΩ Respondent → ℝ :=
  fun ω => Yresp ω.snd ω.fst.fst ω.fst.snd

/--
The fielded status conjoint satisfies `ConjointIdRandomized`:
uniform profile randomization with bounded 0–100 outcomes, plus measurability,
consistency, and ignorability.
-/
theorem status_id_randomized
    {Respondent : Type u} [MeasurableSpace Respondent]
    (μResp : Measure Respondent) [ProbMeasureAssumptions μResp]
    (Yresp : StatusProfile → Respondent → TaskSlot → ℝ)
    (hmeas :
      ∀ p, Measurable (fun rt : Respondent × TaskSlot => Yresp p rt.fst rt.snd))
    (hmeasObs : Measurable (statusYobs (Yresp := Yresp)))
    (hbound : ∀ p r t, |Yresp p r t| ≤ 100) :
    ConjointIdRandomized (μ := μStatus (μResp := μResp))
      (X := statusX) (Y := statusY (Yresp := Yresp))
      (Yobs := statusYobs (Yresp := Yresp)) := by
  classical
  -- Notation shortcuts.
  let μ := μStatus (μResp := μResp)
  -- Measurability of `X` and the potential-outcome lift.
  have hXmeas : Measurable (statusX : StatusΩ Respondent → StatusProfile) := by
    simpa [StatusΩ, statusX] using
      (measurable_snd : Measurable (fun ω : (Respondent × TaskSlot) × StatusProfile => ω.snd))
  have hYmeas :
      ∀ p, Measurable (statusY (Yresp := Yresp) p) := fun p =>
        (hmeas p).comp (by fun_prop)
  have hYobs : Measurable (statusYobs (Yresp := Yresp)) := hmeasObs
  -- Boundedness: responses live on a 0–100 scale.
  have hbounded :
      ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |statusY (Yresp := Yresp) p ω| ≤ C := by
    intro p
    refine ⟨100, by norm_num, ?_⟩
    intro ω
    exact hbound p ω.fst.fst ω.fst.snd
  -- Ignorability: X depends only on the persona coordinate; Y depends only on respondent/task.
  have hign :
      ∀ p, (statusX (Respondent := Respondent)) ⟂ᵢ[μ] (statusY (Yresp := Yresp) p) := by
    intro p
    -- Express preimages as rectangles and apply the product-measure factorization.
    refine
      (ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul
        (f := statusX (Respondent := Respondent))
        (g := statusY (Yresp := Yresp) p)
        (μ := μ)).2 ?_
    intro s t hs ht
    have hsRT :
        MeasurableSet {rt : Respondent × TaskSlot | Yresp p rt.fst rt.snd ∈ t} := by
      exact (hmeas p) ht
    -- Pull back the measurable sets to rectangles.
    have hpreX :
        (statusX (Respondent := Respondent)) ⁻¹' s
          = (Set.univ : Set (Respondent × TaskSlot)) ×ˢ s := by
      ext ω; simp [statusX]
    have hpreY :
        (statusY (Yresp := Yresp) p) ⁻¹' t
          = {rt : Respondent × TaskSlot | Yresp p rt.fst rt.snd ∈ t}
              ×ˢ (Set.univ : Set StatusProfile) := by
      ext ω; simp [statusY]
    -- Combine the rectangles and evaluate with `prod_prod`.
    calc
      μ ((statusX (Respondent := Respondent)) ⁻¹' s
            ∩ (statusY (Yresp := Yresp) p) ⁻¹' t)
          = μRT (μResp := μResp)
                ({rt : Respondent × TaskSlot | Yresp p rt.fst rt.snd ∈ t})
              * νStatus s := by
                have hrect :
                    (statusX (Respondent := Respondent)) ⁻¹' s
                      ∩ (statusY (Yresp := Yresp) p) ⁻¹' t
                      =
                    ({rt : Respondent × TaskSlot | Yresp p rt.fst rt.snd ∈ t}
                      ×ˢ s) := by
                  ext ω; constructor <;> intro hω
                  · have hx := hω.1; have hy := hω.2
                    constructor
                    · have : ω.fst ∈ {rt | Yresp p rt.fst rt.snd ∈ t} := by
                        simpa [statusY, statusX] using hy
                      simpa [statusX] using this
                    · have : ω.snd ∈ s := by simpa [statusX] using hx
                      simpa [statusX] using this
                  · rcases hω with ⟨hrs, hs'⟩
                    constructor
                    · simpa [statusX] using hs'
                    · have : Yresp p ω.fst.fst ω.fst.snd ∈ t := by
                        simpa using hrs
                      simpa [statusY] using this
                -- Evaluate the rectangle under the product measure.
                have hprod :=
                  (Measure.prod_prod (μ := μRT (μResp := μResp)) (ν := νStatus)
                    ({rt : Respondent × TaskSlot | Yresp p rt.fst rt.snd ∈ t}) s)
                simp [μ, μStatus, μRT, hrect]
      _ = μ ((statusX (Respondent := Respondent)) ⁻¹' s)
              * μ ((statusY (Yresp := Yresp) p) ⁻¹' t) := by
                -- Marginals: X depends only on the persona coordinate;
                -- Y depends on respondent/task.
                have hXmass : μ ((statusX (Respondent := Respondent)) ⁻¹' s) = νStatus s := by
                  have hprod :=
                    (Measure.prod_prod (μ := μRT (μResp := μResp)) (ν := νStatus)
                      (Set.univ : Set (Respondent × TaskSlot)) s)
                  have hμrt : (μRT (μResp := μResp)) Set.univ = 1 := measure_univ
                  simp [μ, μStatus, μRT, hpreX]
                have hYmass :
                    μ ((statusY (Yresp := Yresp) p) ⁻¹' t)
                      = μRT (μResp := μResp)
                          ({rt : Respondent × TaskSlot | Yresp p rt.fst rt.snd ∈ t}) := by
                  have hprod :=
                    (Measure.prod_prod (μ := μRT (μResp := μResp)) (ν := νStatus)
                      ({rt : Respondent × TaskSlot | Yresp p rt.fst rt.snd ∈ t})
                      (Set.univ : Set StatusProfile))
                  have hν : νStatus Set.univ = 1 := measure_univ
                  simp [μ, μStatus, μRT, hpreY, hν]
                simp [hXmass, hYmass, mul_comm]
  refine
    { measX := hXmeas
      measYobs := hYobs
      measY := hYmeas
      consistency := by intro ω; rfl
      bounded := hbounded
      ignorability := hign }

/-- Positivity for the status assignment: every profile has nonzero mass. -/
theorem status_event_pos
    {Respondent : Type u} [MeasurableSpace Respondent]
    (μResp : Measure Respondent) [ProbMeasureAssumptions μResp] :
    ∀ p, (μStatus (μResp := μResp)) (eventX (X := statusX) p) ≠ 0 := by
  classical
  let μ := μStatus (μResp := μResp)
  have hXmeas : Measurable (statusX : StatusΩ Respondent → StatusProfile) := by
    simpa [StatusΩ, statusX] using
      (measurable_snd : Measurable (fun ω : (Respondent × TaskSlot) × StatusProfile => ω.snd))
  have hlaw :
      Measure.map (statusX (Respondent := Respondent)) μ = νStatus := by
    ext s hs
    simp [μ, μStatus, μRT, statusX]
  intro p
  have hset : MeasurableSet ({p} : Set StatusProfile) := measurableSet_singleton p
  have hmap_pre :
      Measure.map (statusX (Respondent := Respondent)) μ {p} = μ (eventX (X := statusX) p) := by
    have hpre :
        (statusX (Respondent := Respondent)) ⁻¹' {p} = eventX (X := statusX) p := by
      ext ω; simp [eventX]
    calc
      Measure.map (statusX (Respondent := Respondent)) μ {p}
          = μ ((statusX (Respondent := Respondent)) ⁻¹' {p}) := by
              simpa using (Measure.map_apply hXmeas hset)
      _ = μ (eventX (X := statusX) p) := by simpa [hpre]
  have hmass :
      νStatus {p} = (PMF.uniformOfFintype (α := StatusProfile)) p := by
    simpa [νStatus, hset] using
      (PMF.toMeasure_apply_singleton
        (p := PMF.uniformOfFintype (α := StatusProfile)) p hset)
  have hsupport :
      (PMF.uniformOfFintype (α := StatusProfile)) p ≠ 0 := by
    have hsupport' := PMF.mem_support_uniformOfFintype (α := StatusProfile) p
    exact (PMF.mem_support_iff
      (p := PMF.uniformOfFintype (α := StatusProfile)) (a := p)).1 hsupport'
  have hpreimage :
      μ (eventX (X := statusX) p) = νStatus {p} := by
    calc
      μ (eventX (X := statusX) p)
          = Measure.map (statusX (Respondent := Respondent)) μ {p} := by
              simpa using hmap_pre.symm
      _ = νStatus {p} := by simpa [hlaw]
  have hpos : νStatus {p} ≠ 0 := by
    simpa [hmass] using hsupport
  intro hzero
  apply hpos
  calc
    νStatus {p} = μ (eventX (X := statusX) p) := by
      symm
      exact hpreimage
    _ = 0 := hzero

end ConjointSD
