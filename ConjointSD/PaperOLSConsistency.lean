/-
ConjointSD/PaperOLSConsistency.lean

Paper-specific OLS consistency wrappers targeting the causal estimand `gStar`
with the paper's term set (intercept + main effects + interactions).
-/

import ConjointSD.ModelBridge
import ConjointSD.DecompositionSequentialConsistency
import ConjointSD.RegressionEstimator
import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.DesignAttributeBridge
import ConjointSD.Assumptions

open Filter MeasureTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section PaperTermScore

variable {Attr : Type*}
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]

variable (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)

/-- Paper regression score with coefficients `θ` on the paper term set. -/
def gPaper (θ : PaperTerm Main Inter → ℝ) : Attr → ℝ :=
  gLin (β := θ) (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))

theorem gPaper_eq_gTotalΘ_blocks
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B) :
    gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      =
    (fun θ a =>
      ∑ b : B,
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a) := by
  classical
  funext θ a
  have hblocks :
      gLin (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        =
      gTotal (B := B)
        (g := gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) :=
    gLin_eq_gTotal_blocks (B := B) (Term := PaperTerm Main Inter)
      (blk := blk) (β := θ)
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
  have hblocks' := congrArg (fun f => f a) hblocks
  have hTotal :
      (∑ b : B,
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
        =
      gTotal (B := B)
        (g := gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) a := by
    simp [gTotal]
  calc
    gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ a
        =
      gLin (β := θ)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) a := by
          simp [gPaper]
    _ = gTotal (B := B)
        (g := gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) a := hblocks'
    _ = ∑ b : B,
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a := by
        symm
        exact hTotal

end PaperTermScore

section PaperOLS

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable [DecidableEq (PaperTerm Main Inter)]

variable (μ : Measure Ω) [ProbMeasureAssumptions μ]
variable (ν : Measure Attr) [ProbMeasureAssumptions ν]

variable (Y : Attr → Ω → ℝ)
variable (A : ℕ → Attr) (Yobs : ℕ → ℝ)

variable (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)

omit [DecidableEq (PaperTerm Main Inter)] in
lemma measurable_phiPaper
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i)) :
    ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t) := by
  intro t
  cases t with
  | none =>
      simpa [φPaper] using (measurable_const : Measurable (fun _ : Attr => (1 : ℝ)))
  | some s =>
      cases s with
      | inl m =>
          simpa [φPaper] using hmeasMain m
      | inr i =>
          simpa [φPaper] using hmeasInter i

omit [DecidableEq (PaperTerm Main Inter)] in
lemma bounded_phiPaper
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    ∀ t, ∃ C, 0 ≤ C ∧ ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C := by
  intro t
  cases t with
  | none =>
      refine ⟨1, by norm_num, ?_⟩
      intro a
      simp [φPaper]
  | some s =>
      cases s with
      | inl m =>
          simpa [φPaper] using hboundMain m
      | inr i =>
          simpa [φPaper] using hboundInter i

omit [DecidableEq (PaperTerm Main Inter)] in
theorem functionalContinuity_gPaper_of_bounded
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    FunctionalContinuityAssumptions (ν := ν)
      (g := fun θ =>
        gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ) θ0 := by
  have hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t) :=
    measurable_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hmeasMain hmeasInter
  have hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C :=
    bounded_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hboundMain hboundInter
  simpa [gPaper] using
    (functionalContinuity_gLin_of_bounded
      (ν := ν) (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      hmeasφ hboundφ θ0)

omit [DecidableEq (PaperTerm Main Inter)] in
theorem functionalContinuity_gTotalΘ_of_bounded
    {B : Type*} [Fintype B] [DecidableEq B]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    FunctionalContinuityAssumptions (ν := ν)
      (g := gTotalΘ
        (gB := fun b θ a =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
      θ0 := by
  have hContPaper :
      FunctionalContinuityAssumptions (ν := ν)
        (g := fun θ =>
          gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ) θ0 :=
    functionalContinuity_gPaper_of_bounded
      (Attr := Attr) (Main := Main) (Inter := Inter)
      (fMain := fMain) (fInter := fInter)
      (ν := ν) (θ0 := θ0)
      hmeasMain hmeasInter hboundMain hboundInter
  refine
    functionalContinuity_of_eq
      (ν := ν)
      (g := fun θ =>
        gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ)
      (g' := gTotalΘ
        (gB := fun b θ a =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
      (θ0 := θ0)
      ?_
      hContPaper
  intro θ a
  have hEq :=
    gPaper_eq_gTotalΘ_blocks
      (Attr := Attr) (fMain := fMain) (fInter := fInter) (B := B) (blk := blk)
  have hEq' := congrArg (fun f => f θ a) hEq
  simpa [gTotalΘ] using hEq'

omit [DecidableEq (PaperTerm Main Inter)] in
def φBlock
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B) (b : B) :
    PaperTerm Main Inter → Attr → ℝ :=
  fun t a => if blk t = b
    then φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a
    else 0

omit [DecidableEq (PaperTerm Main Inter)] in
lemma gBlockTerm_eq_gLin_φBlock
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B) (b : B) (θ : PaperTerm Main Inter → ℝ) :
    gBlockTerm
        (blk := blk) (β := θ)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b
      =
    gLin (β := θ) (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b) := by
  classical
  funext a
  simp [gBlockTerm, gLin, φBlock]

omit [DecidableEq (PaperTerm Main Inter)] in
theorem functionalContinuity_gBlockTerm_of_bounded
    {B : Type*} [Fintype B] [DecidableEq B]
    (ν : Measure Attr) [ProbMeasureAssumptions ν]
    (blk : PaperTerm Main Inter → B) (b : B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    FunctionalContinuityAssumptions (ν := ν)
      (g := gBlock (gB := fun b θ a =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a) b)
      θ0 := by
  have hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t) :=
    measurable_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hmeasMain hmeasInter
  have hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C :=
    bounded_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hboundMain hboundInter
  have hmeasφBlock :
      ∀ t, Measurable (φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t) := by
    intro t
    by_cases htb : blk t = b
    · simp [φBlock, htb, hmeasφ t]
    · simp [φBlock, htb, measurable_const]
  have hboundφBlock :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t a| ≤ C := by
    intro t
    by_cases htb : blk t = b
    · simpa [φBlock, htb] using hboundφ t
    · refine ⟨0, by nlinarith, ?_⟩
      intro a
      simp [φBlock, htb]
  have hContLin :
      FunctionalContinuityAssumptions (ν := ν)
        (g := fun θ =>
          gLin (β := θ)
            (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b)) θ0 :=
    functionalContinuity_gLin_of_bounded
      (ν := ν)
      (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b)
      hmeasφBlock hboundφBlock θ0
  have hEq :
      ∀ θ a,
        gBlock
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a) b θ a
          =
        gLin (β := θ)
          (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b) a := by
    intro θ a
    have hEq' :=
      gBlockTerm_eq_gLin_φBlock
        (Attr := Attr) (Main := Main) (Inter := Inter)
        (fMain := fMain) (fInter := fInter)
        (B := B) (blk := blk) (b := b) (θ := θ)
    simpa [gBlock] using congrArg (fun f => f a) hEq'
  exact
    functionalContinuity_of_eq
      (ν := ν)
      (g := fun θ =>
        gLin (β := θ)
          (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b))
      (g' := gBlock
        (gB := fun b θ a =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a) b)
      (θ0 := θ0) hEq hContLin

omit [DecidableEq (PaperTerm Main Inter)] in
lemma bounded_mul
    {f g : Attr → ℝ}
    (hf : ∃ C, 0 ≤ C ∧ ∀ a, |f a| ≤ C)
    (hg : ∃ C, 0 ≤ C ∧ ∀ a, |g a| ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ a, |f a * g a| ≤ C := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf
  obtain ⟨Cg, hCg0, hCg⟩ := hg
  refine ⟨Cf * Cg, mul_nonneg hCf0 hCg0, ?_⟩
  intro a
  have hf' := hCf a
  have hg' := hCg a
  have hmul : |f a| * |g a| ≤ Cf * Cg :=
    mul_le_mul hf' hg' (abs_nonneg _) hCf0
  simpa [abs_mul] using hmul

omit [DecidableEq (PaperTerm Main Inter)] in
lemma scoreAssumptions_gram_of_design
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (Aω : ℕ → Ω → Attr)
    (hPop : DesignAttrIID (μ := μ) Aω)
    (hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t))
    (hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C)
    (i j : PaperTerm Main Inter) :
    ScoreAssumptions
      (μ := μ) (A := Aω)
      (g := fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)) := by
  have hmeas :
      Measurable (fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)) :=
    (hmeasφ i).mul (hmeasφ j)
  have hbound :
      ∃ C, 0 ≤ C ∧
        ∀ a,
          |(φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)| ≤ C :=
    bounded_mul (hf := hboundφ i) (hg := hboundφ j)
  exact
    scoreAssumptions_of_bounded
      (μ := μ) (A := Aω)
      (g := fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a))
      hPop hmeas hbound

omit [DecidableEq (PaperTerm Main Inter)] in
lemma scoreAssumptions_cross_of_design
    (μ : Measure Ω) [ProbMeasureAssumptions μ]
    (Aω : ℕ → Ω → Attr)
    (Y : Attr → Ω → ℝ)
    (hPop : DesignAttrIID (μ := μ) Aω)
    (hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t))
    (hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C)
    (hmeasStar : Measurable (gStar (μ := μ) (Y := Y)))
    (hboundStar : ∃ C, 0 ≤ C ∧ ∀ a, |gStar (μ := μ) (Y := Y) a| ≤ C)
    (i : PaperTerm Main Inter) :
    ScoreAssumptions
      (μ := μ) (A := Aω)
      (g := fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μ := μ) (Y := Y) a) := by
  have hmeas :
      Measurable (fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μ := μ) (Y := Y) a) :=
    (hmeasφ i).mul hmeasStar
  have hbound :
      ∃ C, 0 ≤ C ∧
        ∀ a,
          |(φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * gStar (μ := μ) (Y := Y) a| ≤ C :=
    bounded_mul (hf := hboundφ i) (hg := hboundStar)
  exact
    scoreAssumptions_of_bounded
      (μ := μ) (A := Aω)
      (g := fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μ := μ) (Y := Y) a)
      hPop hmeas hbound

omit [DecidableEq (PaperTerm Main Inter)] [ProbMeasureAssumptions ν] in
theorem paper_ols_lln_of_score_assumptions_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hYobs : ∀ n ω, Yobsω n ω = gStar (μ := μ) (Y := Y) (Aω n ω))
    (hScoreGram :
      ∀ i j,
        ScoreAssumptions
          (μ := μ) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)))
    (hScoreCross :
      ∀ i,
        ScoreAssumptions
          (μ := μ) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * gStar (μ := μ) (Y := Y) a)) :
    ∀ᵐ ω ∂μ,
      (∀ i j,
        Tendsto
          (fun n =>
            gramMatrix
              (A := fun k => Aω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n i j)
          atTop
          (nhds
            (attrGram
              (ν := Measure.map (Aω 0) μ)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)))
      ∧
      (∀ i,
        Tendsto
          (fun n =>
            crossVec
              (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n i)
          atTop
          (nhds
      (attrCross
        (ν := Measure.map (Aω 0) μ)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))) := by
  classical
  have hgram : ∀ i j, ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          gramMatrix
            (A := fun k => Aω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i j)
        atTop
        (nhds
          (attrGram
            (ν := Measure.map (Aω 0) μ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)) := by
    intro i j
    let gGram : Attr → ℝ :=
      fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)
    have hmean :
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n : ℕ =>
              meanHatZ (Z := Zcomp (A := Aω) (g := gGram)) n ω)
            atTop
            (nhds (designMeanZ (μ := μ) (Z := Zcomp (A := Aω) (g := gGram)))) :=
      meanHatZ_tendsto_ae_of_score
        (μ := μ) (A := Aω) (g := gGram) (hScoreGram i j)
    have hpop :
        designMeanZ (μ := μ) (Z := Zcomp (A := Aω) (g := gGram))
          =
        attrMean (Measure.map (Aω 0) μ) gGram :=
      designMeanZ_Zcomp_eq_attrMean
        (μ := μ) (A := Aω) (g := gGram)
        (hA0 := (hScoreGram i j).designAttrIID.measA 0)
        (hg := (hScoreGram i j).meas_g)
    refine hmean.mono ?_
    intro ω hω
    have hω' :
        Tendsto
          (fun n =>
            meanHatZ (Z := Zcomp (A := Aω) (g := gGram)) n ω)
          atTop
          (nhds (attrMean (Measure.map (Aω 0) μ) gGram)) := by
      simpa [hpop] using hω
    have hgram_eq :
        ∀ n,
          gramMatrix
              (A := fun k => Aω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n i j
            =
          ((n : ℝ)⁻¹) * ∑ k ∈ Finset.range n,
            gGram (Aω k ω) := by
      intro n
      have hsum :
          (∑ k : Fin n, gGram (Aω k ω))
            =
          ∑ k ∈ Finset.range n, gGram (Aω k ω) := by
        simpa using (Fin.sum_univ_eq_sum_range (n := n) (fun k => gGram (Aω k ω)))
      simp [gramMatrix, gGram, hsum]
    simpa [meanHatZ, Zcomp, gGram, attrGram, hgram_eq]
      using hω'
  have hcross : ∀ i, ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          crossVec
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i)
        atTop
        (nhds
          (attrCross
            (ν := Measure.map (Aω 0) μ)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i)) := by
    intro i
    let gCross : Attr → ℝ :=
      fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μ := μ) (Y := Y) a
    have hmean :
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n : ℕ =>
              meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω)
            atTop
            (nhds (designMeanZ (μ := μ) (Z := Zcomp (A := Aω) (g := gCross)))) :=
      meanHatZ_tendsto_ae_of_score
        (μ := μ) (A := Aω) (g := gCross) (hScoreCross i)
    have hpop :
        designMeanZ (μ := μ) (Z := Zcomp (A := Aω) (g := gCross))
          =
        attrMean (Measure.map (Aω 0) μ) gCross :=
      designMeanZ_Zcomp_eq_attrMean
        (μ := μ) (A := Aω) (g := gCross)
        (hA0 := (hScoreCross i).designAttrIID.measA 0)
        (hg := (hScoreCross i).meas_g)
    refine hmean.mono ?_
    intro ω hω
    have hω' :
        Tendsto
          (fun n =>
            meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω)
          atTop
          (nhds (attrMean (Measure.map (Aω 0) μ) gCross)) := by
      simpa [hpop] using hω
    have hcross_eq :
        (fun n =>
          crossVec
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i)
          =
        (fun n =>
          meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω) := by
      funext n
      have hsum :
          (∑ k : Fin n, gCross (Aω k ω))
            =
          ∑ k ∈ Finset.range n, gCross (Aω k ω) := by
        simpa using (Fin.sum_univ_eq_sum_range (n := n) (fun k => gCross (Aω k ω)))
      simp [crossVec, meanHatZ, Zcomp, gCross, smul_eq_mul, hYobs, hsum]
    simpa [attrCross, gCross, hcross_eq] using hω'
  have hgram_all : ∀ᵐ ω ∂μ, ∀ i j, Tendsto
      (fun n =>
        gramMatrix
          (A := fun k => Aω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n i j)
      atTop
      (nhds
        (attrGram
          (ν := Measure.map (Aω 0) μ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)) := by
    refine (ae_all_iff.2 ?_)
    intro i
    refine (ae_all_iff.2 ?_)
    intro j
    exact hgram i j
  have hcross_all : ∀ᵐ ω ∂μ, ∀ i, Tendsto
      (fun n =>
        crossVec
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n i)
      atTop
      (nhds
        (attrCross
          (ν := Measure.map (Aω 0) μ)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i)) := by
    refine (ae_all_iff.2 ?_)
    intro i
    exact hcross i
  refine (hgram_all.and hcross_all).mono ?_
  intro ω hω
  rcases hω with ⟨hgramω, hcrossω⟩
  exact ⟨hgramω, hcrossω⟩

omit [DecidableEq (PaperTerm Main Inter)] [ProbMeasureAssumptions ν] in
theorem paper_ols_lln_of_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hDesign :
      PaperOLSDesignAssumptions
        (μ := μ) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (ν := ν) (fMain := fMain) (fInter := fInter)) :
    ∀ᵐ ω ∂μ,
      (∀ i j,
        Tendsto
          (fun n =>
            gramMatrix
              (A := fun k => Aω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n i j)
          atTop
          (nhds
            (attrGram
              (ν := ν)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)))
      ∧
      (∀ i,
        Tendsto
          (fun n =>
            crossVec
              (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n i)
          atTop
          (nhds
            (attrCross
              (ν := ν)
              (g := gStar (μ := μ) (Y := Y))
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))) := by
  have hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t) :=
    measurable_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hDesign.meas_fMain hDesign.meas_fInter
  have hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C :=
    bounded_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hDesign.bound_fMain hDesign.bound_fInter
  have hScoreGram :
      ∀ i j,
        ScoreAssumptions
          (μ := μ) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)) :=
    fun i j =>
      scoreAssumptions_gram_of_design
        (μ := μ) (Aω := Aω) (fMain := fMain) (fInter := fInter)
        hDesign.designAttrIID hmeasφ hboundφ i j
  have hScoreCross :
      ∀ i,
        ScoreAssumptions
          (μ := μ) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * gStar (μ := μ) (Y := Y) a) :=
    fun i =>
      scoreAssumptions_cross_of_design
        (μ := μ) (Aω := Aω) (Y := Y) (fMain := fMain) (fInter := fInter)
        hDesign.designAttrIID hmeasφ hboundφ hDesign.meas_gStar hDesign.bound_gStar i
  have hLLN :=
    paper_ols_lln_of_score_assumptions_ae
      (μ := μ) (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω)
      (hYobs := hDesign.yobs_eq)
      (hScoreGram := hScoreGram) (hScoreCross := hScoreCross)
  refine hLLN.mono ?_
  intro ω hω
  rcases hω with ⟨hgram, hcross⟩
  refine ⟨?_, ?_⟩
  · intro i j
    simpa [hDesign.gram_eq i j] using hgram i j
  · intro i
    simpa [hDesign.cross_eq i] using hcross i

variable {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}

omit [ProbMeasureAssumptions μ] [ProbMeasureAssumptions ν] in
theorem paper_ols_attr_moments_of_lln_fullrank_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hLLN :
      ∀ᵐ ω ∂μ,
        (∀ i j,
          Tendsto
            (fun n =>
              gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n i j)
            atTop
            (nhds
              (attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)))
        ∧
        (∀ i,
          Tendsto
            (fun n =>
              crossVec
                (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n i)
            atTop
            (nhds
              (attrCross
                (ν := ν)
                (g := gStar (μ := μ) (Y := Y))
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))))
    (hInv :
      ∀ᵐ ω ∂μ,
        ∀ i j,
          Tendsto
            (fun n =>
              (gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n)⁻¹ i j)
            atTop
            (nhds
              ((attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
    (hId :
      θ0 =
        (attrGram
          (ν := ν)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (ν := ν)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))) :
    ∀ᵐ ω ∂μ,
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0 := by
  refine (hLLN.and hInv).mono ?_
  intro ω hω
  rcases hω with ⟨hLLNω, hInvω⟩
  refine
    { gramInv_tendsto := hInvω
      cross_tendsto := hLLNω.2
      theta0_eq := hId }

theorem paper_ols_attr_moments_of_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (θ0 : PaperTerm Main Inter → ℝ)
    (hDesign :
      PaperOLSDesignAssumptions
        (μ := μ) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (ν := ν) (fMain := fMain) (fInter := fInter))
    (hInv :
      ∀ᵐ ω ∂μ,
        ∀ i j,
          Tendsto
            (fun n =>
              (gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n)⁻¹ i j)
            atTop
            (nhds
              ((attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
    (hId :
      θ0 =
        (attrGram
          (ν := ν)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (ν := ν)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))) :
    ∀ᵐ ω ∂μ,
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0 := by
  have hLLN :
      ∀ᵐ ω ∂μ,
        (∀ i j,
          Tendsto
            (fun n =>
              gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n i j)
            atTop
            (nhds
              (attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)))
        ∧
        (∀ i,
          Tendsto
            (fun n =>
              crossVec
                (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n i)
            atTop
            (nhds
              (attrCross
                (ν := ν)
                (g := gStar (μ := μ) (Y := Y))
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))) :=
    paper_ols_lln_of_design_ae
      (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω) hDesign
  exact
    paper_ols_attr_moments_of_lln_fullrank_ae
      (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω)
      hLLN hInv hId

omit [ProbMeasureAssumptions μ] [ProbMeasureAssumptions ν] in
theorem theta_tendsto_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          olsThetaHat
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)
        atTop
        (nhds θ0) := by
  refine hMom.mono ?_
  intro ω hω
  simpa using
    (olsThetaHat_tendsto_of_attr_moments
      (ν := ν)
      (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
      (g := gStar (μ := μ) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      hω)

theorem theta_tendsto_of_paper_ols_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (θ0 : PaperTerm Main Inter → ℝ)
    (hDesign :
      PaperOLSDesignAssumptions
        (μ := μ) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (ν := ν) (fMain := fMain) (fInter := fInter))
    (hInv :
      ∀ᵐ ω ∂μ,
        ∀ i j,
          Tendsto
            (fun n =>
              (gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n)⁻¹ i j)
            atTop
            (nhds
              ((attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
    (hId :
      θ0 =
        (attrGram
          (ν := ν)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (ν := ν)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          olsThetaHat
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)
        atTop
        (nhds θ0) := by
  have hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0 :=
    paper_ols_attr_moments_of_design_ae
      (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω)
      hDesign hInv hId
  exact
    theta_tendsto_of_paper_ols_moments_ae
      (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom

omit [ProbMeasureAssumptions μ] in
theorem attrMean_tendsto_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          attrMean ν
            (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds (attrMean ν (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  refine (theta_tendsto_of_paper_ols_moments_ae
    (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
    (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom).mono ?_
  intro ω hθ
  simpa using
    (attrMean_tendsto_of_theta_tendsto
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hθ hCont)

omit [ProbMeasureAssumptions μ] in
theorem attrM2_tendsto_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          attrM2 ν
            (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds (attrM2 ν (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  refine (theta_tendsto_of_paper_ols_moments_ae
    (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
    (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom).mono ?_
  intro ω hθ
  simpa using
    (attrM2_tendsto_of_theta_tendsto
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hθ hCont)

theorem attrMean_tendsto_of_paper_ols_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (θ0 : PaperTerm Main Inter → ℝ)
    (hDesign :
      PaperOLSDesignAssumptions
        (μ := μ) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (ν := ν) (fMain := fMain) (fInter := fInter))
    (hInv :
      ∀ᵐ ω ∂μ,
        ∀ i j,
          Tendsto
            (fun n =>
              (gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n)⁻¹ i j)
            atTop
            (nhds
              ((attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
    (hId :
      θ0 =
        (attrGram
          (ν := ν)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (ν := ν)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          attrMean ν
            (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds (attrMean ν (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  have hθ :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n =>
            olsThetaHat
              (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n)
          atTop
          (nhds θ0) :=
    theta_tendsto_of_paper_ols_design_ae
      (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω)
      hDesign hInv hId
  refine hθ.mono ?_
  intro ω hω
  simpa using
    (attrMean_tendsto_of_theta_tendsto
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hω hCont)

theorem attrM2_tendsto_of_paper_ols_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (θ0 : PaperTerm Main Inter → ℝ)
    (hDesign :
      PaperOLSDesignAssumptions
        (μ := μ) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (ν := ν) (fMain := fMain) (fInter := fInter))
    (hInv :
      ∀ᵐ ω ∂μ,
        ∀ i j,
          Tendsto
            (fun n =>
              (gramMatrix
                (A := fun k => Aω k ω)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n)⁻¹ i j)
            atTop
            (nhds
              ((attrGram
                (ν := ν)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
    (hId :
      θ0 =
        (attrGram
          (ν := ν)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (ν := ν)
            (g := gStar (μ := μ) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          attrM2 ν
            (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds (attrM2 ν (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  have hθ :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n =>
            olsThetaHat
              (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n)
          atTop
          (nhds θ0) :=
    theta_tendsto_of_paper_ols_design_ae
      (μ := μ) (ν := ν) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω)
      hDesign hInv hId
  refine hθ.mono ?_
  intro ω hω
  simpa using
    (attrM2_tendsto_of_theta_tendsto
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hω hCont)

omit [ProbMeasureAssumptions μ] [ProbMeasureAssumptions ν] in
theorem theta_tendsto_of_paper_ols_moments
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := A) (Y := Yobs)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      atTop
      (nhds θ0) :=
  olsThetaHat_tendsto_of_attr_moments
    (ν := ν) (A := A) (Y := Yobs)
    (g := gStar (μ := μ) (Y := Y))
    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
    (θ0 := θ0)
    hMom

omit [ProbMeasureAssumptions μ] in
theorem attrMean_tendsto_of_paper_ols_gStar
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := A) (Y := Yobs)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        attrMean ν
          (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            (fun n =>
              olsThetaHat
                (A := A) (Y := Yobs)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n) n))
      atTop
      (nhds (attrMean ν (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  have hθ :
      Tendsto
        (fun n =>
          olsThetaHat
            (A := A) (Y := Yobs)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)
        atTop
        (nhds θ0) :=
    theta_tendsto_of_paper_ols_moments
      (μ := μ) (ν := ν)
      (Y := Y) (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom
  simpa using
    (attrMean_tendsto_of_theta_tendsto
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hθ hCont)

omit [ProbMeasureAssumptions μ] in
theorem attrM2_tendsto_of_paper_ols_gStar
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := A) (Y := Yobs)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        attrM2 ν
          (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            (fun n =>
              olsThetaHat
                (A := A) (Y := Yobs)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n) n))
      atTop
      (nhds (attrM2 ν (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  have hθ :
      Tendsto
        (fun n =>
          olsThetaHat
            (A := A) (Y := Yobs)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)
        atTop
        (nhds θ0) :=
    theta_tendsto_of_paper_ols_moments
      (μ := μ) (ν := ν)
      (Y := Y) (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom
  simpa using
    (attrM2_tendsto_of_theta_tendsto
      (ν := ν)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hθ hCont)

omit [ProbMeasureAssumptions μ] in
theorem attrMean_tendsto_of_paper_ols_gStar_total
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := A) (Y := Yobs)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        attrMean ν
          (gHat (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
            (fun n =>
              olsThetaHat
                (A := A) (Y := Yobs)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n) n))
      atTop
      (nhds
        (attrMean ν
          (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
            θ0))) := by
  have hmean :=
    attrMean_tendsto_of_paper_ols_gStar
      (μ := μ) (ν := ν) (Y := Y)
      (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom hCont
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hmean

omit [ProbMeasureAssumptions μ] in
theorem attrM2_tendsto_of_paper_ols_gStar_total
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (ν := ν)
        (A := A) (Y := Yobs)
        (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        attrM2 ν
          (gHat (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
            (fun n =>
              olsThetaHat
                (A := A) (Y := Yobs)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n) n))
      atTop
      (nhds
        (attrM2 ν
          (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
            θ0))) := by
  have hm2 :=
    attrM2_tendsto_of_paper_ols_gStar
      (μ := μ) (ν := ν) (Y := Y)
      (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom hCont
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hm2

omit [ProbMeasureAssumptions μ] in
theorem attrMean_tendsto_of_paper_ols_moments_total_ae
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          attrMean ν
            (gHat (gTotalΘ
              (gB := fun b θ a =>
                gBlockTerm (blk := blk) (β := θ)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds
          (attrMean ν
            (gTotalΘ
              (gB := fun b θ a =>
                gBlockTerm (blk := blk) (β := θ)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
              θ0))) := by
  have hmean :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n =>
            attrMean ν
              (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                (fun n =>
                  olsThetaHat
                    (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                    n) n))
          atTop
          (nhds (attrMean ν (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) :=
    attrMean_tendsto_of_paper_ols_moments_ae
      (μ := μ) (ν := ν) (Y := Y)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom hCont
  refine hmean.mono ?_
  intro ω hω
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hω

omit [ProbMeasureAssumptions μ] in
theorem attrM2_tendsto_of_paper_ols_moments_total_ae
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μ,
        OLSMomentAssumptionsOfAttr
          (ν := ν)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μ := μ) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hCont :
      FunctionalContinuityAssumptions
        (ν := ν)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n =>
          attrM2 ν
            (gHat (gTotalΘ
              (gB := fun b θ a =>
                gBlockTerm (blk := blk) (β := θ)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds
          (attrM2 ν
            (gTotalΘ
              (gB := fun b θ a =>
                gBlockTerm (blk := blk) (β := θ)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
              θ0))) := by
  have hm2 :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n =>
            attrM2 ν
              (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                (fun n =>
                  olsThetaHat
                    (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                    n) n))
          atTop
          (nhds (attrM2 ν (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) :=
    attrM2_tendsto_of_paper_ols_moments_ae
      (μ := μ) (ν := ν) (Y := Y)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom hCont
  refine hm2.mono ?_
  intro ω hω
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hω

end PaperOLS

end ConjointSD
