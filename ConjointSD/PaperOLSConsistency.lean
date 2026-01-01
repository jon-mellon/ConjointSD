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
import ConjointSD.RegressionConsistencyBridge

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

variable (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
variable (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]

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
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    FunctionalContinuityAssumptions (xiAttr := xiAttr)
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
      (xiAttr := xiAttr) (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      hmeasφ hboundφ θ0)

omit [DecidableEq (PaperTerm Main Inter)] in
theorem functionalContinuity_gTotalΘ_of_bounded
    {B : Type*} [Fintype B] [DecidableEq B]
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    FunctionalContinuityAssumptions (xiAttr := xiAttr)
      (g := gTotalΘ
        (gB := fun b θ a =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a))
      θ0 := by
  have hContPaper :
      FunctionalContinuityAssumptions (xiAttr := xiAttr)
        (g := fun θ =>
          gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ) θ0 :=
    functionalContinuity_gPaper_of_bounded
      (Attr := Attr) (Main := Main) (Inter := Inter)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := xiAttr) (θ0 := θ0)
      hmeasMain hmeasInter hboundMain hboundInter
  refine
    functionalContinuity_of_eq
      (xiAttr := xiAttr)
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
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (blk : PaperTerm Main Inter → B) (b : B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    FunctionalContinuityAssumptions (xiAttr := xiAttr)
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
    · have hEq :
          φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t
            =
          φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t := by
          funext a
          simp [φBlock, htb]
      simpa [hEq] using hmeasφ t
    · have hEq :
          φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t
            =
          (fun _ : Attr => (0 : ℝ)) := by
          funext a
          simp [φBlock, htb]
      simpa [hEq] using (measurable_const : Measurable (fun _ : Attr => (0 : ℝ)))
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
      FunctionalContinuityAssumptions (xiAttr := xiAttr)
        (g := fun θ =>
          gLin (β := θ)
            (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b)) θ0 :=
    functionalContinuity_gLin_of_bounded
      (xiAttr := xiAttr)
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
      (xiAttr := xiAttr)
      (g := fun θ =>
        gLin (β := θ)
          (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b))
      (g' := gBlock
        (gB := fun b θ a =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a) b)
      (θ0 := θ0)
      (fun θ a => (hEq θ a).symm)
      hContLin

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
theorem paper_ols_normal_eq_of_wellSpecified
    (xiAttr : Measure Attr) [ProbMeasureAssumptions xiAttr]
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C)
    (hspec :
      WellSpecified
        (μexp := μexp) (Y := Y) (β := θ0)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) :
    (attrGram
        (xiAttr := xiAttr)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).mulVec θ0
      =
    attrCross
      (xiAttr := xiAttr)
      (g := gStar (μexp := μexp) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) := by
  classical
  have hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t) :=
    measurable_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hmeasMain hmeasInter
  have hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C :=
    bounded_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hboundMain hboundInter
  funext i
  let φCross : PaperTerm Main Inter → Attr → ℝ :=
    fun t a =>
      φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
        * φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a
  have hmeasCross : ∀ t, Measurable (φCross t) := by
    intro t
    exact (hmeasφ i).mul (hmeasφ t)
  have hboundCross :
      ∀ t, ∃ C, 0 ≤ C ∧ ∀ a, |φCross t a| ≤ C := by
    intro t
    exact bounded_mul (hf := hboundφ i) (hg := hboundφ t)
  have hCrossEq :
      attrCross
          (xiAttr := xiAttr)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i
        =
      ∑ t,
        θ0 t * attrMean xiAttr (fun a =>
          φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
            * φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a) := by
    have hsum :
        attrMean xiAttr (gLin (β := θ0) (φ := φCross))
          =
        ∑ t, θ0 t * attrMean xiAttr (φCross t) :=
      attrMean_gLin_eq_sum
        (xiAttr := xiAttr) (φ := φCross) hmeasCross hboundCross θ0
    have hspec' :
        ∀ a,
          gStar (μexp := μexp) (Y := Y) a
            =
          gLin (β := θ0)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) a := by
      intro a
      simpa using (hspec a).symm
    have hCross :
        attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i
          =
        attrMean xiAttr (gLin (β := θ0) (φ := φCross)) := by
      refine congrArg (fun f => attrMean xiAttr f) ?_
      funext a
      calc
        φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
            * gStar (μexp := μexp) (Y := Y) a
            =
          φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
            *
          gLin (β := θ0)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) a := by
          simp [hspec']
        _ =
          φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
            * ∑ t, θ0 t
              * φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a := by
          rfl
        _ =
          ∑ t,
            φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
              * (θ0 t
                * φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a) := by
          simpa using
            (Finset.mul_sum
              (a := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              (s := (Finset.univ : Finset (PaperTerm Main Inter)))
              (f := fun t =>
                θ0 t * φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a))
        _ =
          ∑ t,
            θ0 t * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
              * φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          simp [mul_comm, mul_left_comm, mul_assoc]
        _ = ∑ t, θ0 t * φCross t a := by
          rfl
        _ = gLin (β := θ0) (φ := φCross) a := by
          rfl
    calc
      attrCross
          (xiAttr := xiAttr)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i
          =
        attrMean xiAttr (gLin (β := θ0) (φ := φCross)) := hCross
      _ = ∑ t, θ0 t * attrMean xiAttr (φCross t) := hsum
  calc
    (attrGram
        (xiAttr := xiAttr)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).mulVec θ0 i
        =
      ∑ t,
        attrMean xiAttr (fun a =>
          φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
            * φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a)
          * θ0 t := by
      simp [Matrix.mulVec, dotProduct, attrGram]
    _ =
      ∑ t,
        θ0 t * attrMean xiAttr (fun a =>
          φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
            * φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ =
      attrCross
        (xiAttr := xiAttr)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i := by
      simpa using hCrossEq.symm

omit [DecidableEq (PaperTerm Main Inter)] in
lemma scoreAssumptions_gram_of_design
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (Aω : ℕ → Ω → Attr)
    (hPop : DesignAttrIID (κ := μexp) Aω)
    (hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t))
    (hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C)
    (i j : PaperTerm Main Inter) :
    ScoreAssumptions
      (κ := μexp) (A := Aω)
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
      (μexp := μexp) (A := Aω)
      (g := fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a))
      hPop hmeas hbound

omit [DecidableEq (PaperTerm Main Inter)] in
lemma scoreAssumptions_cross_of_design
    (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
    (Aω : ℕ → Ω → Attr)
    (Y : Attr → Ω → ℝ)
    (hPop : DesignAttrIID (κ := μexp) Aω)
    (hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t))
    (hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C)
    (hmeasStar : Measurable (gStar (μexp := μexp) (Y := Y)))
    (hboundStar : ∃ C, 0 ≤ C ∧ ∀ a, |gStar (μexp := μexp) (Y := Y) a| ≤ C)
    (i : PaperTerm Main Inter) :
    ScoreAssumptions
      (κ := μexp) (A := Aω)
      (g := fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μexp := μexp) (Y := Y) a) := by
  have hmeas :
      Measurable (fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μexp := μexp) (Y := Y) a) :=
    (hmeasφ i).mul hmeasStar
  have hbound :
      ∃ C, 0 ≤ C ∧
        ∀ a,
          |(φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * gStar (μexp := μexp) (Y := Y) a| ≤ C :=
    bounded_mul (hf := hboundφ i) (hg := hboundStar)
  exact
    scoreAssumptions_of_bounded
      (μexp := μexp) (A := Aω)
      (g := fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μexp := μexp) (Y := Y) a)
      hPop hmeas hbound

omit [DecidableEq (PaperTerm Main Inter)] [ProbMeasureAssumptions xiAttr] in
lemma crossVec_eq_meanHatZ_add_noise
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (ω : Ω) (i : PaperTerm Main Inter) :
    (fun n =>
      crossVec
        (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        n i)
      =
    (fun n =>
      meanHatZ
          (Z := Zcomp
            (A := Aω)
            (g := fun a =>
              (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
                * gStar (μexp := μexp) (Y := Y) a))
          n ω
        +
      ((n : ℝ)⁻¹) *
        ∑ k ∈ Finset.range n,
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
            (Aω k ω)
            * (Yobsω k ω - gStar (μexp := μexp) (Y := Y) (Aω k ω))) := by
  classical
  let gCross : Attr → ℝ :=
    fun a =>
      (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
        * gStar (μexp := μexp) (Y := Y) a
  funext n
  have hsum_yobs :
      (∑ k : Fin n,
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
            (Aω k ω) * Yobsω k ω)
        =
      ∑ k ∈ Finset.range n,
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
            (Aω k ω) * Yobsω k ω := by
    simpa using
      (Fin.sum_univ_eq_sum_range (n := n)
        (fun k =>
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
            (Aω k ω) * Yobsω k ω))
  have hsum_cross :
      ∑ k ∈ Finset.range n,
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
            (Aω k ω) * Yobsω k ω
        =
      ∑ k ∈ Finset.range n,
          gCross (Aω k ω)
        +
      ∑ k ∈ Finset.range n,
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
            (Aω k ω)
            * (Yobsω k ω - gStar (μexp := μexp) (Y := Y) (Aω k ω)) := by
    calc
      ∑ k ∈ Finset.range n,
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
            (Aω k ω) * Yobsω k ω
          =
        ∑ k ∈ Finset.range n,
          ((φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
              (Aω k ω) * gStar (μexp := μexp) (Y := Y) (Aω k ω)
            +
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
            (Aω k ω)
            * (Yobsω k ω - gStar (μexp := μexp) (Y := Y) (Aω k ω))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
      _ = _ := by
          simp [Finset.sum_add_distrib, gCross]
  simp [crossVec, meanHatZ, Zcomp, gCross, smul_eq_mul, hsum_yobs, hsum_cross, mul_add]

omit [DecidableEq (PaperTerm Main Inter)] [ProbMeasureAssumptions xiAttr] in
theorem paper_ols_lln_of_score_assumptions_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hNoise :
      ObservationNoiseAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
    (hScoreGram :
      ∀ i j,
        ScoreAssumptions
          (κ := μexp) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)))
    (hScoreCross :
      ∀ i,
        ScoreAssumptions
          (κ := μexp) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * gStar (μexp := μexp) (Y := Y) a)) :
    ∀ᵐ ω ∂μexp,
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
              (xiAttr := kappaDesign (κ := μexp) (A := Aω))
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
        (xiAttr := kappaDesign (κ := μexp) (A := Aω))
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))) := by
  classical
  have hgram : ∀ i j, ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          gramMatrix
            (A := fun k => Aω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i j)
        atTop
        (nhds
          (attrGram
            (xiAttr := kappaDesign (κ := μexp) (A := Aω))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)) := by
    intro i j
    let gGram : Attr → ℝ :=
      fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)
    have hmean :
        ∀ᵐ ω ∂μexp,
          Tendsto
            (fun n : ℕ =>
              meanHatZ (Z := Zcomp (A := Aω) (g := gGram)) n ω)
            atTop
            (nhds (designMeanZ (κ := μexp) (Z := Zcomp (A := Aω) (g := gGram)))) :=
      meanHatZ_tendsto_ae_of_score
        (μexp := μexp) (A := Aω) (g := gGram) (hScoreGram i j)
    have hpop :
        designMeanZ (κ := μexp) (Z := Zcomp (A := Aω) (g := gGram))
          =
        attrMean (kappaDesign (κ := μexp) (A := Aω)) gGram :=
      designMeanZ_Zcomp_eq_attrMean
        (κ := μexp) (A := Aω) (g := gGram)
        (hA0 := (hScoreGram i j).designAttrIID.measA 0)
        (hg := (hScoreGram i j).meas_g)
    refine hmean.mono ?_
    intro ω hω
    have hω' :
        Tendsto
          (fun n =>
            meanHatZ (Z := Zcomp (A := Aω) (g := gGram)) n ω)
          atTop
          (nhds (attrMean (kappaDesign (κ := μexp) (A := Aω)) gGram)) := by
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
  have hcross : ∀ i, ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          crossVec
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i)
        atTop
        (nhds
          (attrCross
            (xiAttr := kappaDesign (κ := μexp) (A := Aω))
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i)) := by
    intro i
    let gCross : Attr → ℝ :=
      fun a =>
        (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
          * gStar (μexp := μexp) (Y := Y) a
    have hmean :
        ∀ᵐ ω ∂μexp,
          Tendsto
            (fun n : ℕ =>
              meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω)
            atTop
            (nhds (designMeanZ (κ := μexp) (Z := Zcomp (A := Aω) (g := gCross)))) :=
      meanHatZ_tendsto_ae_of_score
        (μexp := μexp) (A := Aω) (g := gCross) (hScoreCross i)
    have hnoise :
        ∀ᵐ ω ∂μexp,
          Tendsto
            (fun n : ℕ =>
              ((n : ℝ)⁻¹) *
                ∑ k ∈ Finset.range n,
                  (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
                    (Aω k ω)
                    * (Yobsω k ω - gStar (μexp := μexp) (Y := Y) (Aω k ω)))
            atTop
            (nhds 0) :=
      hNoise.noise_lln i
    have hpop :
        designMeanZ (κ := μexp) (Z := Zcomp (A := Aω) (g := gCross))
          =
        attrMean (kappaDesign (κ := μexp) (A := Aω)) gCross :=
      designMeanZ_Zcomp_eq_attrMean
        (κ := μexp) (A := Aω) (g := gCross)
        (hA0 := (hScoreCross i).designAttrIID.measA 0)
        (hg := (hScoreCross i).meas_g)
    refine (hmean.and hnoise).mono ?_
    intro ω hω
    rcases hω with ⟨hω, hωnoise⟩
    have hω' :
        Tendsto
          (fun n =>
            meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω)
          atTop
          (nhds (attrMean (kappaDesign (κ := μexp) (A := Aω)) gCross)) := by
      simpa [hpop] using hω
    have hcross_eq :
        (fun n =>
          crossVec
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n i)
          =
        (fun n =>
          meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω
            +
          ((n : ℝ)⁻¹) *
            ∑ k ∈ Finset.range n,
              (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
                (Aω k ω)
                * (Yobsω k ω - gStar (μexp := μexp) (Y := Y) (Aω k ω))) := by
      simpa [gCross] using
        (crossVec_eq_meanHatZ_add_noise
          (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
          (Aω := Aω) (Yobsω := Yobsω) ω i)
    have hsum_tendsto :
        Tendsto
          (fun n =>
            meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω
              +
            ((n : ℝ)⁻¹) *
              ∑ k ∈ Finset.range n,
                (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
                  (Aω k ω)
                  * (Yobsω k ω - gStar (μexp := μexp) (Y := Y) (Aω k ω)))
          atTop
          (nhds (attrMean (kappaDesign (κ := μexp) (A := Aω)) gCross + 0)) :=
      hω'.add hωnoise
    have hsum_tendsto' :
        Tendsto
          (fun n =>
            meanHatZ (Z := Zcomp (A := Aω) (g := gCross)) n ω
              +
            ((n : ℝ)⁻¹) *
              ∑ k ∈ Finset.range n,
                (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i)
                  (Aω k ω)
                  * (Yobsω k ω - gStar (μexp := μexp) (Y := Y) (Aω k ω)))
          atTop
          (nhds (attrMean (kappaDesign (κ := μexp) (A := Aω)) gCross)) := by
      simpa using hsum_tendsto
    simpa [attrCross, gCross, hcross_eq] using hsum_tendsto'
  have hgram_all : ∀ᵐ ω ∂μexp, ∀ i j, Tendsto
      (fun n =>
        gramMatrix
          (A := fun k => Aω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n i j)
      atTop
      (nhds
        (attrGram
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j)) := by
    refine (ae_all_iff.2 ?_)
    intro i
    refine (ae_all_iff.2 ?_)
    intro j
    exact hgram i j
  have hcross_all : ∀ᵐ ω ∂μexp, ∀ i, Tendsto
      (fun n =>
        crossVec
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n i)
      atTop
      (nhds
        (attrCross
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i)) := by
    refine (ae_all_iff.2 ?_)
    intro i
    exact hcross i
  refine (hgram_all.and hcross_all).mono ?_
  intro ω hω
  rcases hω with ⟨hgramω, hcrossω⟩
  exact ⟨hgramω, hcrossω⟩

omit [DecidableEq (PaperTerm Main Inter)] in
theorem paper_ols_lln_of_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hPop : DesignAttrIID (κ := μexp) Aω)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (fMain := fMain) (fInter := fInter)) :
    ∀ᵐ ω ∂μexp,
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
              (xiAttr := kappaDesign (κ := μexp) (A := Aω))
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
              (xiAttr := kappaDesign (κ := μexp) (A := Aω))
              (g := gStar (μexp := μexp) (Y := Y))
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
          (κ := μexp) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)) :=
    fun i j =>
      scoreAssumptions_gram_of_design
        (μexp := μexp) (Aω := Aω) (fMain := fMain) (fInter := fInter)
        hPop hmeasφ hboundφ i j
  have hScoreCross :
      ∀ i,
        ScoreAssumptions
          (κ := μexp) (A := Aω)
          (g := fun a =>
            (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
              * gStar (μexp := μexp) (Y := Y) a) :=
    fun i =>
      scoreAssumptions_cross_of_design
        (μexp := μexp) (Aω := Aω) (Y := Y) (fMain := fMain) (fInter := fInter)
        hPop hmeasφ hboundφ hDesign.meas_gStar hDesign.bound_gStar i
  have hLLN :=
    paper_ols_lln_of_score_assumptions_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω)
      (hNoise := hDesign.obs_noise)
      (hScoreGram := hScoreGram) (hScoreCross := hScoreCross)
  refine hLLN.mono ?_
  intro ω hω
  rcases hω with ⟨hgram, hcross⟩
  exact ⟨hgram, hcross⟩

theorem paper_ols_gramInv_tendsto_of_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hPop : DesignAttrIID (κ := μexp) Aω)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (fMain := fMain) (fInter := fInter)) :
    ∀ᵐ ω ∂μexp,
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
              (xiAttr := kappaDesign (κ := μexp) (A := Aω))
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)) := by
  have hLLN :=
    paper_ols_lln_of_design_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω) hPop hDesign
  have hdet :
      IsUnit
        (attrGram
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).det :=
    (Matrix.isUnit_iff_isUnit_det
      (A :=
        attrGram
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))).1
      hFull.gram_isUnit
  have hdet' :
      (attrGram
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).det ≠ 0 :=
    hdet.ne_zero
  have hcont :
      ContinuousAt Ring.inverse
        (attrGram
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).det := by
    simpa [Ring.inverse] using (continuousAt_inv₀ hdet')
  have hcontInv :
      ContinuousAt Inv.inv
        (attrGram
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) :=
    continuousAt_matrix_inv _ hcont
  refine hLLN.mono ?_
  intro ω hω
  rcases hω with ⟨hgram, _⟩
  have hGramω :
      Tendsto
        (fun n =>
          gramMatrix
            (A := fun k => Aω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)
        atTop
        (nhds
          (attrGram
            (xiAttr := kappaDesign (κ := μexp) (A := Aω))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))) := by
    refine tendsto_pi_nhds.2 ?_
    intro i
    refine tendsto_pi_nhds.2 ?_
    intro j
    simpa using hgram i j
  have hInvω :
      Tendsto
        (fun n =>
          (gramMatrix
            (A := fun k => Aω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)⁻¹)
        atTop
        (nhds
          ((attrGram
            (xiAttr := kappaDesign (κ := μexp) (A := Aω))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹)) :=
    (hcontInv.tendsto).comp hGramω
  have hInvω' := tendsto_pi_nhds.1 hInvω
  intro i j
  have hRow := hInvω' i
  have hEntry := (tendsto_pi_nhds.1 hRow) j
  simpa using hEntry

theorem paper_ols_fullRank_of_orthogonal
    (hOrth :
      PaperOLSOrthogonalAssumptions
        (xiAttr := xiAttr) (fMain := fMain) (fInter := fInter)) :
    PaperOLSFullRankAssumptions
      (xiAttr := xiAttr) (fMain := fMain) (fInter := fInter) := by
  classical
  let v : PaperTerm Main Inter → ℝ :=
    fun i =>
      attrMean
        (xiAttr := xiAttr)
        (fun a =>
          φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a
            *
          φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
  have hDiag :
      attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        =
      Matrix.diagonal v := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [attrGram, v, Matrix.diagonal]
    · have hzero := hOrth.gram_diag i j h
      simp [attrGram, v, Matrix.diagonal, h, hzero]
  have hProd : ∀ i, v i ≠ 0 := by
    intro i
    simpa [v] using hOrth.gram_pos i
  have hDet :
      (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).det ≠ 0 := by
    have hProd' : (∏ i, v i) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 ?_
      intro i hi
      exact hProd i
    calc
      (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).det
          =
        (Matrix.diagonal v).det := by
          simpa [hDiag]
      _ = ∏ i, v i := by
          simpa using (Matrix.det_diagonal (d := v))
      _ ≠ 0 := hProd'
  have hDetUnit :
      IsUnit
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).det :=
    (isUnit_iff_ne_zero).2 hDet
  exact
    { gram_isUnit :=
        (Matrix.isUnit_iff_isUnit_det
          (A :=
            attrGram
              (xiAttr := xiAttr)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))).2
          hDetUnit }

theorem paper_ols_fullRank_of_posDef
    (hPos :
      PaperOLSPosDefAssumptions
        (xiAttr := xiAttr) (fMain := fMain) (fInter := fInter)) :
    PaperOLSFullRankAssumptions
      (xiAttr := xiAttr) (fMain := fMain) (fInter := fInter) := by
  classical
  refine { gram_isUnit := ?_ }
  simpa using
    (Matrix.PosDef.isUnit
      (M :=
        attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
      hPos.gram_posdef)

theorem paper_ols_theta0_eq_of_normal_eq
    (θ0 : PaperTerm Main Inter → ℝ)
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := xiAttr) (fMain := fMain) (fInter := fInter))
    (hNormal :
      (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).mulVec θ0
        =
      attrCross
        (xiAttr := xiAttr)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) :
    θ0 =
      (attrGram
        (xiAttr := xiAttr)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
      (attrCross
        (xiAttr := xiAttr)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) := by
  have hdet :
      IsUnit
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).det :=
    (Matrix.isUnit_iff_isUnit_det
      (A :=
        attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))).1
      hFull.gram_isUnit
  let _ :=
    Matrix.invertibleOfIsUnitDet
      (A :=
        attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
      hdet
  have hM :
      attrCross
          (xiAttr := xiAttr)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        =
      (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))).mulVec θ0 := by
    simpa using hNormal.symm
  have h :=
    Matrix.inv_mulVec_eq_vec
      (A :=
        attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
      (u :=
        attrCross
          (xiAttr := xiAttr)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
      (v := θ0) hM
  simpa using h.symm

variable {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}

omit [ProbMeasureAssumptions μexp] [ProbMeasureAssumptions xiAttr] in
theorem paper_ols_attr_moments_of_lln_fullrank_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hLLN :
      ∀ᵐ ω ∂μexp,
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
                (xiAttr := xiAttr)
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
                (xiAttr := xiAttr)
                (g := gStar (μexp := μexp) (Y := Y))
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))))
    (hInv :
      ∀ᵐ ω ∂μexp,
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
                (xiAttr := xiAttr)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j))) :
    ∀ᵐ ω ∂μexp,
      OLSMomentAssumptionsOfAttr
        (xiAttr := xiAttr)
        (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0 := by
  refine (hLLN.and hInv).mono ?_
  intro ω hω
  rcases hω with ⟨hLLNω, hInvω⟩
  refine
    { gramInv_tendsto := hInvω
      cross_tendsto := hLLNω.2 }

theorem paper_ols_attr_moments_of_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (θ0 : PaperTerm Main Inter → ℝ)
    (hPop : DesignAttrIID (κ := μexp) Aω)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (fMain := fMain) (fInter := fInter)) :
    ∀ᵐ ω ∂μexp,
      OLSMomentAssumptionsOfAttr
        (xiAttr := kappaDesign (κ := μexp) (A := Aω))
        (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0 := by
  have hA0 : Measurable (Aω 0) := hPop.measA 0
  letI : ProbMeasureAssumptions (kappaDesign (κ := μexp) (A := Aω)) :=
    probMeasureAssumptions_map_of_measurable
      (κ := μexp) (A := Aω) (hA0 := hA0)
  have hLLN :
      ∀ᵐ ω ∂μexp,
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
                (xiAttr := kappaDesign (κ := μexp) (A := Aω))
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
                (xiAttr := kappaDesign (κ := μexp) (A := Aω))
                (g := gStar (μexp := μexp) (Y := Y))
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))) :=
    paper_ols_lln_of_design_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω) hPop hDesign
  have hInv :
      ∀ᵐ ω ∂μexp,
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
                (xiAttr := kappaDesign (κ := μexp) (A := Aω))
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)) :=
    paper_ols_gramInv_tendsto_of_design_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω) hPop hDesign hFull
  exact
    paper_ols_attr_moments_of_lln_fullrank_ae
      (μexp := μexp) (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω)
      hLLN hInv

omit [ProbMeasureAssumptions μexp] [ProbMeasureAssumptions xiAttr] in
theorem theta_tendsto_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μexp,
        OLSMomentAssumptionsOfAttr
          (xiAttr := xiAttr)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))) :
    ∀ᵐ ω ∂μexp,
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
      (xiAttr := xiAttr)
      (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
      (g := gStar (μexp := μexp) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      hω hId)

theorem theta_tendsto_of_paper_ols_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (θ0 : PaperTerm Main Inter → ℝ)
    (hPop : DesignAttrIID (κ := μexp) Aω)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (fMain := fMain) (fInter := fInter))
    (hspec :
      WellSpecified
        (μexp := μexp) (Y := Y) (β := θ0)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          olsThetaHat
            (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            n)
        atTop
        (nhds θ0) := by
  have hA0 : Measurable (Aω 0) := hPop.measA 0
  letI : ProbMeasureAssumptions (kappaDesign (κ := μexp) (A := Aω)) :=
    probMeasureAssumptions_map_of_measurable
      (κ := μexp) (A := Aω) (hA0 := hA0)
  have hMom :
      ∀ᵐ ω ∂μexp,
        OLSMomentAssumptionsOfAttr
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0 :=
    paper_ols_attr_moments_of_design_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω)
      hPop hDesign hFull
  have hId :
      θ0 =
        (attrGram
          (xiAttr := kappaDesign (κ := μexp) (A := Aω))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := kappaDesign (κ := μexp) (A := Aω))
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) :=
    paper_ols_theta0_eq_of_normal_eq
      (μexp := μexp) (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hFull
      (paper_ols_normal_eq_of_wellSpecified
        (μexp := μexp) (Y := Y)
        (Attr := Attr) (Main := Main) (Inter := Inter)
        (fMain := fMain) (fInter := fInter)
        (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (θ0 := θ0)
        hDesign.meas_fMain hDesign.meas_fInter
        hDesign.bound_fMain hDesign.bound_fInter
        hspec)
  exact
    theta_tendsto_of_paper_ols_moments_ae
      (μexp := μexp) (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom hId

omit [ProbMeasureAssumptions μexp] in
theorem attrMean_tendsto_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μexp,
        OLSMomentAssumptionsOfAttr
          (xiAttr := xiAttr)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          attrMean xiAttr
            (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds (attrMean xiAttr (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  refine (theta_tendsto_of_paper_ols_moments_ae
    (μexp := μexp) (xiAttr := xiAttr) (Y := Y) (fMain := fMain) (fInter := fInter)
    (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom hId).mono ?_
  intro ω hθ
  simpa using
    (attrMean_tendsto_of_theta_tendsto
      (xiAttr := xiAttr)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hθ hCont)

omit [ProbMeasureAssumptions μexp] in
theorem attrM2_tendsto_of_paper_ols_moments_ae
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μexp,
        OLSMomentAssumptionsOfAttr
          (xiAttr := xiAttr)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          attrM2 xiAttr
            (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds (attrM2 xiAttr (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  refine (theta_tendsto_of_paper_ols_moments_ae
    (μexp := μexp) (xiAttr := xiAttr) (Y := Y) (fMain := fMain) (fInter := fInter)
    (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom hId).mono ?_
  intro ω hθ
  simpa using
    (attrM2_tendsto_of_theta_tendsto
      (xiAttr := xiAttr)
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
    (hPop : DesignAttrIID (κ := μexp) Aω)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (fMain := fMain) (fInter := fInter))
    (hspec :
      WellSpecified
        (μexp := μexp) (Y := Y) (β := θ0)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          attrMean xiAttr
            (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds (attrMean xiAttr (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  have hθ :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n =>
            olsThetaHat
              (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n)
          atTop
          (nhds θ0) :=
    theta_tendsto_of_paper_ols_design_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω)
      hPop hDesign hFull hspec
  refine hθ.mono ?_
  intro ω hω
  simpa using
    (attrMean_tendsto_of_theta_tendsto
      (xiAttr := xiAttr)
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
    (hPop : DesignAttrIID (κ := μexp) Aω)
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (fMain := fMain) (fInter := fInter))
    (hspec :
      WellSpecified
        (μexp := μexp) (Y := Y) (β := θ0)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          attrM2 xiAttr
            (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              (fun n =>
                olsThetaHat
                  (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                  n) n))
        atTop
        (nhds (attrM2 xiAttr (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
  have hθ :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n =>
            olsThetaHat
              (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
              n)
          atTop
          (nhds θ0) :=
    theta_tendsto_of_paper_ols_design_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω)
      hPop hDesign hFull hspec
  refine hθ.mono ?_
  intro ω hω
  simpa using
    (attrM2_tendsto_of_theta_tendsto
      (xiAttr := xiAttr)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hω hCont)

omit [ProbMeasureAssumptions μexp] [ProbMeasureAssumptions xiAttr] in
theorem theta_tendsto_of_paper_ols_moments
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (xiAttr := xiAttr)
        (A := A) (Y := Yobs)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))) :
    Tendsto
      (fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      atTop
      (nhds θ0) :=
  olsThetaHat_tendsto_of_attr_moments
    (xiAttr := xiAttr) (A := A) (Y := Yobs)
    (g := gStar (μexp := μexp) (Y := Y))
    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
    (θ0 := θ0)
    hMom hId

omit [ProbMeasureAssumptions μexp] in
theorem attrMean_tendsto_of_paper_ols_gStar
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (xiAttr := xiAttr)
        (A := A) (Y := Yobs)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        attrMean xiAttr
          (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            (fun n =>
              olsThetaHat
                (A := A) (Y := Yobs)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n) n))
      atTop
      (nhds (attrMean xiAttr (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
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
      (μexp := μexp) (xiAttr := xiAttr)
      (Y := Y) (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom hId
  simpa using
    (attrMean_tendsto_of_theta_tendsto
      (xiAttr := xiAttr)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hθ hCont)

omit [ProbMeasureAssumptions μexp] in
theorem attrM2_tendsto_of_paper_ols_gStar
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (xiAttr := xiAttr)
        (A := A) (Y := Yobs)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        attrM2 xiAttr
          (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
            (fun n =>
              olsThetaHat
                (A := A) (Y := Yobs)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                n) n))
      atTop
      (nhds (attrM2 xiAttr (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) := by
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
      (μexp := μexp) (xiAttr := xiAttr)
      (Y := Y) (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom hId
  simpa using
    (attrM2_tendsto_of_theta_tendsto
      (xiAttr := xiAttr)
      (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (θhat := fun n =>
        olsThetaHat
          (A := A) (Y := Yobs)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          n)
      hθ hCont)

omit [ProbMeasureAssumptions μexp] in
theorem attrMean_tendsto_of_paper_ols_gStar_total
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (xiAttr := xiAttr)
        (A := A) (Y := Yobs)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        attrMean xiAttr
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
        (attrMean xiAttr
          (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
            θ0))) := by
  have hmean :=
    attrMean_tendsto_of_paper_ols_gStar
      (μexp := μexp) (xiAttr := xiAttr) (Y := Y)
      (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom hId hCont
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hmean

omit [ProbMeasureAssumptions μexp] in
theorem attrM2_tendsto_of_paper_ols_gStar_total
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      OLSMomentAssumptionsOfAttr
        (xiAttr := xiAttr)
        (A := A) (Y := Yobs)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    Tendsto
      (fun n =>
        attrM2 xiAttr
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
        (attrM2 xiAttr
          (gTotalΘ
            (gB := fun b θ a =>
              gBlockTerm (blk := blk) (β := θ)
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
            θ0))) := by
  have hm2 :=
    attrM2_tendsto_of_paper_ols_gStar
      (μexp := μexp) (xiAttr := xiAttr) (Y := Y)
      (A := A) (Yobs := Yobs)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hMom hId hCont
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hm2

omit [ProbMeasureAssumptions μexp] in
theorem attrMean_tendsto_of_paper_ols_moments_total_ae
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μexp,
        OLSMomentAssumptionsOfAttr
          (xiAttr := xiAttr)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          attrMean xiAttr
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
          (attrMean xiAttr
            (gTotalΘ
              (gB := fun b θ a =>
                gBlockTerm (blk := blk) (β := θ)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
              θ0))) := by
  have hmean :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n =>
            attrMean xiAttr
              (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                (fun n =>
                  olsThetaHat
                    (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                    n) n))
          atTop
          (nhds (attrMean xiAttr (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) :=
    attrMean_tendsto_of_paper_ols_moments_ae
      (μexp := μexp) (xiAttr := xiAttr) (Y := Y)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom hId hCont
  refine hmean.mono ?_
  intro ω hω
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hω

omit [ProbMeasureAssumptions μexp] in
theorem attrM2_tendsto_of_paper_ols_moments_total_ae
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hMom :
      ∀ᵐ ω ∂μexp,
        OLSMomentAssumptionsOfAttr
          (xiAttr := xiAttr)
          (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
          (g := gStar (μexp := μexp) (Y := Y))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
          θ0)
    (hId :
      θ0 =
        (attrGram
          (xiAttr := xiAttr)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
          (attrCross
            (xiAttr := xiAttr)
            (g := gStar (μexp := μexp) (Y := Y))
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))))
    (hCont :
      FunctionalContinuityAssumptions
        (xiAttr := xiAttr)
        (g := gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
        θ0) :
    ∀ᵐ ω ∂μexp,
      Tendsto
        (fun n =>
          attrM2 xiAttr
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
          (attrM2 xiAttr
            (gTotalΘ
              (gB := fun b θ a =>
                gBlockTerm (blk := blk) (β := θ)
                  (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a)
              θ0))) := by
  have hm2 :
      ∀ᵐ ω ∂μexp,
        Tendsto
          (fun n =>
            attrM2 xiAttr
              (gHat (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                (fun n =>
                  olsThetaHat
                    (A := fun k => Aω k ω) (Y := fun k => Yobsω k ω)
                    (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
                    n) n))
          atTop
          (nhds (attrM2 xiAttr (gPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) θ0))) :=
    attrM2_tendsto_of_paper_ols_moments_ae
      (μexp := μexp) (xiAttr := xiAttr) (Y := Y)
      (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) (Aω := Aω) (Yobsω := Yobsω) hMom hId hCont
  refine hm2.mono ?_
  intro ω hω
  simpa
      [gPaper_eq_gTotalΘ_blocks (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk),
        gTotalΘ]
    using hω

end PaperOLS

end ConjointSD
