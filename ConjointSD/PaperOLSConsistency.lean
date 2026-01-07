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

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section PaperOLS

variable {Ω Attr : Type*} [MeasurableSpace Ω] [MeasurableSpace Attr]
variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]
variable [DecidableEq (PaperTerm Main Inter)]

variable (μexp : Measure Ω) [IsProbabilityMeasure μexp]
variable (xiAttr : Measure Attr) [IsProbabilityMeasure xiAttr]

variable (Y : Attr → Ω → ℝ)
variable (A : ℕ → Attr) (Yobs : ℕ → ℝ)

variable (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)

omit [DecidableEq (PaperTerm Main Inter)] [Fintype Main] [Fintype Inter] in
lemma measurable_phiPaper
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i)) :
    ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t) := by
  intro t
  cases t with
  | none =>
      simp [φPaper]
  | some s =>
      cases s with
      | inl m =>
          simpa [φPaper] using hmeasMain m
      | inr i =>
          simpa [φPaper] using hmeasInter i

omit [DecidableEq (PaperTerm Main Inter)] [MeasurableSpace Attr] [Fintype Main] [Fintype Inter] in
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

lemma evalAttrIID_of_randomization_stream
    {A : ℕ → Ω → Attr} {Y : Attr → Ω → ℝ}
    (h : ConjointRandomizationStream (μexp := μexp) (A := A) (Y := Y)) :
    EvalAttrIID (κ := μexp) A := by
  rcases h.exists_randomization with
    ⟨R, instR, U, f, hmeasU, hmeasf, hAeq, hindep, hident, _⟩
  letI : MeasurableSpace R := instR
  refine
    { measA := ?_
      indepA := ?_
      identA := ?_ }
  · intro i
    simpa [hAeq i] using hmeasf.comp (hmeasU i)
  · intro i j hij
    have hU : IndepFun (U i) (U j) μexp := hindep hij
    have hA :
        IndepFun (fun ω => f (U i ω)) (fun ω => f (U j ω)) μexp :=
      hU.comp hmeasf hmeasf
    simpa [hAeq i, hAeq j] using hA
  · intro i
    have hU : IdentDistrib (U i) (U 0) μexp μexp := hident i
    have hA : IdentDistrib (fun ω => f (U i ω)) (fun ω => f (U 0 ω)) μexp μexp :=
      hU.comp hmeasf
    simpa [hAeq i, hAeq 0] using hA

omit [DecidableEq (PaperTerm Main Inter)] in
def φBlock
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B) (b : B) :
    PaperTerm Main Inter → Attr → ℝ :=
  fun t a => if blk t = b
    then φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a
    else 0

omit [DecidableEq (PaperTerm Main Inter)] [Fintype Main] [Fintype Inter] in
lemma measurable_φBlock
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B) (b : B)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i)) :
    ∀ t,
      Measurable (φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t) := by
  intro t
  by_cases htb : blk t = b
  · have hEq :
        φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t
          =
        φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t := by
        funext a
        simp [φBlock, htb]
    simpa [hEq] using
      (measurable_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
        hmeasMain hmeasInter t)
  · have hEq :
        φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t
          =
        (fun _ : Attr => (0 : ℝ)) := by
        funext a
        simp [φBlock, htb]
    simp [hEq]

omit [DecidableEq (PaperTerm Main Inter)] [MeasurableSpace Attr] [Fintype Main] [Fintype Inter] in
lemma bounded_φBlock
    {B : Type*} [Fintype B] [DecidableEq B]
    (blk : PaperTerm Main Inter → B) (b : B)
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    ∀ t,
      ∃ C, 0 ≤ C ∧
        ∀ a, |φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t a| ≤ C := by
  intro t
  by_cases htb : blk t = b
  · obtain ⟨C, hC0, hC⟩ :=
      bounded_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
        hboundMain hboundInter t
    refine ⟨C, hC0, ?_⟩
    intro a
    simpa [φBlock, htb] using hC a
  · refine ⟨0, by norm_num, ?_⟩
    intro a
    simp [φBlock, htb]

omit [DecidableEq (PaperTerm Main Inter)] [MeasurableSpace Attr] in
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
theorem cont_mean_gBlockTerm_of_bounded
    {B : Type*} [Fintype B] [DecidableEq B]
    (xiAttr : Measure Attr) [IsProbabilityMeasure xiAttr]
    (blk : PaperTerm Main Inter → B) (b : B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    ContinuousAt
      (attrMeanΘ (xiAttr := xiAttr)
        (g := fun θ =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b))
      θ0 := by
  have hmeasφ :
      ∀ t,
        Measurable
          (φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t) :=
    measurable_φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter)
      (blk := blk) (b := b) hmeasMain hmeasInter
  have hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t a| ≤ C :=
    bounded_φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter)
      (blk := blk) (b := b) hboundMain hboundInter
  have hContLinMean :
      ContinuousAt
        (attrMeanΘ (xiAttr := xiAttr)
          (g := fun θ =>
            gLin (β := θ)
              (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b)))
        θ0 :=
    cont_mean_gLin_of_bounded
      (xiAttr := xiAttr)
      (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b)
      hmeasφ hboundφ θ0
  refine
    cont_mean_of_eq
      (xiAttr := xiAttr)
      (g := fun θ =>
        gLin (β := θ)
          (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b))
      (g' := fun θ =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b)
      (θ0 := θ0)
      ?_
      hContLinMean
  intro θ a
  have hEq :=
    gBlockTerm_eq_gLin_φBlock
      (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk) (b := b) (θ := θ)
  exact (congrArg (fun f => f a) hEq).symm

omit [DecidableEq (PaperTerm Main Inter)] in
theorem cont_m2_gBlockTerm_of_bounded
    {B : Type*} [Fintype B] [DecidableEq B]
    (xiAttr : Measure Attr) [IsProbabilityMeasure xiAttr]
    (blk : PaperTerm Main Inter → B) (b : B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    ContinuousAt
      (attrM2Θ (xiAttr := xiAttr)
        (g := fun θ =>
          gBlockTerm (blk := blk) (β := θ)
            (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b))
      θ0 := by
  have hmeasφ :
      ∀ t,
        Measurable
          (φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t) :=
    measurable_φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter)
      (blk := blk) (b := b) hmeasMain hmeasInter
  have hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b t a| ≤ C :=
    bounded_φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter)
      (blk := blk) (b := b) hboundMain hboundInter
  have hContLinM2 :
      ContinuousAt
        (attrM2Θ (xiAttr := xiAttr)
          (g := fun θ =>
            gLin (β := θ)
              (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b)))
        θ0 :=
    cont_m2_gLin_of_bounded
      (xiAttr := xiAttr)
      (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b)
      hmeasφ hboundφ θ0
  refine
    cont_m2_of_eq
      (xiAttr := xiAttr)
      (g := fun θ =>
        gLin (β := θ)
          (φ := φBlock (Attr := Attr) (fMain := fMain) (fInter := fInter) blk b))
      (g' := fun θ =>
        gBlockTerm (blk := blk) (β := θ)
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b)
      (θ0 := θ0)
      ?_
      hContLinM2
  intro θ a
  have hEq :=
    gBlockTerm_eq_gLin_φBlock
      (Attr := Attr) (fMain := fMain) (fInter := fInter) (blk := blk) (b := b) (θ := θ)
  exact (congrArg (fun f => f a) hEq).symm

omit [DecidableEq (PaperTerm Main Inter)] in
theorem cont_mean_blocks_gBlockTerm_of_bounded
    {B : Type*} [Fintype B] [DecidableEq B]
    (xiAttr : Measure Attr) [IsProbabilityMeasure xiAttr]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    ∀ b : B,
      ContinuousAt
        (attrMeanΘ (xiAttr := xiAttr)
          (g := gBlock (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a) b))
        θ0 := by
  intro b
  simpa [gBlock] using
    cont_mean_gBlockTerm_of_bounded
      (Attr := Attr) (Main := Main) (Inter := Inter)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := xiAttr) (blk := blk) (b := b) (θ0 := θ0)
      hmeasMain hmeasInter hboundMain hboundInter

omit [DecidableEq (PaperTerm Main Inter)] in
theorem cont_m2_blocks_gBlockTerm_of_bounded
    {B : Type*} [Fintype B] [DecidableEq B]
    (xiAttr : Measure Attr) [IsProbabilityMeasure xiAttr]
    (blk : PaperTerm Main Inter → B)
    (θ0 : PaperTerm Main Inter → ℝ)
    (hmeasMain : ∀ m, Measurable (fMain m))
    (hmeasInter : ∀ i, Measurable (fInter i))
    (hboundMain : ∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C)
    (hboundInter : ∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C) :
    ∀ b : B,
      ContinuousAt
        (attrM2Θ (xiAttr := xiAttr)
          (g := gBlock (gB := fun b θ a =>
            gBlockTerm (blk := blk) (β := θ)
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) b a) b))
        θ0 := by
  intro b
  simpa [gBlock] using
    cont_m2_gBlockTerm_of_bounded
      (Attr := Attr) (Main := Main) (Inter := Inter)
      (fMain := fMain) (fInter := fInter)
      (xiAttr := xiAttr) (blk := blk) (b := b) (θ0 := θ0)
      hmeasMain hmeasInter hboundMain hboundInter

omit [DecidableEq (PaperTerm Main Inter)] [MeasurableSpace Attr] in
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

omit [DecidableEq (PaperTerm Main Inter)] [IsProbabilityMeasure μexp] in
theorem paper_ols_normal_eq_of_wellSpecified
    (xiAttr : Measure Attr) [IsProbabilityMeasure xiAttr]
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
          ring
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
      ring
    _ =
      attrCross
        (xiAttr := xiAttr)
        (g := gStar (μexp := μexp) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i := by
      simpa using hCrossEq.symm

omit [DecidableEq (PaperTerm Main Inter)] [IsProbabilityMeasure xiAttr]
  [MeasurableSpace Attr] [IsProbabilityMeasure μexp] in
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

omit [DecidableEq (PaperTerm Main Inter)] [IsProbabilityMeasure xiAttr] in
theorem paper_ols_lln_of_score_assumptions_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hNoise :
      ObservationNoiseAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))
    (hIID : EvalAttrIID (κ := μexp) Aω)
    (hMeasGram :
      ∀ i j,
        Measurable (fun a =>
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
            * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)))
    (hBoundGram :
      ∀ i j, ∃ C, 0 ≤ C ∧ ∀ a,
        |(φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
            * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)| ≤ C)
    (hMeasCross :
      ∀ i,
        Measurable (fun a =>
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
            * gStar (μexp := μexp) (Y := Y) a))
    (hBoundCross :
      ∀ i, ∃ C, 0 ≤ C ∧ ∀ a,
        |(φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
            * gStar (μexp := μexp) (Y := Y) a| ≤ C) :
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
        (μexp := μexp) (A := Aω) (g := gGram) hIID (hMeasGram i j) (hBoundGram i j)
    have hpop :
        designMeanZ (κ := μexp) (Z := Zcomp (A := Aω) (g := gGram))
          =
        attrMean (kappaDesign (κ := μexp) (A := Aω)) gGram :=
      designMeanZ_Zcomp_eq_attrMean
        (κ := μexp) (A := Aω) (g := gGram)
        (hA0 := hIID.measA 0)
        (hg := hMeasGram i j)
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
        (μexp := μexp) (A := Aω) (g := gCross) hIID (hMeasCross i) (hBoundCross i)
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
        (hA0 := hIID.measA 0)
        (hg := hMeasCross i)
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
  (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Aω) (Y := Y))
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
  have hPop : EvalAttrIID (κ := μexp) Aω :=
    evalAttrIID_of_randomization_stream
      (μexp := μexp) (A := Aω) (Y := Y) hRand
  have hmeasφ :
      ∀ t, Measurable (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t) :=
    measurable_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hDesign.meas_fMain hDesign.meas_fInter
  have hboundφ :
      ∀ t, ∃ C, 0 ≤ C ∧
        ∀ a, |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) t a| ≤ C :=
    bounded_phiPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)
      hDesign.bound_fMain hDesign.bound_fInter
  have hMeasGram :
      ∀ i j,
        Measurable (fun a =>
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
            * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)) :=
    fun i j => (hmeasφ i).mul (hmeasφ j)
  have hBoundGram :
      ∀ i j, ∃ C, 0 ≤ C ∧ ∀ a,
        |(φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
            * (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a)| ≤ C := by
    intro i j
    obtain ⟨Ci, hCi0, hCi⟩ := hboundφ i
    obtain ⟨Cj, hCj0, hCj⟩ := hboundφ j
    refine ⟨Ci * Cj, mul_nonneg hCi0 hCj0, ?_⟩
    intro a
    have hmul : |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a|
        * |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) j a| ≤ Ci * Cj :=
      mul_le_mul (hCi a) (hCj a) (abs_nonneg _) hCi0
    simpa [abs_mul] using hmul
  have hMeasCross :
      ∀ i,
        Measurable (fun a =>
          (φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
            * gStar (μexp := μexp) (Y := Y) a) :=
    fun i => (hmeasφ i).mul hDesign.meas_gStar
  have hBoundCross :
      ∀ i, ∃ C, 0 ≤ C ∧ ∀ a,
        |(φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a)
            * gStar (μexp := μexp) (Y := Y) a| ≤ C := by
    intro i
    obtain ⟨Ci, hCi0, hCi⟩ := hboundφ i
    obtain ⟨Cg, hCg0, hCg⟩ := hDesign.bound_gStar
    refine ⟨Ci * Cg, mul_nonneg hCi0 hCg0, ?_⟩
    intro a
    have hmul : |φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter) i a|
        * |gStar (μexp := μexp) (Y := Y) a| ≤ Ci * Cg :=
      mul_le_mul (hCi a) (hCg a) (abs_nonneg _) hCi0
    simpa [abs_mul] using hmul
  have hLLN :=
    paper_ols_lln_of_score_assumptions_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω)
      (hNoise := hDesign.obs_noise) (hIID := hPop)
      (hMeasGram := hMeasGram) (hBoundGram := hBoundGram)
      (hMeasCross := hMeasCross) (hBoundCross := hBoundCross)
  refine hLLN.mono ?_
  intro ω hω
  rcases hω with ⟨hgram, hcross⟩
  exact ⟨hgram, hcross⟩

theorem paper_ols_gramInv_tendsto_of_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Aω) (Y := Y))
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
      (Aω := Aω) (Yobsω := Yobsω) hRand hDesign
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

omit [IsProbabilityMeasure μexp] [IsProbabilityMeasure xiAttr] in
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

omit [IsProbabilityMeasure μexp] [IsProbabilityMeasure xiAttr] in
theorem paper_ols_attr_moments_of_lln_fullrank_ae
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
      (∀ i j,
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
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
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
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))) := by
  refine (hLLN.and hInv).mono ?_
  intro ω hω
  rcases hω with ⟨hLLNω, hInvω⟩
  exact ⟨hInvω, hLLNω.2⟩

theorem paper_ols_attr_moments_of_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Aω) (Y := Y))
    (hDesign :
      PaperOLSDesignAssumptions
        (μexp := μexp) (A := Aω) (Y := Y) (Yobs := Yobsω)
        (fMain := fMain) (fInter := fInter))
    (hFull :
      PaperOLSFullRankAssumptions
        (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (fMain := fMain) (fInter := fInter)) :
    ∀ᵐ ω ∂μexp,
      (∀ i j,
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
              (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
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
  have hPop : EvalAttrIID (κ := μexp) Aω :=
    evalAttrIID_of_randomization_stream
      (μexp := μexp) (A := Aω) (Y := Y) hRand
  have hA0 : Measurable (Aω 0) := hPop.measA 0
  letI : IsProbabilityMeasure (kappaDesign (κ := μexp) (A := Aω)) :=
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
      (Aω := Aω) (Yobsω := Yobsω) hRand hDesign
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
      (Aω := Aω) (Yobsω := Yobsω) hRand hDesign hFull
  exact
    paper_ols_attr_moments_of_lln_fullrank_ae
      (μexp := μexp)
      (xiAttr := kappaDesign (κ := μexp) (A := Aω))
      (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω)
      hLLN hInv

theorem theta_tendsto_of_paper_ols_design_ae
    {Aω : ℕ → Ω → Attr} {Yobsω : ℕ → Ω → ℝ}
    (θ0 : PaperTerm Main Inter → ℝ)
    (hRand :
      ConjointRandomizationStream (μexp := μexp) (A := Aω) (Y := Y))
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
  have hPop : EvalAttrIID (κ := μexp) Aω :=
    evalAttrIID_of_randomization_stream
      (μexp := μexp) (A := Aω) (Y := Y) hRand
  have hA0 : Measurable (Aω 0) := hPop.measA 0
  letI : IsProbabilityMeasure (kappaDesign (κ := μexp) (A := Aω)) :=
    probMeasureAssumptions_map_of_measurable
      (κ := μexp) (A := Aω) (hA0 := hA0)
  have hMom :
      ∀ᵐ ω ∂μexp,
        (∀ i j,
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
                (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j)))
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
    paper_ols_attr_moments_of_design_ae
      (μexp := μexp) (Y := Y) (fMain := fMain) (fInter := fInter)
      (Aω := Aω) (Yobsω := Yobsω)
      hRand hDesign hFull
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
      (μexp := μexp)
      (xiAttr := kappaDesign (κ := μexp) (A := Aω))
      (Y := Y) (fMain := fMain) (fInter := fInter)
      (θ0 := θ0) hFull
      (paper_ols_normal_eq_of_wellSpecified
        (μexp := μexp) (Y := Y)
        (Attr := Attr) (Main := Main) (Inter := Inter)
        (fMain := fMain) (fInter := fInter)
        (xiAttr := kappaDesign (κ := μexp) (A := Aω)) (θ0 := θ0)
        hDesign.meas_fMain hDesign.meas_fInter
        hDesign.bound_fMain hDesign.bound_fInter
        hspec)
  filter_upwards [hMom] with ω hMomω
  exact
    olsThetaHat_tendsto_of_attr_moments
      (xiAttr := kappaDesign (κ := μexp) (A := Aω))
      (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
      (g := gStar (μexp := μexp) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      (θ0 := θ0)
      (hGramInv := hMomω.1)
      (hCross := hMomω.2)
      (hId := hId)
end PaperOLS

end ConjointSD
