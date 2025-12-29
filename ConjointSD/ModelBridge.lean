import ConjointSD.VarianceDecompositionFromBlocks
import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

/-!
# Model bridge: from linear score models to block/component scores
-/

/--
Block score defined by summing the terms assigned to block `b`.

We use an `if` formulation so the additivity proof is just sum-swapping + `simp`.
-/
def gBlockTerm {Attr B Term : Type*} [Fintype B] [Fintype Term] [DecidableEq B]
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) : B → Attr → ℝ :=
  by
    classical
    let _ := (inferInstance : Fintype B)
    exact fun b a => ∑ t, (if blk t = b then (β t * φ t a) else 0)

/--
**Additivity bridge:** allocating each model term to exactly one block implies the total score
equals the sum of block scores.
-/
theorem gLin_eq_gTotal_blocks
    {Attr B Term : Type*}
    [Fintype B] [Fintype Term] [DecidableEq B]
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) :
    gLin (β := β) (φ := φ)
      =
    gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) := by
  classical
  funext a
  -- Prove RHS = LHS pointwise, then flip.
  have h :
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) a
        =
      gLin (β := β) (φ := φ) a := by
    calc
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) a
          = (∑ b : B, ∑ t : Term, (if blk t = b then (β t * φ t a) else 0)) := by
              simp [gTotal, gBlockTerm]
      _   = (∑ t : Term, ∑ b : B, (if blk t = b then (β t * φ t a) else 0)) := by
              -- swap the two finite sums
              simpa using
                (Finset.sum_comm
                  (s := (Finset.univ : Finset B))
                  (t := (Finset.univ : Finset Term))
                  (f := fun b t => (if blk t = b then (β t * φ t a) else 0)))
      _   = (∑ t : Term, (β t * φ t a)) := by
              -- inner sum over b picks exactly b = blk t
              refine Finset.sum_congr rfl ?_
              intro t ht
              -- `simp` knows how to evaluate `∑ b, if blk t = b then r else 0`
              simp [eq_comm]
      _   = gLin (β := β) (φ := φ) a := by
              simp [gLin]
  simpa using h.symm

/--
If the estimand is well-specified by a linear-in-terms model, then it decomposes into blocks
(using the chosen term-to-block assignment).
-/
theorem gStar_eq_sum_blocks_of_WellSpecified
    {Ω Attr B Term : Type*}
    [MeasurableSpace Ω] [Fintype B] [Fintype Term] [DecidableEq B]
    (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ)
    (hspec : WellSpecified (μ := μ) (Y := Y) (β := β) (φ := φ)) :
    gStar (μ := μ) (Y := Y)
      =
    gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) := by
  classical
  funext x
  have hblocks :
      gLin (β := β) (φ := φ)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gLin_eq_gTotal_blocks (B := B) (Term := Term) (blk := blk) (β := β) (φ := φ)
  calc
    gStar (μ := μ) (Y := Y) x
        = gLin (β := β) (φ := φ) x := by
            simpa [WellSpecified] using (hspec x).symm
    _   = gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x := by
            simpa using congrArg (fun f => f x) hblocks

/--
If the estimand is within ε of a linear-in-terms model, it is within ε of the induced block sum.
-/
theorem gStar_approx_sum_blocks_of_ApproxWellSpecified
    {Ω Attr B Term : Type*}
    [MeasurableSpace Ω] [Fintype B] [Fintype Term] [DecidableEq B]
    (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ)
    (hspec : ApproxWellSpecified (μ := μ) (Y := Y) (β := β) (φ := φ) ε) :
    ∀ x,
      |gStar (μ := μ) (Y := Y) x
        - gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x|
        ≤ ε := by
  classical
  intro x
  have hblocks :
      gLin (β := β) (φ := φ)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gLin_eq_gTotal_blocks (B := B) (Term := Term) (blk := blk) (β := β) (φ := φ)
  have hlin :
      gLin (β := β) (φ := φ) x
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x := by
    simpa using congrArg (fun f => f x) hblocks
  have h := hspec x
  simpa [hlin, abs_sub_comm] using h

/--
AE version of the approximation bridge: if `gStar` is ε-close to the linear model ν-a.e.,
then it is ε-close to the induced block sum ν-a.e.
-/
theorem gStar_approx_sum_blocks_of_ApproxWellSpecifiedAE
    {Ω Attr B Term : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Attr] [Fintype B] [Fintype Term] [DecidableEq B]
    (ν : Measure Attr) (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : Term → B) (β : Term → ℝ) (φ : Term → Attr → ℝ) (ε : ℝ)
    (hspec : ApproxWellSpecifiedAE (ν := ν) (μ := μ) (Y := Y) (β := β) (φ := φ) ε) :
    ∀ᵐ x ∂ν,
      |gStar (μ := μ) (Y := Y) x
        - gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x|
        ≤ ε := by
  classical
  have hblocks :
      gLin (β := β) (φ := φ)
        =
      gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) :=
    gLin_eq_gTotal_blocks (B := B) (Term := Term) (blk := blk) (β := β) (φ := φ)
  have hlin :
      ∀ x,
        gLin (β := β) (φ := φ) x
          =
        gTotal (B := B) (g := gBlockTerm (blk := blk) (β := β) (φ := φ)) x := by
    intro x
    simpa using congrArg (fun f => f x) hblocks
  refine hspec.mono ?_
  intro x hx
  simpa [hlin x, abs_sub_comm] using hx

/-
## Parametric model: intercept + main effects + selected interactions

The paper runs a linear regression with an intercept, a collection of main-effect terms,
and a finite list of interaction terms. We encode exactly that term set and show that the
stated parametric equality of the causal estimand implies `WellSpecified`, which can then
be fed into the block decomposition bridge above.
-/

section ParametricMainInteractions

variable {Ω Attr : Type*} [MeasurableSpace Ω]

variable {Main Inter : Type*} [Fintype Main] [Fintype Inter]

/-- Expand `gLin` with the paper term set into intercept + main + interaction sums. -/
theorem gLin_eq_parametric
    (β0 : ℝ) (βMain : Main → ℝ) (βInter : Inter → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ) (x : Attr) :
    gLin (β := βPaper (β0 := β0) (βMain := βMain) (βInter := βInter))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) x
      =
    β0 + (∑ m, βMain m * fMain m x) + (∑ i, βInter i * fInter i x) := by
  classical
  -- Split the finite sum over `Option (Sum Main Inter)` into the three term types.
  -- `Fintype.sum_option` peels off the intercept; `Fintype.sum_sum_type` splits the Sum.
  simp [gLin, βPaper, φPaper, Fintype.sum_option, Fintype.sum_sum_type, add_assoc]

/--
Parametric equality of `gStar` with the paper’s regression model implies well-specification
for the induced term set `(βPaper, φPaper)`.
-/
theorem wellSpecified_of_parametricMainInteractions
    (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (β0 : ℝ) (βMain : Main → ℝ) (βInter : Inter → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)
    (hParam :
      ParametricMainInteractions (μ := μ) (Y := Y)
        (β0 := β0) (βMain := βMain) (βInter := βInter)
        (fMain := fMain) (fInter := fInter)) :
    WellSpecified (μ := μ) (Y := Y)
      (β := βPaper (β0 := β0) (βMain := βMain) (βInter := βInter))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) := by
  classical
  intro x
  have hlin :=
    gLin_eq_parametric (β0 := β0) (βMain := βMain) (βInter := βInter)
      (fMain := fMain) (fInter := fInter) x
  have hmodel :
      β0 + (∑ m, βMain m * fMain m x) + (∑ i, βInter i * fInter i x)
        =
      gStar (μ := μ) (Y := Y) x := by
    simpa using (hParam x).symm
  exact by
    calc
      gLin (β := βPaper (β0 := β0) (βMain := βMain) (βInter := βInter))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) x
          = β0 + (∑ m, βMain m * fMain m x) + (∑ i, βInter i * fInter i x) :=
        hlin
      _ = gStar (μ := μ) (Y := Y) x := hmodel

/--
Block decomposition specialized to the paper parametric model: if `gStar` equals the
intercept/main/interaction regression surface, then it also equals the sum of block scores
formed from that same term set.
-/
theorem gStar_eq_sum_blocks_of_parametricMainInteractions
    {B : Type*} [Fintype B] [DecidableEq B]
    (μ : Measure Ω) (Y : Attr → Ω → ℝ)
    (blk : PaperTerm Main Inter → B)
    (β0 : ℝ) (βMain : Main → ℝ) (βInter : Inter → ℝ)
    (fMain : Main → Attr → ℝ) (fInter : Inter → Attr → ℝ)
    (hParam :
      ParametricMainInteractions (μ := μ) (Y := Y)
        (β0 := β0) (βMain := βMain) (βInter := βInter)
        (fMain := fMain) (fInter := fInter)) :
    gStar (μ := μ) (Y := Y)
      =
    gTotal (B := B)
      (g := gBlockTerm (blk := blk)
          (β := βPaper (β0 := β0) (βMain := βMain) (βInter := βInter))
          (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))) := by
  classical
  have hspec :=
    wellSpecified_of_parametricMainInteractions
      (μ := μ) (Y := Y)
      (β0 := β0) (βMain := βMain) (βInter := βInter)
      (fMain := fMain) (fInter := fInter) hParam
  exact
    gStar_eq_sum_blocks_of_WellSpecified
      (μ := μ) (Y := Y) (blk := blk)
      (β := βPaper (β0 := β0) (βMain := βMain) (βInter := βInter))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      hspec

end ParametricMainInteractions

end ConjointSD
