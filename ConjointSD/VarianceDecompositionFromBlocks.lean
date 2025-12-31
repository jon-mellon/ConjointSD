import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

variable {Attr : Type*}
variable {B : Type*} [Fintype B]

/-!
## Integrability assumptions for block functions and their products
-/

structure BlockIntegrable (A : ℕ → Ω → Attr) (g : B → Attr → ℝ) : Prop where
  intX : ∀ b, Integrable (fun ω => g b (A 0 ω)) μ
  intMul : ∀ b c, Integrable (fun ω => g b (A 0 ω) * g c (A 0 ω)) μ

/-- Total additive score. -/
def gTotal (g : B → Attr → ℝ) : Attr → ℝ :=
  fun a => Finset.sum Finset.univ (fun b => g b a)

/-- Raw covariance: E[XY] - E[X]E[Y]. -/
def covRaw (X Y : Ω → ℝ) : ℝ :=
  (∫ ω, X ω * Y ω ∂μ) - (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)

/-- Variance proxy: E[X^2] - (E[X])^2. -/
def varProxy (X : Ω → ℝ) : ℝ :=
  (∫ ω, (X ω) ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2

omit [Fintype B] in
theorem blockIntegrable_of_bounded [ProbMeasureAssumptions μ]
    {Attr : Type*} [MeasurableSpace Attr]
    {A : ℕ → Ω → Attr} {g : B → Attr → ℝ}
    (hA : Measurable (A 0))
    (hMeas : ∀ b, Measurable (g b))
    (hBound : ∀ b, ∃ C, 0 ≤ C ∧ ∀ a, |g b a| ≤ C) :
    BlockIntegrable (μ := μ) (A := A) (g := g) := by
  classical
  refine ⟨?_, ?_⟩
  · intro b
    obtain ⟨C, hC0, hC⟩ := hBound b
    have hMeas' : AEStronglyMeasurable (fun ω => g b (A 0 ω)) μ :=
      (hMeas b).comp hA |>.aestronglyMeasurable
    refine Integrable.of_bound (hf := hMeas') C ?_
    refine ae_of_all μ ?_
    intro ω
    have hCω := hC (A 0 ω)
    simpa [Real.norm_eq_abs] using hCω
  · intro b c
    obtain ⟨Cb, hCb0, hCb⟩ := hBound b
    obtain ⟨Cc, _hCc0, hCc⟩ := hBound c
    have hMeas' :
        AEStronglyMeasurable (fun ω => g b (A 0 ω) * g c (A 0 ω)) μ := by
      have hb : Measurable (fun ω => g b (A 0 ω)) := (hMeas b).comp hA
      have hc : Measurable (fun ω => g c (A 0 ω)) := (hMeas c).comp hA
      exact (hb.mul hc).aestronglyMeasurable
    refine Integrable.of_bound (hf := hMeas') (Cb * Cc) ?_
    refine ae_of_all μ ?_
    intro ω
    have hb := hCb (A 0 ω)
    have hc := hCc (A 0 ω)
    have hmul : ‖g b (A 0 ω) * g c (A 0 ω)‖ ≤ Cb * Cc := by
      calc
        ‖g b (A 0 ω) * g c (A 0 ω)‖
            = |g b (A 0 ω) * g c (A 0 ω)| := by simp
        _ = |g b (A 0 ω)| * |g c (A 0 ω)| := by simp [abs_mul]
        _ ≤ Cb * Cc := by
              exact mul_le_mul hb hc (abs_nonneg _) hCb0
    simpa using hmul

theorem varProxy_sum_eq_sum_covRaw
    (A : ℕ → Ω → Attr) (g : B → Attr → ℝ)
    (h : BlockIntegrable (μ := μ) (A := A) (g := g)) :
    varProxy (μ := μ) (fun ω => gTotal (B := B) g (A 0 ω))
      =
    Finset.sum Finset.univ (fun b =>
      Finset.sum Finset.univ (fun c =>
        covRaw (μ := μ)
          (fun ω => g b (A 0 ω))
          (fun ω => g c (A 0 ω)))) := by
  classical
  -- X b ω = block score, S ω = total score
  let X : B → Ω → ℝ := fun b ω => g b (A 0 ω)
  let S : Ω → ℝ := fun ω => Finset.sum Finset.univ (fun b => X b ω)
  -- pair index finset
  let pairs : Finset (B × B) :=
    (Finset.univ : Finset B).product (Finset.univ : Finset B)
  -- integrability facts
  have hintX : ∀ b, Integrable (X b) μ := by
    intro b
    simpa [X] using h.intX b
  have hintMul : ∀ b c, Integrable (fun ω => X b ω * X c ω) μ := by
    intro b c
    simpa [X] using h.intMul b c
  have hintF : ∀ p : B × B, Integrable (fun ω => X p.1 ω * X p.2 ω) μ := by
    intro p
    simpa using hintMul p.1 p.2
  -- E[S] = ∑_b E[X b]
  have hmean :
      (∫ ω, S ω ∂μ) = Finset.sum Finset.univ (fun b => ∫ ω, X b ω ∂μ) := by
    simpa [S] using
      (integral_finset_sum (μ := μ) (s := (Finset.univ : Finset B))
        (f := fun b ω => X b ω)
        (fun b hb => hintX b))
  /- Helper: double-sum = product-sum pointwise (use pair-function form of `sum_product`). -/
  have hprod (ω : Ω) :
      (Finset.sum Finset.univ (fun i =>
          Finset.sum Finset.univ (fun j => X i ω * X j ω)))
        =
      (Finset.sum pairs (fun p => X p.1 ω * X p.2 ω)) := by
    -- `sum_product` gives: sum over product = double sum, so take `.symm`.
    simpa [pairs] using
      (Finset.sum_product
        (s := (Finset.univ : Finset B))
        (t := (Finset.univ : Finset B))
        (f := fun p : B × B => X p.1 ω * X p.2 ω)).symm
  -- Pointwise: S(ω)^2 = ∑_{p∈pairs} X(p.1,ω)X(p.2,ω)
  have hsq_fun :
      (fun ω => (S ω) ^ 2) = (fun ω => Finset.sum pairs (fun p => X p.1 ω * X p.2 ω)) := by
    funext ω
    calc
      (S ω) ^ 2
          = (Finset.sum Finset.univ (fun b => X b ω))
              * (Finset.sum Finset.univ (fun b => X b ω)) := by
                simp [S, pow_two]
      _ = Finset.sum Finset.univ (fun i =>
            Finset.sum Finset.univ (fun j => X i ω * X j ω)) := by
                simp [Finset.sum_mul_sum]
      _ = Finset.sum pairs (fun p => X p.1 ω * X p.2 ω) := by
                simpa using hprod (ω := ω)
  -- E[S^2] = ∑_{p∈pairs} E[X p.1 * X p.2]
  have hm2 :
      (∫ ω, (S ω) ^ 2 ∂μ)
        =
      Finset.sum pairs (fun p => ∫ ω, (X p.1 ω * X p.2 ω) ∂μ) := by
    calc
      (∫ ω, (S ω) ^ 2 ∂μ)
          = (∫ ω, Finset.sum pairs (fun p => X p.1 ω * X p.2 ω) ∂μ) := by
              simp [hsq_fun]
      _ = Finset.sum pairs (fun p => ∫ ω, (X p.1 ω * X p.2 ω) ∂μ) := by
            simpa using
              (integral_finset_sum (μ := μ) (s := pairs)
                (f := fun p ω => X p.1 ω * X p.2 ω)
                (fun p hp => hintF p))
  -- (∑_b E[X b])^2 = ∑_{pairs} E[X p.1]E[X p.2]  (pair-function form of `sum_product`)
  have hmean_sq :
      (Finset.sum Finset.univ (fun b => ∫ ω, X b ω ∂μ)) ^ 2
        =
      Finset.sum pairs (fun p =>
        (∫ ω, X p.1 ω ∂μ) * (∫ ω, X p.2 ω ∂μ)) := by
    calc
      (Finset.sum Finset.univ (fun b => ∫ ω, X b ω ∂μ)) ^ 2
          =
        (Finset.sum Finset.univ (fun b => ∫ ω, X b ω ∂μ))
          * (Finset.sum Finset.univ (fun b => ∫ ω, X b ω ∂μ)) := by
            simp [pow_two]
      _ =
        Finset.sum Finset.univ (fun i =>
          Finset.sum Finset.univ (fun j =>
            (∫ ω, X i ω ∂μ) * (∫ ω, X j ω ∂μ))) := by
            simp [Finset.sum_mul_sum]
      _ =
        Finset.sum pairs (fun p =>
          (∫ ω, X p.1 ω ∂μ) * (∫ ω, X p.2 ω ∂μ)) := by
          simpa [pairs] using
            (Finset.sum_product
              (s := (Finset.univ : Finset B))
              (t := (Finset.univ : Finset B))
              (f := fun p : B × B =>
                (∫ ω, X p.1 ω ∂μ) * (∫ ω, X p.2 ω ∂μ))).symm
  -- varProxy(S) as a pairs-sum of covRaw
  have var_as_pairs :
      varProxy (μ := μ) S =
        Finset.sum pairs (fun p => covRaw (μ := μ) (X p.1) (X p.2)) := by
    calc
      varProxy (μ := μ) S
          = (∫ ω, (S ω) ^ 2 ∂μ) - (∫ ω, S ω ∂μ) ^ 2 := by
              simp [varProxy]
      _ = (Finset.sum pairs (fun p => ∫ ω, (X p.1 ω * X p.2 ω) ∂μ))
            - (Finset.sum Finset.univ (fun b => ∫ ω, X b ω ∂μ)) ^ 2 := by
              simp [hm2, hmean]
      _ = (Finset.sum pairs (fun p => ∫ ω, (X p.1 ω * X p.2 ω) ∂μ))
            - (Finset.sum pairs (fun p =>
                (∫ ω, X p.1 ω ∂μ) * (∫ ω, X p.2 ω ∂μ))) := by
              simp [hmean_sq]
      _ = Finset.sum pairs (fun p =>
            (∫ ω, (X p.1 ω * X p.2 ω) ∂μ)
              - (∫ ω, X p.1 ω ∂μ) * (∫ ω, X p.2 ω ∂μ)) := by
              simp [Finset.sum_sub_distrib]
      _ = Finset.sum pairs (fun p => covRaw (μ := μ) (X p.1) (X p.2)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            simp [covRaw]
  -- pairs covariance sum = nested covariance sum (pair-function form of `sum_product`)
  have hprodCov :
      (Finset.sum pairs (fun p => covRaw (μ := μ) (X p.1) (X p.2)))
        =
      (Finset.sum Finset.univ (fun b =>
        Finset.sum Finset.univ (fun c => covRaw (μ := μ) (X b) (X c)))) := by
    simpa [pairs] using
      (Finset.sum_product
        (s := (Finset.univ : Finset B))
        (t := (Finset.univ : Finset B))
        (f := fun p : B × B => covRaw (μ := μ) (X p.1) (X p.2)))
  -- gTotal relation: gTotal g (A0 ω) = S ω
  have hS : (fun ω => gTotal (B := B) g (A 0 ω)) = S := by
    funext ω
    simp [gTotal, S, X]
  calc
    varProxy (μ := μ) (fun ω => gTotal (B := B) g (A 0 ω))
        = varProxy (μ := μ) S := by simp [hS]
    _ = Finset.sum pairs (fun p => covRaw (μ := μ) (X p.1) (X p.2)) := var_as_pairs
    _ = Finset.sum Finset.univ (fun b =>
          Finset.sum Finset.univ (fun c =>
            covRaw (μ := μ)
              (fun ω => g b (A 0 ω))
              (fun ω => g c (A 0 ω)))) := by
          simpa [X] using hprodCov

end ConjointSD
