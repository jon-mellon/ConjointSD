import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.Assumptions

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω)

variable {Attr : Type*}
variable {B : Type*} [Fintype B]

/-!
## Integrability assumptions for block functions and their products
-/

structure BlockIntegrable (A : ℕ → Ω → Attr) (g : B → Attr → ℝ) : Prop where
  intX : ∀ b, Integrable (fun ω => g b (A 0 ω)) μexp
  intMul : ∀ b c, Integrable (fun ω => g b (A 0 ω) * g c (A 0 ω)) μexp

/-- Total additive score. -/
def gTotal (g : B → Attr → ℝ) : Attr → ℝ :=
  fun a => Finset.sum Finset.univ (fun b => g b a)

/-- Raw covariance: E[XY] - E[X]E[Y]. -/
def covRaw (X Y : Ω → ℝ) : ℝ :=
  (∫ ω, X ω * Y ω ∂μexp) - (∫ ω, X ω ∂μexp) * (∫ ω, Y ω ∂μexp)

/-- Variance proxy: E[X^2] - (E[X])^2. -/
def varProxy (X : Ω → ℝ) : ℝ :=
  (∫ ω, (X ω) ^ 2 ∂μexp) - (∫ ω, X ω ∂μexp) ^ 2

end ConjointSD
