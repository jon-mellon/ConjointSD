-- ConjointSD/Defs.lean
import Mathlib

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section
namespace ConjointSD

/-!
Core definitions shared across the project.

This file is intentionally definition-only (no heavy theorems), so other modules can
import it without pulling in lots of dependencies.
-/

section IdentificationBasics

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {Attr : Type*}

/-- Event that the shown profile equals `x`. -/
def eventX (X : Ω → Attr) (x : Attr) : Set Ω := {ω | X ω = x}

/-- Conditional mean on an event `s`: `(∫ Z d(μ.restrict s)) / (μ s).toReal`. -/
def condMean (μ : Measure Ω) (Z : Ω → ℝ) (s : Set Ω) : ℝ :=
  (∫ ω, Z ω ∂ (μ.restrict s)) / (μ s).toReal

/-- Mean of a potential outcome under profile `x`. -/
def potMean (μ : Measure Ω) (Y : Attr → Ω → ℝ) (x : Attr) : ℝ :=
  ∫ ω, Y x ω ∂μ

/-- AMCE between profiles `x` and `x'`. -/
def amce (μ : Measure Ω) (Y : Attr → Ω → ℝ) (x x' : Attr) : ℝ :=
  potMean (μ := μ) Y x' - potMean (μ := μ) Y x

end IdentificationBasics

section AdditiveDecomposition

variable {Attr : Type*}
variable {B : Type*} [Fintype B]

/-- Total additive score. -/
def gTotal (g : B → Attr → ℝ) : Attr → ℝ :=
  fun a => ∑ b, g b a

end AdditiveDecomposition

section VarianceDefs

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Raw covariance: `E[XY] - E[X]E[Y]`. -/
def covRaw (X Y : Ω → ℝ) : ℝ :=
  (∫ ω, X ω * Y ω ∂μ) - (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)

/-- Variance proxy: `E[X^2] - (E[X])^2`. -/
def varProxy (X : Ω → ℝ) : ℝ :=
  (∫ ω, (X ω) ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2

end VarianceDefs

end ConjointSD
