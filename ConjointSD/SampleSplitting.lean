/-
ConjointSD/SampleSplitting.lean

Evaluation-stage convergence for sample-splitting arguments.

For a fixed training index `m`, treat `gHat g θhat m` as a fixed (“oracle”) score
function and apply the oracle SD consistency theorem.
-/

import ConjointSD.SDDecompositionFromConjoint
import ConjointSD.DesignAttributeBridge
import ConjointSD.EstimatedG
import ConjointSD.Assumptions
import ConjointSD.EvalSamplingSRS

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace ConjointSD

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Attr : Type*} [MeasurableSpace Attr]
variable {Θ : Type*}

/--
For fixed training index `m`, the empirical SD of `gHat g θhat m (A i)` converges a.s.
    to the population SD under weighted evaluation moments.
-/
theorem sdHat_fixed_m_tendsto_ae_attrSD
    (ρ : Measure Ω) [ProbMeasureAssumptions ρ]
    (A : ℕ → Ω → Attr)
    (ν : Measure Attr)
    (w : Attr → ℝ)
    (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
    (m : ℕ)
    (h : SplitEvalWeightAssumptionsBounded
      (ρ := ρ) (A := A) (w := w) (g := g) (θhat := θhat) m)
    (hLaw : EvalAttrLawEqPop (ρ := ρ) (A := A) (ν := ν))
    (hW : w = fun _ => (1 : ℝ)) :
    ∀ᵐ ω ∂ρ,
      Tendsto
        (fun n : ℕ =>
          sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
            (W := Wcomp (A := A) (w := w)) n ω)
        atTop
        (nhds (attrSD ν (gHat g θhat m))) := by
  have hMom :
      EvalWeightMatchesPopMoments (ρ := ρ) (A := A) (ν := ν)
        (w := w) (s := gHat g θhat m) :=
    evalWeightMatchesPopMoments_of_law_eq
      (hLaw := hLaw) (w := w) (s := gHat g θhat m) hW
  have hSDZ :
      ∀ᵐ ω ∂ρ,
        Tendsto
          (fun n : ℕ =>
            sdHatZW (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) n ω)
          atTop
          (nhds (designSDZW (κ := ρ)
            (Z := Zcomp (A := A) (g := gHat g θhat m))
            (W := Wcomp (A := A) (w := w)))) := by
    have hPop : DesignAttrIID (κ := ρ) A :=
      { measA := h.hIID.measA, indepA := h.hIID.indepA, identA := h.hIID.identA }
    exact sdHatZW_tendsto_ae_of_score
      (μexp := ρ) (A := A) (w := w) (g := gHat g θhat m)
      hPop h.hMeasW h.hBoundW h.hMeasG h.hBoundG h.hW0
  have hEq :
      designSDZW (κ := ρ)
        (Z := Zcomp (A := A) (g := gHat g θhat m))
        (W := Wcomp (A := A) (w := w)) =
        attrSD ν (gHat g θhat m) :=
    by
      have hMeasWG : Measurable (fun a => w a * gHat g θhat m a) :=
        h.hMeasW.mul h.hMeasG
      have hMeasSq : Measurable (fun a => (gHat g θhat m a) ^ 2) := by
        simpa [pow_two] using (h.hMeasG.mul h.hMeasG)
      have hMeasWSq : Measurable (fun a => w a * (gHat g θhat m a) ^ 2) :=
        h.hMeasW.mul hMeasSq
      have hMeanW :
          designMeanZ (κ := ρ) (Z := Wcomp (A := A) (w := w)) =
            attrMean (kappaDesign (κ := ρ) (A := A)) w := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A) (g := w)
            (hA0 := hMom.measA0) (hg := h.hMeasW))
      have hMeanWZ :
          designMeanZ (κ := ρ)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω
                  * Zcomp (A := A) (g := gHat g θhat m) i ω) =
            attrMean (kappaDesign (κ := ρ) (A := A)) (fun a => w a * gHat g θhat m a) := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A)
            (g := fun a => w a * gHat g θhat m a)
            (hA0 := hMom.measA0) (hg := hMeasWG))
      have hM2WZ :
          designMeanZ (κ := ρ)
              (Z := fun i ω =>
                Wcomp (A := A) (w := w) i ω
                  * (Zcomp (A := A) (g := gHat g θhat m) i ω) ^ 2) =
            attrMean (kappaDesign (κ := ρ) (A := A)) (fun a => w a * (gHat g θhat m a) ^ 2) := by
        simpa using
          (designMeanZ_Zcomp_eq_attrMean (κ := ρ) (A := A)
            (g := fun a => w a * (gHat g θhat m a) ^ 2)
            (hA0 := hMom.measA0) (hg := hMeasWSq))
      have hMean :
          designMeanZW (κ := ρ)
              (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) =
            attrMean ν (gHat g θhat m) := by
        simp [designMeanZW, hMeanW, hMeanWZ, hMom.mean_eq, attrMean]
      have hM2 :
          designM2ZW (κ := ρ)
              (Z := Zcomp (A := A) (g := gHat g θhat m))
              (W := Wcomp (A := A) (w := w)) =
            attrM2 ν (gHat g θhat m) := by
        simpa [designM2ZW, hMeanW, hM2WZ, attrMean, attrM2] using hMom.m2_eq
      simp [designSDZW, designVarZW, attrSD, attrVar, hMean, hM2]
  simpa [hEq] using hSDZ

end

end ConjointSD
