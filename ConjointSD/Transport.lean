import ConjointSD.Assumptions

noncomputable section
namespace ConjointSD

/-!
# Transport (attribute-distribution prediction) layer

Definitions and assumptions are centralized in:
- `ConjointSD.Defs`
- `ConjointSD.Assumptions`
-/

open MeasureTheory

section

variable {Attr : Type*} [MeasurableSpace Attr]

theorem attrSD_eq_of_moments {ν₁ ν₂ : Measure Attr} (s : Attr → ℝ)
    (hmean : attrMean ν₁ s = attrMean ν₂ s)
    (hm2 : attrM2 ν₁ s = attrM2 ν₂ s) :
    attrSD ν₁ s = attrSD ν₂ s := by
  simp [attrSD, attrVar, hmean, hm2]

end

end ConjointSD
