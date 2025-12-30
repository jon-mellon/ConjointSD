import ConjointSD.StatusConjointDesign
import ConjointSD.SurveyWeights
import ConjointSD.Assumptions

noncomputable section
namespace ConjointSD

/-!
Status-conjoint survey weights: placeholders for the paper's weighting scheme.
The actual weight function is a parameter; we record the assumptions needed to
use weighted SD targets.
-/

section StatusSurveyWeights

variable (wStatus : StatusProfile → ℝ)

/-- Weight assumptions for a given score under the status design. -/
def StatusWeightAssumptions (s : StatusProfile → ℝ) : Prop :=
  WeightAssumptions (ν := νStatus) (w := wStatus) (s := s)

/-- Moment-matching assumption for status weights. -/
def StatusWeightMatchesAttrMoments (s : StatusProfile → ℝ) : Prop :=
  WeightMatchesAttrMoments (ν := νStatus) (w := wStatus) (s := s)

lemma status_weighted_sd_eq_attr
    (s : StatusProfile → ℝ)
    (h : StatusWeightMatchesAttrMoments (wStatus := wStatus) s) :
    weightSDAttr νStatus wStatus s = attrSD νStatus s := by
  exact weightSDAttr_eq_attrSD_of_moments (ν := νStatus) (w := wStatus) (s := s) h

end StatusSurveyWeights

end ConjointSD
