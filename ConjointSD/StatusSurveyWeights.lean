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
def StatusWeightMatchesPopMoments (s : StatusProfile → ℝ) : Prop :=
  WeightMatchesPopMoments (ν := νStatus) (w := wStatus) (s := s)

lemma status_weighted_sd_eq_pop
    (s : StatusProfile → ℝ)
    (h : StatusWeightMatchesPopMoments (wStatus := wStatus) s) :
    weightSDAttr νStatus wStatus s = popSDAttr νStatus s := by
  exact weightSDAttr_eq_popSDAttr_of_moments (ν := νStatus) (w := wStatus) (s := s) h

end StatusSurveyWeights

end ConjointSD
