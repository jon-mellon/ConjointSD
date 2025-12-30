# StatusSurveyWeights.lean

Lean file: [ConjointSD/StatusSurveyWeights.lean](../ConjointSD/StatusSurveyWeights.lean)

This file introduces survey-weight placeholders for the status conjoint. The weight
function `wStatus` is treated as a parameter and the file records the assumptions
needed to use weighted SD targets.

What it provides:
- `StatusWeightAssumptions`: shorthand for `WeightAssumptions` under `νStatus`.
- `StatusWeightMatchesAttrMoments`: shorthand for `WeightMatchesAttrMoments` under `νStatus`.
- `status_weighted_sd_eq_attr`: if weighted moments match target human population
  moments, the weighted SD equals the target human population SD for the given score.

This is a lightweight status-specific wrapper around `SurveyWeights`.
