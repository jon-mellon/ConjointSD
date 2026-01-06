# EvalSamplingSRS

Lean file: [ConjointSD/EvalSamplingSRS.lean](../ConjointSD/EvalSamplingSRS.lean)

This file derives the weighted-moment assumption used by the evaluation SD machinery
from a simple random sample (SRS) evaluation law and uniform weights.

Key pieces:
- `evalWeightMatchesPopMoments_of_law_eq`: if the evaluation attribute law equals `ν`
  and weights are constant 1, then the weighted moment match holds for any score `s`.
