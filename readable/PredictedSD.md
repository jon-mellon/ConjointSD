# PredictedSD.lean

Lean file: [ConjointSD/PredictedSD.lean](../ConjointSD/PredictedSD.lean)

This file defines empirical and experimental-design dispersion measures for real-valued processes and includes basic helper lemmas (e.g., measurability of squaring). The LLN-based consistency results are stated in score-based form in `SDDecompositionFromConjoint.lean`.

Definitions:
- `meanHatZ`, `m2HatZ`, `varHatZ`, `sdHatZ`, `rmseHatZ` are sample-based (empirical) versions of the [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md), and [RMSE](jargon_rmse.md) for a sequence `Z i`.
- `meanHatZW`, `m2HatZW`, `varHatZW`, `sdHatZW` are weighted empirical analogues that use a weight stream `W i` (e.g., evaluation weights based on attributes).
- `designMeanZ`, `designM2Z`, `designVarZ`, `designSDZ`, `designRMSEZ` are the corresponding experimental-design quantities, with `designSDZ` being the design-distribution [standard deviation](jargon_standard_deviation.md).
- `designMeanZW`, `designM2ZW`, `designVarZW`, `designSDZW` are the weighted design-distribution quantities, defined as ratios of weighted integrals.

Main results:
- LLN-based SD consistency is handled in `SDDecompositionFromConjoint.lean`, where IID comes from `DesignAttrIID` (often derived from `ConjointRandomizationStream`) alongside boundedness/measurability of the score functions.
