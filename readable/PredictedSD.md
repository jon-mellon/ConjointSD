# PredictedSD.lean

Lean file: [ConjointSD/PredictedSD.lean](../ConjointSD/PredictedSD.lean)

This file defines empirical and experimental-design dispersion measures and proves that the empirical [standard deviation](jargon_standard_deviation.md) [converges](jargon_convergence.md) to the design-distribution [SD](jargon_standard_deviation.md) under [IID](jargon_iid.md) assumptions. It now uses the bundled `ProbMeasureAssumptions` in place of standalone probability-measure hypotheses.

Definitions:
- `meanHatZ`, `m2HatZ`, `varHatZ`, `sdHatZ`, `rmseHatZ` are sample-based (empirical) versions of the [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md), and [RMSE](jargon_rmse.md) for a sequence `Z i`.
- `meanHatZW`, `m2HatZW`, `varHatZW`, `sdHatZW` are weighted empirical analogues that use a weight stream `W i` (e.g., evaluation weights based on attributes).
- `designMeanZ`, `designM2Z`, `designVarZ`, `designSDZ`, `designRMSEZ` are the corresponding experimental-design quantities, with `designSDZ` being the design-distribution [standard deviation](jargon_standard_deviation.md).
- `designMeanZW`, `designM2ZW`, `designVarZW`, `designSDZW` are the weighted design-distribution quantities, defined as ratios of weighted integrals.
- `IIDAssumptions` bundles the usual IID requirements for the strong [LLN](jargon_lln.md) (see [iid](jargon_iid.md)), with the first-moment integrability derived from the second moment under a probability measure.

Main results:
- The strong [LLN](jargon_lln.md) implies `meanHatZ` [converges](jargon_convergence.md) to `designMeanZ` [almost everywhere](jargon_almost_everywhere.md).
- Applying the strong [LLN](jargon_lln.md) to the squared values gives [convergence](jargon_convergence.md) of `m2HatZ` to `designM2Z`.
- By continuity of square root, `rmseHatZ` [converges](jargon_convergence.md) to `designRMSEZ`.
- These two [converge](jargon_convergence.md) results are combined to show `varHatZ` [converges](jargon_convergence.md) to `designVarZ`.
- By [continuity](jargon_continuity.md) of the square root, `sdHatZ` [converges](jargon_convergence.md) to `designSDZ`.
- Weighted counterparts show `meanHatZW`, `m2HatZW`, and `sdHatZW` [converge](jargon_convergence.md) to their weighted design limits when the weight stream satisfies IID and the weight mean is nonzero.

In short, the file formalizes the standard "sample [standard deviation](jargon_standard_deviation.md) [converges](jargon_convergence.md) to design-distribution SD" result under [IID](jargon_iid.md) conditions.
