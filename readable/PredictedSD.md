# PredictedSD.lean

Lean file: [ConjointSD/PredictedSD.lean](../ConjointSD/PredictedSD.lean)

This file defines empirical and [population](jargon_population.md) dispersion measures and proves that the empirical [standard deviation](jargon_standard_deviation.md) [converges](jargon_convergence.md) to the population [SD](jargon_standard_deviation.md) under [IID](jargon_iid.md) assumptions. It now uses the bundled `ProbMeasureAssumptions` in place of standalone probability-measure hypotheses.

Definitions:
- `meanHatZ`, `m2HatZ`, `varHatZ`, `sdHatZ`, `rmseHatZ` are sample-based (empirical) versions of the [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md), and [RMSE](jargon_rmse.md) for a sequence `Z i`.
- `popMeanZ`, `popM2Z`, `popVarZ`, `popSDZ`, `popRMSEZ` are the corresponding population quantities, with `popSDZ` being the population [standard deviation](jargon_standard_deviation.md).
- `IIDAssumptions` bundles the usual IID requirements for the strong [LLN](jargon_lln.md) (see [iid](jargon_iid.md)), with the first-moment integrability derived from the second moment under a probability measure.

Main results:
- The strong [LLN](jargon_lln.md) implies `meanHatZ` [converges](jargon_convergence.md) to `popMeanZ` [almost everywhere](jargon_almost_everywhere.md).
- Applying the strong [LLN](jargon_lln.md) to the squared values gives [convergence](jargon_convergence.md) of `m2HatZ` to `popM2Z`.
- By continuity of square root, `rmseHatZ` [converges](jargon_convergence.md) to `popRMSEZ`.
- These two [converge](jargon_convergence.md) results are combined to show `varHatZ` [converges](jargon_convergence.md) to `popVarZ`.
- By [continuity](jargon_continuity.md) of the square root, `sdHatZ` [converges](jargon_convergence.md) to `popSDZ`.

In short, the file formalizes the standard "sample [standard deviation](jargon_standard_deviation.md) [converges](jargon_convergence.md) to population SD" result under [IID](jargon_iid.md) conditions.
