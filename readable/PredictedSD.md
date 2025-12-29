# PredictedSD.lean

This file defines empirical and population dispersion measures and proves that the empirical [standard deviation](jargon_standard_deviation.md) [converges](jargon_convergence.md) to the population SD under [IID](jargon_iid.md) assumptions.

Definitions:
- `meanHatZ`, `m2HatZ`, `varHatZ`, `sdHatZ` are sample-based (empirical) versions of the [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), and [standard deviation](jargon_standard_deviation.md) for a sequence `Z i`.
- `popMeanZ`, `popM2Z`, `popVarZ`, `popSDZ` are the corresponding population quantities, with `popSDZ` being the population [standard deviation](jargon_standard_deviation.md).
- `IIDAssumptions` bundles the usual IID requirements for the strong law of large numbers (see [iid](jargon_iid.md)).

Main results:
- The strong law implies `meanHatZ` [converges](jargon_convergence.md) to `popMeanZ` [almost everywhere](jargon_almost_everywhere.md).
- Applying the strong law to the squared values gives [convergence](jargon_convergence.md) of `m2HatZ` to `popM2Z`.
- These two converge results are combined to show `varHatZ` [converges](jargon_convergence.md) to `popVarZ`.
- By continuity of the square root, `sdHatZ` [converges](jargon_convergence.md) to `popSDZ`.

In short, the file formalizes the standard "sample [standard deviation](jargon_standard_deviation.md) [converges](jargon_convergence.md) to population SD" result under IID conditions.
