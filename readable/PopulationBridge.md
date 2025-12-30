# PopulationBridge.lean

Lean file: [ConjointSD/PopulationBridge.lean](../ConjointSD/PopulationBridge.lean)

This file connects averages computed on the [population](jargon_population.md) probability space to averages computed under the attribute [distribution](jargon_distribution.md) `nu`. The law-identification and measurability assumptions are now bundled as `MapLawAssumptions`.

Setup:
- `A 0` is a random attribute draw on a big probability space with distribution `nu` (see [distribution](jargon_distribution.md)).
- `g` is a score function on attributes.
- `Zcomp` is the composed process `g (A i)`.

Main [bridges](jargon_bridge.md):
- If `A 0` has [distribution](jargon_distribution.md) `nu`, then the population [mean](jargon_mean.md) of `g(A 0)` under the big space equals the mean of `g` under `nu`.
- The same is shown for the [second moment](jargon_second_moment.md), then [variance](jargon_variance.md), then [standard deviation](jargon_standard_deviation.md).

How the proofs work:
- They use a change-of-variables formula for [integrals](jargon_integral.md), so [measurability](jargon_measurable.md) conditions are checked (see [measurable](jargon_measurable.md)).
- [Variance](jargon_variance.md) and [standard deviation](jargon_standard_deviation.md) are reduced to [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) via their definitions.

This lets later files replace abstract "population-space" limits with the paper-facing `pop*Attr` targets.
