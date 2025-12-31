# DesignAttributeBridge.lean

Lean file: [ConjointSD/DesignAttributeBridge.lean](../ConjointSD/DesignAttributeBridge.lean)

This file connects averages computed under the experimental design distribution to averages computed under the attribute [distribution](jargon_distribution.md) induced by the pushforward law `Measure.map (A 0) μ`. The bridge assumes measurability of `A 0` and uses change-of-variables formulas for the map.

Setup:
- `A 0` is a random attribute draw on the experimental design distribution, with attribute distribution `Measure.map (A 0) μ` (see [distribution](jargon_distribution.md)).
- `g` is a score function on attributes.
- `Zcomp` is the composed process `g (A i)`.

Main [bridges](jargon_bridge.md):
- If `A 0` has [distribution](jargon_distribution.md) `nu`, then the experimental-design [mean](jargon_mean.md) of `g(A 0)` under the sample space equals the mean of `g` under `nu`.
- The same is shown for the [second moment](jargon_second_moment.md), then [variance](jargon_variance.md), then [standard deviation](jargon_standard_deviation.md).

How the proofs work:
- They use a change-of-variables formula for [integrals](jargon_integral.md), so [measurability](jargon_measurable.md) conditions are checked (see [measurable](jargon_measurable.md)).
- [Variance](jargon_variance.md) and [standard deviation](jargon_standard_deviation.md) are reduced to [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) via their definitions.

This lets later files replace abstract experimental-design limits with the paper-facing
`attr*` targets.
