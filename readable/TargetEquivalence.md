# TargetEquivalence.lean

This file provides two related tools:
1) Exact equality of targets when two score functions match [almost everywhere](jargon_almost_everywhere.md).
2) Approximate bounds when two score functions are close [almost everywhere](jargon_almost_everywhere.md).

Exact equality section:
- If two score functions are equal almost everywhere (see [almost everywhere](jargon_almost_everywhere.md)), then their [population](jargon_population.md) [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), and [standard deviation](jargon_standard_deviation.md) are equal.
- The file proves this step by step: [mean](jargon_mean.md) -> [second moment](jargon_second_moment.md) -> [variance](jargon_variance.md) -> [standard deviation](jargon_standard_deviation.md).

Approximate section:
- Defines `ApproxInvarianceAE`: two score functions differ by at most epsilon almost everywhere (see [almost everywhere](jargon_almost_everywhere.md)).
- Defines `BoundedAE`: a uniform bound on a score function [almost everywhere](jargon_almost_everywhere.md).
- Uses these to show that the difference in [means](jargon_mean.md) is at most epsilon.
- Uses bounds to control the difference in [second moments](jargon_second_moment.md) and [variances](jargon_variance.md).
- Uses a square-root inequality to control the difference in [standard deviations](jargon_standard_deviation.md).

The main idea: if two scores are the same (or nearly the same) on the population support, then their population dispersion targets are the same (or nearly the same).
