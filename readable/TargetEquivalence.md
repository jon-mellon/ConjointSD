# TargetEquivalence.lean

Lean file: [ConjointSD/TargetEquivalence.lean](../ConjointSD/TargetEquivalence.lean)

This file provides the exact-equality tools and now uses `ProbMeasureAssumptions` instead of standalone probability-measure hypotheses:
1) Exact equality of targets when two score functions match [almost everywhere](jargon_almost_everywhere.md).

Exact equality section:
- If two score functions are equal almost everywhere (see [almost everywhere](jargon_almost_everywhere.md)), then their target human [population](jargon_population.md) [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), and [standard deviation](jargon_standard_deviation.md) (under the attribute distribution) are equal.
- The file proves this step by step: [mean](jargon_mean.md) -> [second moment](jargon_second_moment.md) -> [variance](jargon_variance.md) -> [standard deviation](jargon_standard_deviation.md).

Approximate bounds are now documented in `readable/ApproxTargetEquivalence.md`.

The main idea: if two scores are the same on the attribute-distribution support, then their target human population dispersion targets are the same.

Recent changes: moved approximate bounds to `ConjointSD/ApproxTargetEquivalence.lean`.
