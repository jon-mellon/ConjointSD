# EstimatedG.lean

Lean file: [ConjointSD/EstimatedG.lean](../ConjointSD/EstimatedG.lean)

This file formalizes what happens when you replace a true score function `g theta0` with an estimated one `g (theta_hat n)`. It now uses `ProbMeasureAssumptions` instead of standalone probability-measure hypotheses.

Key definitions:
- `gHat` is the [plug-in](jargon_plug_in.md) score: it takes the [parameter](jargon_parameter.md) estimate at step `n` and applies `g`.

Key results:
- Given [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) [convergence](jargon_convergence.md) of the plug‑in score, the file derives [variance](jargon_variance.md) convergence (`attrVar_tendsto_of_mean_m2_tendsto`).
- Using [continuity](jargon_continuity.md) of the square root, it derives [standard deviation](jargon_standard_deviation.md) convergence (`attrSD_tendsto_of_mean_m2_tendsto`).

Logic flow in plain [terms](jargon_term.md):
1) Assume the [plug-in](jargon_plug_in.md) [mean](jargon_mean.md) and [plug-in](jargon_plug_in.md) [second moment](jargon_second_moment.md) [converge](jargon_convergence.md).
2) Since [variance](jargon_variance.md) is second moment minus [mean](jargon_mean.md) squared, variance also [converges](jargon_convergence.md).
3) Standard deviation is the square root of [variance](jargon_variance.md), so it [converges](jargon_convergence.md) too.
