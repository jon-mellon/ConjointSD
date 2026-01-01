# RegressionConsistencyBridge.lean

Lean file: [ConjointSD/RegressionConsistencyBridge.lean](../ConjointSD/RegressionConsistencyBridge.lean)

This file [bridges](jargon_bridge.md) [parameter](jargon_parameter.md) [convergence](jargon_convergence.md) to [plug-in](jargon_plug_in.md) moment convergence using raw `Tendsto` hypotheses and `ProbMeasureAssumptions`.

Key definitions:
- `attrMeanΘ` and `attrM2Θ` treat the attribute-distribution [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) (under `xiAttr`) as functions of the [parameter](jargon_parameter.md).
- `FunctionalContinuityAssumptions` says those functions are [continuous](jargon_continuity.md) at the true [parameter](jargon_parameter.md) for the chosen `xiAttr`.

Main theorems:
- If `theta_hat` [converges](jargon_convergence.md) to `theta0`, and the `xiAttr` [mean](jargon_mean.md) / [second moment](jargon_second_moment.md) are [continuous](jargon_continuity.md) at `theta0`, then the plug‑in mean and second moment converge (the `attrMean_tendsto_of_theta_tendsto` and `attrM2_tendsto_of_theta_tendsto` lemmas).

Additional results:
- For [block](jargon_block.md) models, `BlockFunctionalContinuityAssumptions` and block versions of the mean/second‑moment bridge are provided.
- For linear-in-terms scores, `functionalContinuity_gLin_of_bounded` derives `FunctionalContinuityAssumptions` from bounded/measurable features by rewriting the mean and second moment as finite sums (`attrMean_gLin_eq_sum`, `attrM2_gLin_eq_sum`).
- `functionalContinuity_of_eq` lets you transfer continuity assumptions across pointwise-equal score families.

In plain [terms](jargon_term.md): if the [parameter](jargon_parameter.md) estimates settle down and the `xiAttr` moments depend smoothly on the parameter, then [plug-in](jargon_plug_in.md) moments [converge](jargon_convergence.md) as needed.
