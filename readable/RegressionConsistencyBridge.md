# RegressionConsistencyBridge.lean

Lean file: [ConjointSD/RegressionConsistencyBridge.lean](../ConjointSD/RegressionConsistencyBridge.lean)

This file [bridges](jargon_bridge.md) [parameter](jargon_parameter.md) [convergence](jargon_convergence.md) to [plug-in](jargon_plug_in.md) moment convergence. It now packages the convergence premise as `ThetaTendstoAssumptions` and uses `ProbMeasureAssumptions` for probability-measure hypotheses.

Key definitions:
- `attrMeanΘ` and `attrM2Θ` treat the target human [population](jargon_population.md) [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) (under the attribute distribution) as functions of the [parameter](jargon_parameter.md).
- `FunctionalContinuityAssumptions` says those functions are [continuous](jargon_continuity.md) at the true [parameter](jargon_parameter.md).

Main theorem:
- If `theta_hat` [converges](jargon_convergence.md) to `theta0`, and the target human population [mean](jargon_mean.md) / [second moment](jargon_second_moment.md) are [continuous](jargon_continuity.md) at `theta0`, then `GEstimationAssumptions` holds. This is the package used by later files.

Additional results:
- A [variance](jargon_variance.md) [convergence](jargon_convergence.md) [lemma](jargon_lemma.md) is derived from [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) convergence.
- For [block](jargon_block.md) models, `BlockFunctionalContinuityAssumptions` and a block version of the [bridge](jargon_bridge.md) are provided.

In plain [terms](jargon_term.md): if the [parameter](jargon_parameter.md) estimates settle down and the target human population moments depend smoothly on the parameter, then [plug-in](jargon_plug_in.md) moments [converge](jargon_convergence.md) as needed.
