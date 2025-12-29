# RegressionConsistencyBridge.lean

This file bridges [parameter](jargon_parameter.md) [convergence](jargon_convergence.md) to plug-in moment convergence.

Key definitions:
- `popMeanTheta` and `popM2Theta` treat the population [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) as functions of the [parameter](jargon_parameter.md).
- `FunctionalContinuityAssumptions` says those functions are continuous at the true [parameter](jargon_parameter.md).

Main theorem:
- If `theta_hat` [converges](jargon_convergence.md) to `theta0`, and the population [mean](jargon_mean.md) / [second moment](jargon_second_moment.md) are continuous at `theta0`, then `GEstimationAssumptions` holds. This is the package used by later files.

Additional results:
- A [variance](jargon_variance.md) [convergence](jargon_convergence.md) lemma is derived from [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) convergence.
- For block models, `BlockFunctionalContinuityAssumptions` and a block version of the bridge are provided.

In plain terms: if the [parameter](jargon_parameter.md) estimates settle down and the population moments depend smoothly on the parameter, then plug-in moments [converge](jargon_convergence.md) as needed.
