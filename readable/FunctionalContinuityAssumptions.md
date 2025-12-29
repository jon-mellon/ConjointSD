# FunctionalContinuityAssumptions.lean

This file turns [continuity](jargon_continuity.md) of [population](jargon_population.md) functionals into [convergence](jargon_convergence.md) of [plug-in](jargon_plug_in.md) population quantities.

What it assumes:
- A score function `g` depends on a [parameter](jargon_parameter.md) `theta`.
- The population [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) as functions of `theta` are [continuous](jargon_continuity.md) at `theta0`.

What it proves:
- `meanContinuousAt_of_FunctionalContinuityAssumptions` and `m2ContinuousAt_of_FunctionalContinuityAssumptions` extract [continuity](jargon_continuity.md) of the [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) from the bundled assumptions.
- If `theta_hat` [converges](jargon_convergence.md) to `theta0`, then the [plug-in](jargon_plug_in.md) [mean](jargon_mean.md) converges to the true mean.
- The same holds for the second moment, then for [variance](jargon_variance.md) (as a combination), and finally for [standard deviation](jargon_standard_deviation.md).

The key idea is simple: [continuity](jargon_continuity.md) plus [convergence](jargon_convergence.md) of [parameters](jargon_parameter.md) gives convergence of the population functionals.
