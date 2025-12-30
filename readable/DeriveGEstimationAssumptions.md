# DeriveGEstimationAssumptions.lean

Lean file: [ConjointSD/DeriveGEstimationAssumptions.lean](../ConjointSD/DeriveGEstimationAssumptions.lean)

This file gives a short route from "the [parameter](jargon_parameter.md) estimates [converge](jargon_convergence.md)" to the assumptions used later about [plug-in](jargon_plug_in.md) moments. It now packages the convergence premise as `ThetaTendstoAssumptions`.

What it does:
- Assumes a parameter sequence `theta_hat` [converges](jargon_convergence.md) to a true value `theta0` (see [convergence](jargon_convergence.md) and [parameter](jargon_parameter.md)).
- Assumes the [population](jargon_population.md) [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) as functions of the [parameter](jargon_parameter.md) are [continuous](jargon_continuity.md) at `theta0`.
- Concludes the bundled `GEstimationAssumptions` needed for [plug-in](jargon_plug_in.md) [consistency](jargon_consistency.md).

Key steps:
- `derive_hG` takes a single score function `g` and returns the `GEstimationAssumptions` package.
- `derive_hG_blocks` does the same for a family of block scores, giving the assumption for each [block](jargon_block.md).

In short, the file is a thin wrapper: it reuses the more general [bridge](jargon_bridge.md) theorem and specializes it to the paper-friendly form.
