# DeriveGEstimationAssumptions.lean

Lean file: [ConjointSD/DeriveGEstimationAssumptions.lean](../ConjointSD/DeriveGEstimationAssumptions.lean)

This file gives a short route from "the [parameter](jargon_parameter.md) estimates [converge](jargon_convergence.md)" to plug‑in moment convergence using raw `Tendsto` hypotheses, without assuming a separate `GEstimationAssumptions` bundle.

What it does:
- Assumes a parameter sequence `theta_hat` [converges](jargon_convergence.md) to a true value `theta0` (see [convergence](jargon_convergence.md) and [parameter](jargon_parameter.md)).
- Assumes the target human [population](jargon_population.md) [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) (under the attribute distribution) as functions of the [parameter](jargon_parameter.md) are [continuous](jargon_continuity.md) at `theta0`.
- Concludes plug‑in [mean](jargon_mean.md) and [second moment](jargon_second_moment.md) convergence needed for [plug-in](jargon_plug_in.md) [consistency](jargon_consistency.md).

Key steps:
- `derive_mean_tendsto` and `derive_m2_tendsto` give plug‑in mean/second‑moment convergence for a single score.
- `derive_mean_tendsto_blocks` and `derive_m2_tendsto_blocks` do the same for block scores.

In short, the file is a thin wrapper: it reuses the more general [bridge](jargon_bridge.md) theorem and specializes it to the paper-friendly form.
