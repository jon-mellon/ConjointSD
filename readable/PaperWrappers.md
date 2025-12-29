# PaperWrappers.lean

Lean file: [ConjointSD/PaperWrappers.lean](../ConjointSD/PaperWrappers.lean)

This file provides paper-friendly wrappers around the core technical results. It mostly re-exports theorems with names and hypotheses that match the manuscript.

Section 1: identification
- Wraps the identification results so they read as "[conditional mean](jargon_conditional_mean.md) identifies the potential [mean](jargon_mean.md)" and "difference in [conditional [means](jargon_mean.md)](jargon_conditional_mean.md) identifies the treatment contrast."
- Adds status-conjoint identification wrappers so the concrete survey design can instantiate these results directly.

Section 2: model to [blocks](jargon_block.md)
- Wraps the result that a [well-specified](jargon_well_specified.md) linear model implies the causal score equals the sum of block scores (see [linear model](jargon_linear_model.md) and [block](jargon_block.md)).

Section 3: sequential [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md)
- Provides paper-facing statements that block [standard deviations](jargon_standard_deviation.md) and total standard deviation are sequentially [consistent](jargon_consistency.md) (see [sequential consistency](jargon_sequential_consistency.md) and [consistency](jargon_consistency.md)).
- Uses the "Route 2" [bridge](jargon_bridge.md): [parameter](jargon_parameter.md) [convergence](jargon_convergence.md) plus [continuity](jargon_continuity.md) implies the [plug-in](jargon_plug_in.md) moment assumptions.
- Includes bounded variants.
- Adds `hGTotal`-based wrappers so the total-score sequential consistency chain can be driven directly by `GEstimationAssumptions`.

Section 4: targeting the true estimand
- Adds a separate assumption that the model score equals the true target [almost everywhere](jargon_almost_everywhere.md), then concludes the [population](jargon_population.md) [standard deviations](jargon_standard_deviation.md) are equal.
- Provides an approximate version where the scores are within epsilon, giving an explicit [standard deviation](jargon_standard_deviation.md) error bound.

Section 4c: link to the causal estimand
- If the total model score at `theta0` matches a linear [term](jargon_term.md) model and that model is [well-specified](jargon_well_specified.md) for `gStar`, then the [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) targets `gStar`.
- Adds an approximate counterpart: if the model is only approximately [well-specified](jargon_well_specified.md) ν-a.e., the total-score [standard deviation](jargon_standard_deviation.md) target is within an explicit bound of the `gStar` target.
- Adds a two-stage approximation version: a flexible oracle score approximates `gStar`, and the model approximates that oracle, with the combined error driving the [standard deviation](jargon_standard_deviation.md) bound.
- Provides an `hGTotal` variant of the `gStar` bridge so OLS-style `GEstimationAssumptions` can drive the same conclusion.

Section 4d: no-[interactions](jargon_interaction.md) corollary
- Uses the "no [interactions](jargon_interaction.md)" assumption to produce [well-specification](jargon_well_specified.md) automatically and then applies the same [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) [bridge](jargon_bridge.md).

In short, this file is the narrative layer: it collects the pieces into statements that match the paper's wording and flow.
