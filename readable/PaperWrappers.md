# PaperWrappers.lean

Lean file: [ConjointSD/PaperWrappers.lean](../ConjointSD/PaperWrappers.lean)

This file provides paper-friendly wrappers around the core technical results. It mostly re-exports theorems with names and hypotheses that match the manuscript. The wrapper statements use the standard probability/convergence bundles and target attribute moments under `ν`, with `EvalWeightMatchesAttrMoments` encoding the weighted evaluation-to-population moment match needed for SD targets. Where causal scores (`gStar`, `gPot`, `gExp`) appear, they are tied to the experimental law `μexp`, separating experimental identification from population evaluation.

Section 1: identification
- Wraps the identification results so they read as "[conditional mean](jargon_conditional_mean.md) identifies the potential [mean](jargon_mean.md)" and "difference in [conditional [means](jargon_mean.md)](jargon_conditional_mean.md) identifies the treatment contrast," now with an explicit positivity assumption on the conditioning events.
- Adds status-conjoint identification wrappers and derives positivity from the single-shot design before applying the generic identification results.

Section 2: model to [blocks](jargon_block.md)
- Wraps the result that a [well-specified](jargon_well_specified.md) linear model implies the causal score equals the sum of block scores (see [linear model](jargon_linear_model.md) and [block](jargon_block.md)).

Section 3: sequential [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md)
- Provides paper-facing statements that block [standard deviations](jargon_standard_deviation.md) and total standard deviation are sequentially [consistent](jargon_consistency.md) (see [sequential consistency](jargon_sequential_consistency.md) and [consistency](jargon_consistency.md)).
- Uses the "Route 2" [bridge](jargon_bridge.md): [parameter](jargon_parameter.md) [convergence](jargon_convergence.md) plus [continuity](jargon_continuity.md) implies plug‑in moment convergence.
- Includes bounded variants.
- Adds total-score wrappers that take raw `Tendsto` + continuity hypotheses instead of a bundled plug‑in assumption.
- Adds [OLS](jargon_ols.md)-based wrappers that plug the paper OLS assumptions into the total-only and blocks+total sequential [consistency](jargon_consistency.md) results.
- Adds a design-based OLS wrapper (`paper_sd_total_sequential_consistency_ae_of_paper_ols_design_total_ae`) that derives the plug-in moment assumptions and functional continuity a.e. from `PaperOLSDesignAssumptions`, inverse-Gram stability, and identification.

Section 4: targeting the true [estimand](jargon_estimand.md)
- Adds a separate assumption that the model score equals the true target [almost everywhere](jargon_almost_everywhere.md), then concludes the target human [population](jargon_population.md) [standard deviations](jargon_standard_deviation.md) are equal.
- Provides an approximate version where the scores are within epsilon, giving an explicit [standard deviation](jargon_standard_deviation.md) error bound.
- Adds an identification bridge: if the model score targets the observed score and the observed score equals the causal score, then the SD target is the causal one (using [potential outcomes](jargon_potential_outcome.md) and [conditional means](jargon_conditional_mean.md)).

Section 4c: link to the causal [estimand](jargon_estimand.md)
- If the total model score at `theta0` matches a linear [term](jargon_term.md) model and that model is [well-specified](jargon_well_specified.md) for `gStar`, then the [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) targets the `gStar` SD.
- Adds an approximate counterpart: if the model is only approximately [well-specified](jargon_well_specified.md) ν-a.e., the total-score [standard deviation](jargon_standard_deviation.md) target is within an explicit bound of the `gStar` target.
- Adds a two-stage approximation version: a flexible oracle score approximates `gStar`, and the model approximates that oracle, with the combined error driving the [standard deviation](jargon_standard_deviation.md) bound to the `gStar` target.
- Provides a `gStar` bridge variant that takes raw `Tendsto` + continuity hypotheses so the OLS path can drive the same conclusion.

Section 4d: no-[interactions](jargon_interaction.md) corollary
- Uses the "no [interactions](jargon_interaction.md)" assumption to produce [well-specification](jargon_well_specified.md) automatically and then applies the same [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) [bridge](jargon_bridge.md).

In short, this file is the narrative layer: it collects the pieces into statements that match the paper's wording and flow.
