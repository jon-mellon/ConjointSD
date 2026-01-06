# PaperCoreEstimand.lean

Lean file: [ConjointSD/PaperCoreEstimand.lean](../ConjointSD/PaperCoreEstimand.lean)

This file defines the paper's core [standard deviation](jargon_standard_deviation.md) targets as
pure [population](jargon_population.md) quantities under the attribute distribution `ν_pop` and links
them to the main [estimator](jargon_estimator.md). The consistency wrappers use
`EvalAttrLawEqPop` to relate evaluation draws under the evaluation law `ρ` to the target
population law. Causal scores (`gStar`) are tied to the experimental law `μexp`, matching the
paper’s “fit on experiment, evaluate on population” pipeline.

Part 1: core targets
- `paperTrueBlockScore` and `paperTrueTotalScore` are the true [block](jargon_block.md) and total scores induced by the [term](jargon_term.md) model.
- `paperBlockSD` and `paperTotalSD` are the target human [population](jargon_population.md)
  [standard deviation](jargon_standard_deviation.md) targets for those scores (under `ν_pop`), and
  are defined without any sampling assumptions.
- `paperBlockSDs` collects block [standard deviation](jargon_standard_deviation.md) targets into a function over [blocks](jargon_block.md).
- The targets are unweighted [population](jargon_population.md) SDs under `ν_pop`.

Part 2: the main estimator

Part 3: [bridge](jargon_bridge.md) to the causal target

Overall, this file packages the paper's target quantities and shows the main estimator [converges](jargon_convergence.md) to them under the stated assumptions.
