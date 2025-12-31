# PaperCoreEstimand.lean

Lean file: [ConjointSD/PaperCoreEstimand.lean](../ConjointSD/PaperCoreEstimand.lean)

This file defines the paper's core [standard deviation](jargon_standard_deviation.md) targets and links them to the main [estimator](jargon_estimator.md). The consistency wrappers target the attribute distribution `ν` and use `EvalWeightMatchesAttrMoments` to relate weighted evaluation draws under the evaluation law `μ` to the target population moments. Causal scores (`gStar`) are tied to the experimental law `μexp`, matching the paper’s “fit on experiment, evaluate on population” pipeline.

Part 1: core targets
- `paperTrueBlockScore` and `paperTrueTotalScore` are the true [block](jargon_block.md) and total scores induced by the [term](jargon_term.md) model.
- `paperBlockSD` and `paperTotalSD` are the target human [population](jargon_population.md) [standard deviation](jargon_standard_deviation.md) targets for those scores (under the attribute distribution).
- `paperBlockSDs` collects block [standard deviation](jargon_standard_deviation.md) targets into a function over [blocks](jargon_block.md).
- The targets are unweighted [population](jargon_population.md) SDs under `ν`.

Part 2: the main estimator
- `paperTotalSDEst` is the weighted evaluation-stage [standard deviation](jargon_standard_deviation.md) estimator for the total score induced by the term model.
- `paper_total_sd_estimator_consistency_ae_of_gBTerm` proves the estimator is [sequentially [consistent](jargon_consistency.md)](jargon_sequential_consistency.md) for the paper's total [standard deviation](jargon_standard_deviation.md) target, assuming coefficient identification and [continuity](jargon_continuity.md).

Part 3: [bridge](jargon_bridge.md) to the causal target
- `gTotalTheta_eq_gTotal_gBTerm` shows how the total score at `theta0` matches the term-based total score.
- `paper_sd_total_sequential_consistency_to_gStar_ae_of_gBTerm` then targets the causal score `gStar` when the term model is [well-specified](jargon_well_specified.md).

Overall, this file packages the paper's target quantities and shows the main estimator [converges](jargon_convergence.md) to them under the stated assumptions.
