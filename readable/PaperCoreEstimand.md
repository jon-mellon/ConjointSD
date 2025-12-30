# PaperCoreEstimand.lean

Lean file: [ConjointSD/PaperCoreEstimand.lean](../ConjointSD/PaperCoreEstimand.lean)

This file defines the paper's core [standard deviation](jargon_standard_deviation.md) targets and links them to the main [estimator](jargon_estimator.md). It now takes the bundled assumption records (`ProbMeasureAssumptions`, `MapLawAssumptions`, `ThetaTendstoAssumptions`, `EpsilonAssumptions`) instead of standalone hypotheses.

Part 1: core targets
- `paperTrueBlockScore` and `paperTrueTotalScore` are the true [block](jargon_block.md) and total scores induced by the [term](jargon_term.md) model.
- `paperBlockSD` and `paperTotalSD` are the [population](jargon_population.md) [standard deviation](jargon_standard_deviation.md) targets for those scores.
- `paperBlockSDs` collects block [standard deviation](jargon_standard_deviation.md) targets into a function over [blocks](jargon_block.md).
- `paperBlockSD_weighted`, `paperTotalSD_weighted`, and `paperBlockSDs_weighted` define survey-weighted population SD targets using `weightSDAttr` from [SurveyWeights](SurveyWeights.md).
- `paperBlockSD_weighted_eq_pop`, `paperTotalSD_weighted_eq_pop`, and `paperBlockSDs_weighted_eq_pop` state that if the survey weights match the population moments, the weighted targets equal the population SD targets.

Part 2: the main estimator
- `paperTotalSDEst` is the evaluation-stage [standard deviation](jargon_standard_deviation.md) estimator for the total score induced by the term model.
- `paper_total_sd_estimator_consistency_ae_of_gBTerm` proves the estimator is [sequentially [consistent](jargon_consistency.md)](jargon_sequential_consistency.md) for the paper's total [standard deviation](jargon_standard_deviation.md) target, assuming coefficient identification and [continuity](jargon_continuity.md).

Part 3: [bridge](jargon_bridge.md) to the causal target
- `gTotalTheta_eq_gTotal_gBTerm` shows how the total score at `theta0` matches the term-based total score.
- `paper_sd_total_sequential_consistency_to_gStar_ae_of_gBTerm` then targets the causal score `gStar` when the term model is [well-specified](jargon_well_specified.md).

Overall, this file packages the paper's target quantities and shows the main estimator [converges](jargon_convergence.md) to them under the stated assumptions.
