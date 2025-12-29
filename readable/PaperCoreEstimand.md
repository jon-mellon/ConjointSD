# PaperCoreEstimand.lean

This file defines the paper's core [standard deviation](jargon_standard_deviation.md) targets and links them to the main estimator.

Part 1: core targets
- `paperTrueBlockScore` and `paperTrueTotalScore` are the true block and total scores induced by the term model.
- `paperBlockSD` and `paperTotalSD` are the population [standard deviation](jargon_standard_deviation.md) targets for those scores.
- `paperBlockSDs` collects block [standard deviation](jargon_standard_deviation.md) targets into a function over blocks.

Part 2: the main estimator
- `paperTotalSDEst` is the evaluation-stage [standard deviation](jargon_standard_deviation.md) estimator for the total score induced by the term model.
- `paper_total_sd_estimator_consistency_ae_of_gBTerm` proves the estimator is [sequentially consistent](jargon_sequential_consistency.md) for the paper's total [standard deviation](jargon_standard_deviation.md) target, assuming coefficient identification and continuity.

Part 3: bridge to the causal target
- `gTotalTheta_eq_gTotal_gBTerm` shows how the total score at `theta0` matches the term-based total score.
- `paper_sd_total_sequential_consistency_to_gStar_ae_of_gBTerm` then targets the causal score `gStar` when the term model is well-specified.

Overall, this file packages the paper's target quantities and shows the main estimator [converges](jargon_convergence.md) to them under the stated assumptions.
