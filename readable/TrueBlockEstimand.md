# TrueBlockEstimand.lean

This file defines the "true" block-level score coming from a linear-in-terms model, then shows how the block [standard deviation](jargon_standard_deviation.md) [convergence](jargon_convergence.md) results can be targeted at those true block scores.

Part 1: define the true block score
- A term-level linear model is split into [blocks](jargon_block.md) using a `blk` map from [terms](jargon_term.md) to blocks.
- `trueBlockScore` is the block score induced by `blk`, the true coefficients `beta0`, and the term features `phi`.
- If the model is well-specified, the conjoint causal target equals the sum of these true block scores.

Part 2: connect [sequential consistency](jargon_sequential_consistency.md) to the true block targets
- Theorems `paper_blocks_converge_to_trueBlockSDs_ae` and its specialization show that the block-level [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) results can be stated as [convergence](jargon_convergence.md) to the SD of the true block score.
- The assumptions include block-wise continuity, [convergence](jargon_convergence.md) of [parameter](jargon_parameter.md) estimates, and a block-specification equality at `theta0`.
- The result says: for large enough training index `m`, and for almost all draws (see [almost everywhere](jargon_almost_everywhere.md)), the evaluation [standard deviation](jargon_standard_deviation.md) error becomes small as evaluation size `n` grows, and the target SD equals the true block SD.

In short, the file pins down the "true" block targets and proves that the generic [consistency](jargon_consistency.md) statements can be aimed at those targets.
