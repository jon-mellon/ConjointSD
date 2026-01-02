# DecompositionSequentialConsistency.lean

Lean file: [ConjointSD/DecompositionSequentialConsistency.lean](../ConjointSD/DecompositionSequentialConsistency.lean)

This file lifts the [sequential [consistency](jargon_consistency.md)](jargon_sequential_consistency.md) results to a [block](jargon_block.md) decomposition and to the total score. It uses the standard probability/convergence bundles and evaluates targets under the target attribute distribution `ν`, with `EvalWeightMatchesPopMoments` providing the weighted evaluation-to-population moment match needed for the SD targets.

Key definitions:
- `gBlock` is the block score as a function of the [parameter](jargon_parameter.md).
- `gTotalTheta` sums [block](jargon_block.md) scores across all [blocks](jargon_block.md) to get the total score.

Main results:
- `sequential_consistency_blocks_ae` shows that for a finite set of [blocks](jargon_block.md), there is a single `M` such that all [block](jargon_block.md) [standard deviation](jargon_standard_deviation.md) errors are eventually small (see [sequential consistency](jargon_sequential_consistency.md)).
- `sequential_consistency_total_ae` gives the same for the total score.
- Bounded versions turn boundedness assumptions into the needed evaluation assumptions; these now use `EvalAttrIID` for the evaluation sample (separate from any design-side IID).

The file mainly combines the single-score [sequential consistency](jargon_sequential_consistency.md) result with a finite-union argument over [blocks](jargon_block.md).
