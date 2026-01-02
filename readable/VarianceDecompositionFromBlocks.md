# VarianceDecompositionFromBlocks.lean

Lean file: [ConjointSD/VarianceDecompositionFromBlocks.lean](../ConjointSD/VarianceDecompositionFromBlocks.lean)

This file proves a [variance](jargon_variance.md) decomposition for a sum of [block](jargon_block.md) scores.

Key definitions:
- `gTotal`: sums all [block](jargon_block.md) scores to get the total score.
- `covRaw`: a raw [covariance](jargon_covariance.md) formula `E[XY] - E[X]E[Y]`.
- `varProxy`: a [variance](jargon_variance.md) formula `E[X^2] - (E[X])^2`.
- `BlockIntegrable`: the [integrable](jargon_integrable.md) conditions needed so all these averages exist.

This file currently provides the core definitions and integrability bundle for variance decompositions, but no top-level theorem is exposed.
