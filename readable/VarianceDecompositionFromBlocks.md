# VarianceDecompositionFromBlocks.lean

This file proves a [variance](jargon_variance.md) decomposition for a sum of [block](jargon_block.md) scores.

Key definitions:
- `gTotal`: sums all [block](jargon_block.md) scores to get the total score.
- `covRaw`: a raw [covariance](jargon_covariance.md) formula `E[XY] - E[X]E[Y]`.
- `varProxy`: a [variance](jargon_variance.md) formula `E[X^2] - (E[X])^2`.
- `BlockIntegrable`: the [integrable](jargon_integrable.md) conditions needed so all these averages exist.

Main theorem:
- `varProxy_sum_eq_sum_covRaw` shows that the [variance](jargon_variance.md) proxy of the total score equals the double sum of [covariances](jargon_covariance.md) across all pairs of [blocks](jargon_block.md).

How the proof works:
- It rewrites the total score as a finite sum (using [finite type](jargon_finite_type.md)).
- It expands the square of that sum into a double sum.
- It turns [integrals](jargon_integral.md) of sums into sums of integrals.
- It arranges [terms](jargon_term.md) to match the covariance formula.

The result is the familiar [variance](jargon_variance.md) decomposition: variance of a sum equals the sum of all pairwise covariances.
