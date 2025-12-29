# ConjointIdentification.lean

Lean file: [ConjointSD/ConjointIdentification.lean](../ConjointSD/ConjointIdentification.lean)

This file formalizes identification in a conjoint experiment: observed [conditional means](jargon_conditional_mean.md) recover causal [potential outcomes](jargon_potential_outcome.md) on average.

Core definitions:
- `eventX x`: the set of units whose assigned [profile](jargon_profile.md) equals `x`.
- `condMean`: the [conditional mean](jargon_conditional_mean.md) of a variable on an event.
- `potMean`: the [mean](jargon_mean.md) of a [potential outcome](jargon_potential_outcome.md) under profile `x`.
- `amce`: the difference in potential [means](jargon_mean.md) between two [profiles](jargon_profile.md).

Assumption bundles:
- `ConjointIdAssumptions` collects [measurability](jargon_measurable.md), a condition that observed outcomes equal the potential outcomes for the assigned profile, positivity of assignment, and a factorization that expresses random assignment.
- `ConjointIdRandomized` is a stronger, more explicit random-assignment package using [independence](jargon_independent.md).
- `ConjointSingleShotDesign` describes the one-shot conjoint design with a specified assignment [distribution](jargon_distribution.md), bounded outcomes, and [independence](jargon_independent.md).

Main logical steps:
1) Show that `ConjointIdRandomized` implies the factorization used in `ConjointIdAssumptions`.
2) Use that factorization to prove that the [conditional mean](jargon_conditional_mean.md) among `X = x0` equals the potential [mean](jargon_mean.md) for `x0`.
3) Use the observed-equals-potential condition to replace `Yobs` with `Y x0` inside the [conditional mean](jargon_conditional_mean.md).
4) Combine the above to identify `amce` as a difference of observed [conditional means](jargon_conditional_mean.md).

Final result:
- The file defines `gExp` (the observed [conditional mean](jargon_conditional_mean.md) score) and `gPot` (the causal score), and proves they are equal under the assumptions.

In plain [terms](jargon_term.md): under random assignment and basic regularity conditions, the observed conditional averages identify the causal target function.
