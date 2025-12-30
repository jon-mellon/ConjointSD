# ConjointIdentification.lean

Lean file: [ConjointSD/ConjointIdentification.lean](../ConjointSD/ConjointIdentification.lean)

This file formalizes identification in a conjoint experiment: observed [conditional means](jargon_conditional_mean.md) recover causal [potential outcomes](jargon_potential_outcome.md) on average. It now takes `ProbMeasureAssumptions` in place of standalone probability-measure hypotheses.

Core definitions:
- `eventX x`: the set of units whose assigned [profile](jargon_profile.md) equals `x`.
- `condMean`: the [conditional mean](jargon_conditional_mean.md) of a variable on an event.
- `potMean`: the [mean](jargon_mean.md) of a [potential outcome](jargon_potential_outcome.md) under profile `x`.
- `amce`: the difference in potential [means](jargon_mean.md) between two [profiles](jargon_profile.md) ([AMCE](jargon_amce.md)).

Assumption bundles (defined in `ConjointSD/Assumptions.lean`):
- `ConjointIdAssumptions` collects [measurability](jargon_measurable.md), a condition that observed outcomes equal the potential outcomes for the assigned profile, and a factorization that expresses random assignment.
- `ConjointIdRandomized` is a stronger, more explicit random-assignment package using [independence](jargon_independent.md) plus bounded outcomes; integrability is derived from boundedness under a probability measure.
- `ConjointRandomizationMechanism` models the assignment as a function of a randomization variable that is [independent](jargon_independent.md) of every [potential outcome](jargon_potential_outcome.md).
- `ConjointSingleShotDesign` describes the one-shot conjoint design with a specified assignment [distribution](jargon_distribution.md), an explicit randomization mechanism, and bounded outcomes.

Main logical steps:
1) Show that `ConjointIdRandomized` implies the factorization used in `ConjointIdAssumptions`.
1a) Derive ignorability of `X` from the randomization mechanism in `ConjointSingleShotDesign`.
2) Use that factorization to prove that the [conditional mean](jargon_conditional_mean.md) among `X = x0` equals the potential [mean](jargon_mean.md) for `x0`.
3) Use the observed-equals-potential condition to replace `Yobs` with `Y x0` inside the [conditional mean](jargon_conditional_mean.md).
4) Combine the above to identify `amce` as a difference of observed [conditional means](jargon_conditional_mean.md).
5) If task outcomes are order-invariant, a short bridge lemma shows the potential mean
   is invariant under profile-order permutations.

Final result:
- The file defines `gExp` (the observed [conditional mean](jargon_conditional_mean.md) score) and `gPot` (the causal score), and proves they are equal under the assumptions.

In plain [terms](jargon_term.md): under random assignment and basic regularity conditions, the observed conditional averages identify the causal target function (given a separate positivity assumption for the conditioning events).

Note: attribute-level AMCE identification and estimation assumptions (e.g., conditional or componentwise randomization) are not formalized here; we defer to Hainmueller–Hopkins–Yamamoto for those results.

Recent changes: drop explicit integrability assumptions for potential outcomes; boundedness plus `ProbMeasureAssumptions` now supplies integrability when needed.
