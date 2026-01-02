# ConjointIdentification.lean

Lean file: [ConjointSD/ConjointIdentification.lean](../ConjointSD/ConjointIdentification.lean)

This file formalizes identification in a conjoint experiment: observed [conditional means](jargon_conditional_mean.md) recover causal [potential outcomes](jargon_potential_outcome.md) on average. It now takes `ProbMeasureAssumptions` in place of standalone probability-measure hypotheses.

Core definitions:
- `eventX x`: the set of units whose assigned [profile](jargon_profile.md) equals `x`.
- `condMean`: the [conditional mean](jargon_conditional_mean.md) of a variable on an event.
- `potMean`: the [mean](jargon_mean.md) of a [potential outcome](jargon_potential_outcome.md) under profile `x`.
- `amce`: the difference in potential [means](jargon_mean.md) between two [profiles](jargon_profile.md) ([AMCE](jargon_amce.md)).

Assumption bundle (defined in `ConjointSD/Assumptions.lean`):
- `ConjointIdRandomized` is the explicit random-assignment package used here, combining [measurability](jargon_measurable.md), consistency, bounded outcomes, and [independence](jargon_independent.md) between `X` and each potential outcome `Y x`.

Main logical steps:
1) Use `ConjointIdRandomized` to derive the key factorization for conditional means.
2) Use that factorization to show the [conditional mean](jargon_conditional_mean.md) among `X = x0` equals the potential [mean](jargon_mean.md) for `x0`.
3) Use consistency to replace `Yobs` with `Y x0` inside the conditional mean.
4) Combine the above to identify `amce` as a difference of observed [conditional means](jargon_conditional_mean.md).
Final result:
- The file defines `gExp` (the observed [conditional mean](jargon_conditional_mean.md) score) and `gPot` (the causal score) for use in identification statements.

In plain [terms](jargon_term.md): under random assignment and basic regularity conditions, the observed conditional averages identify the causal target function (given a separate positivity assumption for the conditioning events).

Bridge note: identification results in this file take `ConjointIdRandomized` directly; stream-level SD consistency uses separate attribute-stream assumptions.

Note: attribute-level AMCE identification and estimation assumptions (e.g., conditional or componentwise randomization) are not formalized here; we defer to Hainmueller–Hopkins–Yamamoto for those results.

Recent changes: drop explicit integrability assumptions for potential outcomes; boundedness plus `ProbMeasureAssumptions` now supplies integrability when needed.
