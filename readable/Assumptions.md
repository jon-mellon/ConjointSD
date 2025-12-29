# Assumptions.lean

Lean file: [ConjointSD/Assumptions.lean](../ConjointSD/Assumptions.lean)

This file gathers all assumption bundles and assumption-level props in a single place
for auditability.

Coverage includes:
- Transport/overlap/invariance assumptions for [population](jargon_population.md) targets.
- [IID](jargon_iid.md) and score/moment assumptions for SD consistency.
- [Regression](jargon_regression.md)/continuity bridges and [OLS](jargon_ols.md) consistency/moment assumptions.
- Conjoint identification and randomized-design assumptions.
- Weighted-moment and [block](jargon_block.md)-integrability assumptions.
- Paper-specific [OLS](jargon_ols.md) LLN/identifiability packages.
- Well-specification and no-[interactions](jargon_interaction.md) assumptions.

The file depends on shared definitions in `ConjointSD/Defs.lean`.
