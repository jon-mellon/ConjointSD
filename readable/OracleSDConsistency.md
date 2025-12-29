# OracleSDConsistency.lean

This file restates the [standard deviation](jargon_standard_deviation.md) [convergence](jargon_convergence.md) result so the limit is written in terms of the attribute [distribution](jargon_distribution.md) `nu`.

What it does:
- Starts from the existing result: the empirical [standard deviation](jargon_standard_deviation.md) of `g(A i)` [converges](jargon_convergence.md) to `popSDZ` on the big probability space.
- Uses the PopulationBridge result to rewrite `popSDZ` as `popSDAttr nu g` when `A 0` has [distribution](jargon_distribution.md) `nu`.

Main theorem:
- `sd_component_consistent_to_popSDAttr` says the empirical [standard deviation](jargon_standard_deviation.md) [converges](jargon_convergence.md) to the population SD under `nu` for a fixed score function `g`.

This is a notational bridge: it lets later statements talk directly about the paper's population target.
