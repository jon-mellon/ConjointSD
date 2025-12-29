# ModelBridge.lean

This file connects linear [term](jargon_term.md) models to [block](jargon_block.md) scores and to the conjoint causal target.

Core linear model pieces:
- `gLin` defines a [linear model](jargon_linear_model.md) as a sum over [terms](jargon_term.md).
- `gBlockTerm` groups [terms](jargon_term.md) into [blocks](jargon_block.md) using a block assignment function.
- `gLin_eq_gTotal_blocks` proves that summing block scores recovers the original linear score.

Causal target pieces:
- `gStar` is the causal score function: the [mean](jargon_mean.md) [potential outcome](jargon_potential_outcome.md) under each [profile](jargon_profile.md).
- `WellSpecified` says the causal target equals a linear model.
- `ApproxWellSpecified` and `ApproxWellSpecifiedAE` are exact and almost-everywhere approximation versions.
- The theorems show that (approximate) [well-specification](jargon_well_specified.md) implies (approximate) equality with the block-sum score.

Paper term set:
- `PaperTerm`, `betaPaper`, and `phiPaper` encode the intercept + main effects + [interactions](jargon_interaction.md) term set.
- `ParametricMainInteractions` is the paper's parametric assumption written as an equality for `gStar`.
- `wellSpecified_of_parametricMainInteractions` shows this parametric equality implies `WellSpecified`.
- `gStar_eq_sum_blocks_of_parametricMainInteractions` then gives the block decomposition for the paper term set.

This file is the main algebraic [bridge](jargon_bridge.md) from "linear model for the causal target" to "sum of block scores."
