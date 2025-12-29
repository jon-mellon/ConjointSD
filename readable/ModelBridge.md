# ModelBridge.lean

Lean file: [ConjointSD/ModelBridge.lean](../ConjointSD/ModelBridge.lean)

This file connects linear [term](jargon_term.md) models to [block](jargon_block.md) scores and to the conjoint causal target.

Core linear model pieces:
- `gLin` (defined in `ConjointSD/Defs.lean`) defines a [linear model](jargon_linear_model.md) as a sum over [terms](jargon_term.md).
- `gBlockTerm` groups [terms](jargon_term.md) into [blocks](jargon_block.md) using a block assignment function.
- `gLin_eq_gTotal_blocks` proves that summing block scores recovers the original linear score.

Causal target pieces:
- `gStar` (defined in `ConjointSD/Defs.lean`) is the causal score function: the [mean](jargon_mean.md) [potential outcome](jargon_potential_outcome.md) under each [profile](jargon_profile.md).
- `WellSpecified` and approximation variants live in `ConjointSD/Assumptions.lean`.
- The theorems show that (approximate) [well-specification](jargon_well_specified.md) implies (approximate) equality with the block-sum score.

Paper term set:
- `PaperTerm`, `betaPaper`, and `phiPaper` (from `ConjointSD/Defs.lean`) encode the intercept + main effects + [interactions](jargon_interaction.md) term set.
- `ParametricMainInteractions` (in `ConjointSD/Assumptions.lean`) is the paper's parametric assumption written as an equality for `gStar`.
- `wellSpecified_of_parametricMainInteractions` shows this parametric equality implies `WellSpecified`.
- `gStar_eq_sum_blocks_of_parametricMainInteractions` then gives the block decomposition for the paper term set.

This file is the main algebraic [bridge](jargon_bridge.md) from "linear model for the causal target" to "sum of block scores."
