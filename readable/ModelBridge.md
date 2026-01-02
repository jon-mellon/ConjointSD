# ModelBridge.lean

Lean file: [ConjointSD/ModelBridge.lean](../ConjointSD/ModelBridge.lean)

This file connects linear [term](jargon_term.md) models to [block](jargon_block.md) scores and to the conjoint causal target.

Core linear model pieces:
- `gLin` (defined in `ConjointSD/Defs.lean`) defines a [linear model](jargon_linear_model.md) as a sum over [terms](jargon_term.md).
- `gBlockTerm` groups [terms](jargon_term.md) into [blocks](jargon_block.md) using a block assignment function.
- `gLin_eq_gTotal_blocks` proves that summing block scores recovers the original linear score.

Causal target pieces:
- `gStar` (defined in `ConjointSD/Defs.lean`) is the causal score function: the [mean](jargon_mean.md) [potential outcome](jargon_potential_outcome.md) under each [profile](jargon_profile.md).
- `WellSpecified` and approximation variants are defined in `ConjointSD/ModelBridge.lean`.
- The theorems show that [well-specification](jargon_well_specified.md) yields equality with the block-sum score, and the AE approximation variant yields a.e. closeness to the block-sum score.

This file is the main algebraic [bridge](jargon_bridge.md) from "linear model for the causal target" to "sum of block scores."
