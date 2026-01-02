# TrueBlockEstimand.lean

Lean file: [ConjointSD/TrueBlockEstimand.lean](../ConjointSD/TrueBlockEstimand.lean)

This file defines the "true" [block](jargon_block.md)-level score coming from a [linear-in-terms](jargon_linear_in_terms.md) model.

Part 1: define the true block score
- A [term](jargon_term.md)-level [linear model](jargon_linear_model.md) is split into [blocks](jargon_block.md) using a `blk` map from [terms](jargon_term.md) to blocks.
- `trueBlockScore` is the block score induced by `blk`, the true coefficients `beta0`, and the term features `phi`.
