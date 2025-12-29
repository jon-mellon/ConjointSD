# TermModelBlocks.lean

Lean file: [ConjointSD/TermModelBlocks.lean](../ConjointSD/TermModelBlocks.lean)

This file defines how a term-level [linear model](jargon_linear_model.md) induces a block-level score model.

Key definition:
- `gBTerm` takes a mapping from [terms](jargon_term.md) to [blocks](jargon_block.md) and a coefficient function `betaOf`. For each block, it sums the terms assigned to that block (see [term](jargon_term.md) and [block](jargon_block.md)).

Key theorem:
- `gBTerm_blockSpec` says that if the estimated coefficients at `theta0` equal the true coefficients, then the block score induced by `gBTerm` at `theta0` equals the "true" block score.

This is a small but important link used later to replace a model-based block score with a true block target under coefficient identification.
