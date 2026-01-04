# ApproxModelBridge.lean

Lean file: [ConjointSD/ApproxModelBridge.lean](../ConjointSD/ApproxModelBridge.lean)

This file collects approximation variants of the model-bridge definitions and lemmas.

What it defines:
- `ApproxWellSpecified`: uniform (pointwise) ε-approximation of `gStar` by the linear model.
- `ApproxWellSpecifiedAE`: ν-a.e. ε-approximation of `gStar` by the linear model.

Approximation bridge:
- `gStar_approx_sum_blocks_of_ApproxWellSpecifiedAE`: the ν-a.e. approximation transfers from the linear score to the induced block-sum score.
