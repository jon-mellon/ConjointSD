# Population (vs sample)

Lean entrypoint: [ConjointSD.lean](../ConjointSD.lean)

The population is the real-world set of human units in a specific space and
time that the paper’s final inferences target. We refer to this as the
*target human population*. A sample is the finite data you observe in the
experiment. Population quantities are defined using a target
[distribution](jargon_distribution.md) for the target human population, which
we call the *attribute distribution* (often denoted `ν`). Sample quantities are
computed from the observed data, typically modeled with an *experimental design
distribution* (often denoted `μ`). In the readable documentation, “population”
always refers to the target human population, not to any generic probability
measure.

Back to [jargon index](jargon_index.md).

Back to [Lean docs index](lean_index.md).
