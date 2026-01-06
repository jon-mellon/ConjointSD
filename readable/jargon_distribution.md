# Distribution (also called a measure)

Lean entrypoint: [ConjointSD.lean](../ConjointSD.lean)

A distribution tells you how likely different outcomes are. In this project, the
target human population attribute distribution is denoted `ν_pop`, while the
experimental attribute pushforward is written `kappaDesign := Measure.map (A 0) μexp`
and the evaluation attribute pushforward is written `kappaDesign := Measure.map (A 0) ρ`.

When the distribution is a probability distribution, the total probability of all possible outcomes is 1.

Back to [jargon index](jargon_index.md).

Back to [Lean docs index](lean_index.md).
