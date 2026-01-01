# Core idea

This project’s core idea is a simple two-stage argument about identifying and
transporting social status variation.

1) **Conjoint identification of a status-assigning function.**
- A randomized conjoint experiment assigns independent attribute bundles and
  elicits bounded status judgments (0–100).
- The experiment identifies the average status-assigning rule in the design via
  randomized assignment and standard identification logic.
- An external-validity assumption (ν-a.e. equality of score functions) is
  required later to transport the experimental score to target-population
  moments; it is not part of within-design identification.
- The model is well specified: all relevant attributes are included and there
  are no meaningful [interaction](readable/jargon_interaction.md) effects, so a
  linear-in-terms model recovers the true rule.

2) **Transport to the population distribution.**
- A separate evaluation sample is reweighted to match the target
  [population](readable/jargon_population.md)
  [distribution](readable/jargon_distribution.md) of attributes.
- Weighted sample moments converge to the true
  [population](readable/jargon_population.md) moments.
- Applying the estimated status-assigning rule to this weighted population
  sample yields a predicted status distribution whose
  [standard deviation](readable/jargon_standard_deviation.md) converges to the
  population SD.

Under these assumptions, the estimated model converges to the true status
assignment function, and the predicted population status dispersion converges
to the true dispersion.
