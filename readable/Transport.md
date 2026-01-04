# Transport.lean

Lean file: [ConjointSD/Transport.lean](../ConjointSD/Transport.lean)

This file gathers the target human [population](jargon_population.md)-level targets, transport assumptions, and small transport lemmas used by later results.

Population targets:
- `attrMean`, `attrM2`, `attrVar`, `attrSD` define the mean, second moment, variance, and standard deviation of a score function under the target-population attribute [distribution](jargon_distribution.md) `ν` (see [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md)).
- `AttrMomentAssumptions` bundles [integrable](jargon_integrable.md) conditions so these quantities are well-defined.

Transport assumptions:
- `SubjectSamplingLLN` packages the experiment-subject sampling LLN bridge: subject-level
  score averages converge to both the experimental estimand `gStar` and the population
  mean score `gPop`. The implied ν-a.e. equality is derived from these LLNs.
- `EvalWeightMatchesPopMoments` packages the evaluation-weight moment match that
  links the evaluation sample to the target population moments under `ν`.

This file is the foundation: it exposes the target human population targets and transport conditions that all later [consistency](jargon_consistency.md) results point to.
