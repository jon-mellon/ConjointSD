# Transport.lean

Lean file: [ConjointSD/Transport.lean](../ConjointSD/Transport.lean)

This file gathers the target human [population](jargon_population.md)-level targets, transport assumptions, and small transport lemmas used by later results.

Population targets:
- `attrMean`, `attrM2`, `attrVar`, `attrSD` define the mean, second moment, variance, and standard deviation of a score function under the target-population attribute [distribution](jargon_distribution.md) `ν_pop` (see [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md)).
- `AttrMomentAssumptions` bundles measurability and boundedness so these quantities are well-defined, and uses boundedness to derive the needed [integrable](jargon_integrable.md) moments.

Transport assumptions:
- `SubjectSamplingLLN` packages the experiment-subject sampling LLN bridge: subject-level
  score averages converge to both the experimental estimand `gStar` and the population
  mean score `gPop`. In the main chain, the `gPop` convergence is derived from
  `SubjectSamplingIID` + `SubjectScoreAssumptions`, while the `gStar` convergence is assumed
  via `SubjectSamplingLLNStar`. The implied ν_pop-a.e. equality is derived from these LLNs.
- `EvalAttrLawEqPop` states the evaluation attribute law equals `ν_pop`, providing the SRS
  representativeness assumption for evaluation targets.

This file is the foundation: it exposes the target human population targets and transport conditions that all later [consistency](jargon_consistency.md) results point to.
