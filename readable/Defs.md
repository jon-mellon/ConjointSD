# Defs.lean

Lean file: [ConjointSD/Defs.lean](../ConjointSD/Defs.lean)

This file centralizes shared definitions that the rest of the project (especially
assumptions) builds on.

Highlights:
- Core score-model definitions: `gLin`, `gStar`, `PaperTerm`, `βPaper`, `φPaper`.
- Ordered-task helpers: `OrderedProfiles` for profile-order invariance
  assumptions.
- Attribute-distribution and experimental design distribution moment functionals:
  `attrMean`, `attrM2`, `attrVar`, `attrSD` (all parameterized by a generic attribute
  distribution `xiAttr`; use `ν` only for the target population in transport files),
  `meanHatZ`, `m2HatZ`,
  `designMeanZ`/`designM2Z`/`designVarZ`/`designSDZ`
  (see [mean](jargon_mean.md), [variance](jargon_variance.md),
  [standard deviation](jargon_standard_deviation.md)).
- Plug-in and induced-process helpers: `gHat`, `Zcomp`, `attrMeanΘ`, `attrM2Θ`, `blockScoreΘ`.
- [OLS](jargon_ols.md) helpers and [estimator](jargon_estimator.md) scaffolding:
  `gramMatrix`, `crossVec`, `attrGram`, `attrCross`.
- Conjoint identification primitives: `eventX`, `condMean`, `potMean`, `amce` ([AMCE](jargon_amce.md)).

Purpose:
- Keep foundational definitions in one place so assumption packages can be audited in
`ConjointSD/Assumptions.lean`.
