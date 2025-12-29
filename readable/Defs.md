# Defs.lean

Lean file: [ConjointSD/Defs.lean](../ConjointSD/Defs.lean)

This file centralizes shared definitions that the rest of the project (especially
assumptions) builds on.

Highlights:
- Core score-model definitions: `gLin`, `gStar`, `PaperTerm`, `βPaper`, `φPaper`.
- [Population](jargon_population.md)/empirical moment functionals: `popMeanAttr`, `popM2Attr`,
  `popVarAttr`, `popSDAttr`, `meanHatZ`, `m2HatZ`, `varHatZ`, `sdHatZ`, plus
  `popMeanZ`/`popM2Z`/`popVarZ`/`popSDZ` (see [mean](jargon_mean.md),
  [variance](jargon_variance.md), [standard deviation](jargon_standard_deviation.md)).
- Plug-in and induced-process helpers: `gHat`, `Zcomp`, `popMeanΘ`, `popM2Θ`, `blockScoreΘ`.
- [OLS](jargon_ols.md) helpers and [estimator](jargon_estimator.md) scaffolding: `empiricalRisk`,
  `OLSSequence`, `gramMatrix`, `crossVec`, `popGram`, `popCross`.
- Conjoint identification primitives: `eventX`, `condMean`, `potMean`, `amce`.

Purpose:
- Keep foundational definitions in one place so assumption packages can be audited in
`ConjointSD/Assumptions.lean`.
