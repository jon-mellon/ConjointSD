# Proven statements

This file lists key theorems that are already proved in the Lean development,
with the file they live in, an explanation, an intuition line, and a compact
formalization. The list is curated to cover identification, SD consistency,
transport, and model-to-target bridges.

## sdHatZ tendsto ae (PredictedSD)

File: `ConjointSD/PredictedSD.lean`

Statement: Under [IID](readable/jargon iid.md) and moment assumptions, the
empirical [standard deviation](readable/jargon standard deviation.md) of a real
process [converges](readable/jargon convergence.md) almost everywhere to the
population SD.

Intuition: If draws are i.i.d., the sample moments stabilize, so the sample SD
approaches the true population SD.

Formalization (Lean name): `sdHatZ tendsto ae`

Formalization (math):
`sdHatZ(Z) -> popSDZ(Z)` a.e. under `IIDAssumptions Z`.

## sd component consistent (SDDecompositionFromConjoint)

File: `ConjointSD/SDDecompositionFromConjoint.lean`

Statement: For a score function `g` applied to attribute draws `A i`, the
empirical SD of `g(A i)` [converges](readable/jargon convergence.md) to the
population SD when the score process satisfies [ScoreAssumptions](readable/Assumptions.md).

Intuition: Once you view each `g(A i)` as a real-valued i.i.d. sequence, the
standard SD consistency result applies to the induced score process.

Formalization (Lean name): `sd component consistent`

Formalization (math):
`sdHatZ (fun i => g (A i)) -> popSDZ (fun i => g (A i))` a.e.

## sd component consistent to popSDAttr (OracleSDConsistency)

File: `ConjointSD/OracleSDConsistency.lean`

Statement: If `A 0` has attribute [distribution](readable/jargon distribution.md)
`nu`, then the SD limit from the previous theorem can be rewritten as the
population target `popSDAttr nu g`.

Intuition: This is a transport step from the big probability space to the
attribute-level population target.

Formalization (Lean name): `sd component consistent to popSDAttr`

Formalization (math):
`sdHatZ (fun i => g (A i)) -> popSDAttr nu g` a.e., assuming `Law(A 0) = nu`.

## gExp eq gPot (ConjointIdentification)

File: `ConjointSD/ConjointIdentification.lean`

Statement: Under conjoint identification assumptions, the observed
[conditional mean](readable/jargon conditional mean.md) score equals the causal
potential-outcome score.

Intuition: Random assignment and consistency let observed conditional averages
recover causal averages.

Formalization (Lean name): `gExp eq gPot`

Formalization (math):
`gExp = gPot` under `ConjointIdAssumptions`.

## popSDAttr congr ae (TargetEquivalence)

File: `ConjointSD/TargetEquivalence.lean`

Statement: If two scores agree almost everywhere under `nu`, then their
population SDs are equal.

Intuition: Differences on a `nu`-null set do not change [population](readable/jargon population.md)
moments.

Formalization (Lean name): `popSDAttr congr ae`

Formalization (math):
If `s = t` `nu`-a.e., then `popSDAttr nu s = popSDAttr nu t`.

## gStar eq sum blocks of WellSpecified (ModelBridge)

File: `ConjointSD/ModelBridge.lean`

Statement: If the causal [estimand](readable/jargon estimand.md) `gStar` is
[well-specified](readable/jargon well specified.md) by the linear-in-terms model,
then it equals the sum of block scores.

Intuition: Well-specification means the model and target are the same function,
so the model’s block decomposition is a valid decomposition of the target.

Formalization (Lean name): `gStar eq sum blocks of WellSpecified`

Formalization (math):
`WellSpecified -> gStar = sum b gBlock b`.

## sequential consistency ae (SequentialConsistency)

File: `ConjointSD/SequentialConsistency.lean`

Statement: With evaluation-sample moment assumptions and plug-in moment
[convergence](readable/jargon convergence.md), the two-stage SD estimator is
sequentially consistent (training size then evaluation size).

Intuition: First the fitted score stabilizes, then the evaluation SD converges
to the population SD of that stabilized score.

Formalization (Lean name): `sequential consistency ae`

Formalization (math):
`sdEst m n -> popSDAttr nu (g theta0)` sequentially, under
`SplitEvalAssumptions` and `GEstimationAssumptions`.

## paper identifies potMean from condMean (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under conjoint identification assumptions, the observed conditional
mean for profile `x0` equals the potential outcome mean for `x0`.

Intuition: Random assignment and consistency make the observed conditional
average a causal mean.

Formalization (Lean name): `paper identifies potMean from condMean`

Formalization (math):
`condMean μ Yobs (eventX X x0) = potMean μ Y x0`.

## paper identifies amce from condMeans (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under conjoint identification assumptions, the difference in observed
conditional means equals the AMCE.

Intuition: AMCE is a causal contrast, and identification lets you compute it
from observed conditional averages.

Formalization (Lean name): `paper identifies amce from condMeans`

Formalization (math):
`condMean μ Yobs (eventX X x') - condMean μ Yobs (eventX X x) = amce μ Y x x'`.

## paper sd total sequential consistency ae (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: For the total score `gTotalΘ gB`, if `θhat -> θ0` and the population
moments are continuous at `θ0`, then the evaluation SD estimator is sequentially
consistent (training size then evaluation size).

Intuition: Parameter convergence plus continuity yields plug in moment
convergence, which then feeds the sequential SD consistency chain.

Formalization (Lean name): `paper sd total sequential consistency ae`

Formalization (math):
`totalErr μ A ν (gTotalΘ gB) θ0 θhat m n -> 0` sequentially in `m,n`.

## paper sd total sequential consistency to true target ae (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Adds an external validity assumption (`InvarianceAE`) so the total
score target can be replaced by a declared true target `gTrue`.

Intuition: If the model score equals the true population score on the population
support, their population SDs are identical.

Formalization (Lean name): `paper sd total sequential consistency to true target ae`

Formalization (math):
Sequential consistency for `gTotalΘ gB`, plus
`popSDAttr ν (gTotalΘ gB θ0) = popSDAttr ν gTrue`.

## paper sd total sequential consistency to gPot ae of identification (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: If the model targets the observed score and the observed score equals
the causal score, then the sequential SD consistency target is the causal score.

Intuition: Identification turns the observed score into the causal score, so the
population SD equality transfers to `gPot`.

Formalization (Lean name): `paper sd total sequential consistency to gPot ae of identification`

Formalization (math):
Sequential consistency for `gTotalΘ gB`, plus
`popSDAttr ν (gTotalΘ gB θ0) = popSDAttr ν (gPot μ Y)`.

## paper total sd estimator consistency ae of gBTerm (PaperCoreEstimand)

File: `ConjointSD/PaperCoreEstimand.lean`

Statement: The paper’s total SD estimator (plugging a term model into the
population sample) converges to the paper’s total SD target.

Intuition: This is the paper facing version of sequential consistency, specialized
to the term model used in the manuscript.

Formalization (Lean name): `paper total sd estimator consistency ae of gBTerm`

Formalization (math):
`|paperTotalSDEst μ A blk βOf φ θhat m n - paperTotalSD ν blk β0 φ| < ε` a.e. eventually.

## paper sd total sequential consistency to gStar ae of gBTerm (PaperCoreEstimand)

File: `ConjointSD/PaperCoreEstimand.lean`

Statement: If the term model is [well specified](readable/jargon_well_specified.md)
for `gStar`, then the sequential SD consistency target can be stated for `gStar`.

Intuition: Well specification identifies the causal score with the model score,
so the population SD target transfers to `gStar`.

Formalization (Lean name): `paper sd total sequential consistency to gStar ae of gBTerm`

Formalization (math):
Sequential consistency for `gTotalΘ (gBTerm ...)`, plus
`popSDAttr ν (gTotalΘ (gBTerm ...) θ0) = popSDAttr ν (gStar μ Y)`.

## Assumption matrix

Legend: `✅` = theorem relies on the assumption (directly or via bundled
assumptions), `(❌)` = does not rely on it. This table includes transitive
dependencies: if a theorem uses another theorem, it inherits that theorem’s
assumptions.

| Assumption | sdHatZ tendsto ae | sd component consistent | sd component consistent to popSDAttr | gExp eq gPot | popSDAttr congr ae | gStar eq sum blocks of WellSpecified | sequential consistency ae | paper identifies potMean from condMean | paper identifies amce from condMeans | paper sd total sequential consistency ae | paper sd total sequential consistency to true target ae | paper sd total sequential consistency to gPot ae of identification | paper total sd estimator consistency ae of gBTerm | paper sd total sequential consistency to gStar ae of gBTerm |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| IsProbabilityMeasure μ | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| IIDAssumptions intZ | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| IIDAssumptions indep | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| IIDAssumptions ident | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| IIDAssumptions intZ2 | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| PopIID measA | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| PopIID indepA | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| PopIID identA | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| ScoreAssumptions meas g | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| ScoreAssumptions int g(A0) | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| ScoreAssumptions int g(A0)2 | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| Measurable (A 0) | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| Measure map (A 0) μ = ν | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| ConjointIdAssumptions measYobs | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> |
| ConjointIdAssumptions measY | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> |
| ConjointIdAssumptions consistency | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> |
| ConjointIdAssumptions positivity | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> |
| ConjointIdAssumptions rand | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> |
| AE equality s = t under ν | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> |
| InvarianceAE | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> |
| WellSpecified | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> |
| IsProbabilityMeasure ν | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| FunctionalContinuityAssumptions cont mean | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| FunctionalContinuityAssumptions cont m2 | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| Tendsto θhat -> θ0 | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| betaOf θ0 = beta | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| GEstimationAssumptions mean tendsto | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| GEstimationAssumptions m2 tendsto | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |
| Epsilon > 0 | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: red">(❌)</span> | <span style="color: red">(❌)</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> | <span style="color: green">✅</span> |

## Theorem dependency matrix

Legend: `✅` = column theorem depends on row theorem (transitively), `(❌)` = does
not depend on it. A theorem does not depend on itself.

| Theorem | sdHatZ tendsto ae | sd component consistent | sd component consistent to popSDAttr | gExp eq gPot | popSDAttr congr ae | gStar eq sum blocks of WellSpecified | sequential consistency ae | paper identifies potMean from condMean | paper identifies amce from condMeans | paper sd total sequential consistency ae | paper sd total sequential consistency to true target ae | paper sd total sequential consistency to gPot ae of identification | paper total sd estimator consistency ae of gBTerm | paper sd total sequential consistency to gStar ae of gBTerm |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| sdHatZ tendsto ae | Ø | ✅ | ✅ | (❌) | (❌) | (❌) | ✅ | (❌) | (❌) | ✅ | ✅ | ✅ | ✅ | ✅ |
| sd component consistent | (❌) | Ø | ✅ | (❌) | (❌) | (❌) | ✅ | (❌) | (❌) | ✅ | ✅ | ✅ | ✅ | ✅ |
| sd component consistent to popSDAttr | (❌) | (❌) | Ø | (❌) | (❌) | (❌) | ✅ | (❌) | (❌) | ✅ | ✅ | ✅ | ✅ | ✅ |
| gExp eq gPot | (❌) | (❌) | (❌) | Ø | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | ✅ | (❌) | (❌) |
| popSDAttr congr ae | (❌) | (❌) | (❌) | (❌) | Ø | (❌) | (❌) | (❌) | (❌) | (❌) | ✅ | ✅ | ✅ | ✅ |
| gStar eq sum blocks of WellSpecified | (❌) | (❌) | (❌) | (❌) | (❌) | Ø | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | ✅ |
| sequential consistency ae | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | Ø | (❌) | (❌) | ✅ | ✅ | ✅ | ✅ | ✅ |
| paper identifies potMean from condMean | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | Ø | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) |
| paper identifies amce from condMeans | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | Ø | (❌) | (❌) | (❌) | (❌) | (❌) |
| paper sd total sequential consistency ae | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | Ø | ✅ | ✅ | ✅ | ✅ |
| paper sd total sequential consistency to true target ae | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | Ø | ✅ | ✅ | ✅ |
| paper sd total sequential consistency to gPot ae of identification | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | Ø | (❌) | (❌) |
| paper total sd estimator consistency ae of gBTerm | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | Ø | (❌) |
| paper sd total sequential consistency to gStar ae of gBTerm | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | (❌) | Ø |
