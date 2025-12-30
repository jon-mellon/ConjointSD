# Proven statements

This file lists key theorems that are already proved in the Lean development,
with the file they live in, an explanation, an intuition line, and a compact
formalization. The list is curated to cover identification, SD consistency,
transport, and model-to-target bridges.

## sdHatZ_tendsto_ae (PredictedSD)

File: `ConjointSD/PredictedSD.lean`

Statement: Under [IID](readable/jargon_iid.md) and moment assumptions, the
empirical [standard deviation](readable/jargon_standard_deviation.md) of a real
process [converges](readable/jargon_convergence.md) almost everywhere to the
population SD.

Intuition: If draws are i.i.d., the sample moments stabilize, so the sample SD
approaches the true population SD.

Formalization (Lean name): `sdHatZ_tendsto_ae`

Formalization (math):
`sdHatZ(Z) -> popSDZ(Z)` a.e. under `IIDAssumptions Z`.

## sd_component_consistent (SDDecompositionFromConjoint)

File: `ConjointSD/SDDecompositionFromConjoint.lean`

Statement: For a score function `g` applied to attribute draws `A i`, the
empirical SD of `g(A i)` [converges](readable/jargon_convergence.md) to the
population SD when the score process satisfies [ScoreAssumptions](readable/Assumptions.md).

Intuition: Once you view each `g(A i)` as a real-valued i.i.d. sequence, the
standard SD consistency result applies to the induced score process.

Formalization (Lean name): `sd_component_consistent`

Formalization (math):
`sdHatZ (fun i => g (A i)) -> popSDZ (fun i => g (A i))` a.e.

## sd_component_consistent_to_popSDAttr (OracleSDConsistency)

File: `ConjointSD/OracleSDConsistency.lean`

Statement: If `A 0` has attribute [distribution](readable/jargon_distribution.md)
`nu`, then the SD limit from the previous theorem can be rewritten as the
population target `popSDAttr nu g`.

Intuition: This is a transport step from the big probability space to the
attribute-level population target.

Formalization (Lean name): `sd_component_consistent_to_popSDAttr`

Formalization (math):
`sdHatZ (fun i => g (A i)) -> popSDAttr nu g` a.e., assuming `Law(A 0) = nu`.

## gExp_eq_gPot (ConjointIdentification)

File: `ConjointSD/ConjointIdentification.lean`

Statement: Under conjoint identification assumptions, the observed
[conditional mean](readable/jargon_conditional_mean.md) score equals the causal
potential-outcome score.

Intuition: Random assignment and consistency let observed conditional averages
recover causal averages.

Formalization (Lean name): `gExp_eq_gPot`

Formalization (math):
`gExp = gPot` under `ConjointIdAssumptions`.

## popSDAttr_congr_ae (TargetEquivalence)

File: `ConjointSD/TargetEquivalence.lean`

Statement: If two scores agree almost everywhere under `nu`, then their
population SDs are equal.

Intuition: Differences on a `nu`-null set do not change [population](readable/jargon_population.md)
moments.

Formalization (Lean name): `popSDAttr_congr_ae`

Formalization (math):
If `s = t` `nu`-a.e., then `popSDAttr nu s = popSDAttr nu t`.

## gStar_eq_sum_blocks_of_WellSpecified (ModelBridge)

File: `ConjointSD/ModelBridge.lean`

Statement: If the causal [estimand](readable/jargon_estimand.md) `gStar` is
[well-specified](readable/jargon_well_specified.md) by the linear-in-terms model,
then it equals the sum of block scores.

Intuition: Well-specification means the model and target are the same function,
so the model’s block decomposition is a valid decomposition of the target.

Formalization (Lean name): `gStar_eq_sum_blocks_of_WellSpecified`

Formalization (math):
`WellSpecified -> gStar = sum_b gBlock b`.

## sequential_consistency_ae (SequentialConsistency)

File: `ConjointSD/SequentialConsistency.lean`

Statement: With evaluation-sample moment assumptions and plug-in moment
[convergence](readable/jargon_convergence.md), the two-stage SD estimator is
sequentially consistent (training size then evaluation size).

Intuition: First the fitted score stabilizes, then the evaluation SD converges
to the population SD of that stabilized score.

Formalization (Lean name): `sequential_consistency_ae`

Formalization (math):
`sdEst m n -> popSDAttr nu (g theta0)` sequentially, under
`SplitEvalAssumptions` and `GEstimationAssumptions`.

## Assumption matrix

Legend: `Y` = theorem relies on the assumption, `N` = does not rely on it.

Columns:
- T1 = sdHatZ_tendsto_ae
- T2 = sd_component_consistent
- T3 = sd_component_consistent_to_popSDAttr
- T4 = gExp_eq_gPot
- T5 = popSDAttr_congr_ae
- T6 = gStar_eq_sum_blocks_of_WellSpecified
- T7 = sequential_consistency_ae

| Assumption | T1 | T2 | T3 | T4 | T5 | T6 | T7 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| IIDAssumptions | Y | N | N | N | N | N | N |
| ScoreAssumptions | N | Y | Y | N | N | N | N |
| Law(A0) = nu | N | N | Y | N | N | N | N |
| ConjointIdAssumptions | N | N | N | Y | N | N | N |
| InvarianceAE | N | N | N | N | Y | N | N |
| PopulationMomentAssumptions | N | N | N | N | Y | N | N |
| WellSpecified | N | N | N | N | N | Y | N |
| SplitEvalAssumptions | N | N | N | N | N | N | Y |
| GEstimationAssumptions | N | N | N | N | N | N | Y |
