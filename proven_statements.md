# Proven statements

This file lists key theorems that are already proved in the Lean development,
with the file they live in, an explanation, an intuition line, and a compact
formalization. The list is curated to cover identification,
[standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md),
transport, and model-to-target bridges.

## attrSD congr ae (TargetEquivalence)

File: `ConjointSD/TargetEquivalence.lean`

Statement: If two scores agree [almost everywhere](readable/jargon_almost_everywhere.md)
under `nu`, then their [standard deviation](readable/jargon_standard_deviation.md)
values under the target [distribution](readable/jargon_distribution.md) are equal.

Intuition: Differences on a `nu`-null set do not change moments under the target
[distribution](readable/jargon_distribution.md) for the
[population](readable/jargon_population.md).

Formalization (Lean name): `attrSD congr ae`

Formalization (math):
If `s = t` `nu`-a.e., then `attrSD nu s = attrSD nu t`.

## gStar eq sum blocks of WellSpecified (ModelBridge)

File: `ConjointSD/ModelBridge.lean`

Statement: If the causal [estimand](readable/jargon_estimand.md) `gStar` is
[well-specified](readable/jargon_well_specified.md) by the
[linear-in-terms](readable/jargon_linear_in_terms.md) model, then it equals the
sum of [block](readable/jargon_block.md) scores.

Intuition: Well-specification means the model and target are the same function,
so the model’s block decomposition is a valid decomposition of the target.

Formalization (Lean name): `gStar eq sum blocks of WellSpecified`

Formalization (math):
`WellSpecified -> gStar = sum b gBlock b`.

## approx wellSpecified of approx no interactions (ApproxWellSpecifiedFromNoInteractions)

File: `ConjointSD/ApproxWellSpecifiedFromNoInteractions.lean`

Statement: If the causal target is approximately additive and the term features
can represent any additive main-effect surface, then the linear-in-terms model
is approximately [well-specified](readable/jargon_well_specified.md) with the
same uniform error bound.

Intuition: Approximate additivity fixes the target up to ε, and the full
main-effect term set lets the model match that additive surface exactly, leaving
only the ε discrepancy.

Formalization (Lean name): `approxWellSpecified_of_approxNoInteractions_of_fullMainEffects`

Formalization (math):
`ApproxNoInteractions ε ∧ FullMainEffectsTerms φ -> ∃ β, ApproxWellSpecified ε`.

## End-to-end block SD consistency (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under randomized assignment, OLS design assumptions, no-interactions/full-main-effects identification, and subject-sampling LLN (with the `gPop` LLN derived from IID subject sampling plus score regularity and the `gStar` LLN assumed), the block components of the paper score have sequentially consistent SD estimates that target the block decomposition implied by the population-mean score `gPop`. IID and boundedness of the evaluation score are assumed, with evaluation representativeness supplied by `EvalAttrLawEqPop`, and plug‑in moment convergence is **derived** from OLS coefficient convergence plus functional continuity under `ν_pop`.

Intuition: OLS consistency (`θhat → θ0`) and bounded/measurable features yield plug‑in moment convergence; subject sampling links the experiment to the population-mean score, and LLNs yield sequential consistency for each block score.

Formalization (Lean name): `paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization`

Formalization (math):
Block-level SD consistency follows from the paper OLS design chain, with targets given by the block components implied by `gPop`.

## sequential consistency ae (SequentialConsistency)

File: `ConjointSD/SequentialConsistency.lean`

Statement: With evaluation-sample representativeness and [plug-in](readable/jargon_plug_in.md)
moment [convergence](readable/jargon_convergence.md), the two-stage
[standard deviation](readable/jargon_standard_deviation.md)
[estimator](readable/jargon_estimator.md) is
[sequentially consistent](readable/jargon_sequential_consistency.md) (training
size then evaluation size), targeting the attribute-law SD under `ν_pop` with
`EvalAttrLawEqPop` tying the evaluation attribute law to `ν_pop`.

Intuition: First the fitted score stabilizes, then the evaluation
[standard deviation](readable/jargon_standard_deviation.md) converges to the
[standard deviation](readable/jargon_standard_deviation.md) under the target
[distribution](readable/jargon_distribution.md) for the
[population](readable/jargon_population.md) of that stabilized score.

Formalization (Lean name): `sequential consistency ae`

Formalization (math):
`sdEst w m n -> attrSD nu (g theta0)` sequentially, under
`SplitEvalAssumptionsBounded` and direct mean/second‑moment convergence of the plug‑in score.

## paper identifies potMean from condMean (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under conjoint identification assumptions, the observed
[conditional mean](readable/jargon_conditional_mean.md) for profile `x0` equals
the [potential outcome](readable/jargon_potential_outcome.md) mean for `x0`.

Intuition: Random assignment and consistency make the observed conditional
average a causal mean.

Formalization (Lean name): `paper identifies potMean from condMean`

Formalization (math):
`condMean μ Yobs (eventX X x0) = potMean μ Y x0`.

## paper identifies amce from condMeans (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under conjoint identification assumptions, the difference in observed
[conditional means](readable/jargon_conditional_mean.md) equals the
[AMCE](readable/jargon_amce.md).

Intuition: [AMCE](readable/jargon_amce.md) is a causal contrast, and
identification lets you compute it from observed conditional averages.

Formalization (Lean name): `paper identifies amce from condMeans`

Formalization (math):
`condMean μ Yobs (eventX X x') - condMean μ Yobs (eventX X x) = amce μ Y x x'`.

## paper sd total sequential consistency ae (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: For the total score `gTotalΘ gB`, if `θhat -> θ0` and the moments
under the target [distribution](readable/jargon_distribution.md) for the
[population](readable/jargon_population.md) are
[continuous](readable/jargon_continuity.md) at `θ0`, then the evaluation
[standard deviation](readable/jargon_standard_deviation.md)
[estimator](readable/jargon_estimator.md) is
[sequentially consistent](readable/jargon_sequential_consistency.md) (training
size then evaluation size), with `EvalAttrLawEqPop` tying the evaluation attribute law to `ν_pop`.

Intuition: [parameter](readable/jargon_parameter.md)
[convergence](readable/jargon_convergence.md) plus
[continuity](readable/jargon_continuity.md) yields [plug-in](readable/jargon_plug_in.md)
moment convergence, which then feeds the sequential
[standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md) chain.

Formalization (Lean name): `paper sd total sequential consistency ae`

Formalization (math):
`totalErr μ A ν_pop w (gTotalΘ gB) θ0 θhat m n -> 0` sequentially in `m,n`.

## paper sd total sequential consistency to true target ae (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Adds a ν_pop-a.e. target equality so the total score target can be
replaced by a declared true target `gTrue`, and then states the target
[standard deviation](readable/jargon_standard_deviation.md).

Intuition: If the model score equals the true
[population](readable/jargon_population.md) score on the
[population support](readable/jargon_population_support.md), their
[standard deviation](readable/jargon_standard_deviation.md) values under the
target [distribution](readable/jargon_distribution.md) are identical.

Formalization (Lean name): `paper sd total sequential consistency to true target ae`

Formalization (math):
Sequential consistency for `gTotalΘ gB`, plus
`attrSD ν_pop (gTotalΘ gB θ0) = attrSD ν_pop gTrue`.

## attrSD diff le of L2Approx (TargetEquivalence)

File: `ConjointSD/TargetEquivalence.lean`

Statement: If two scores are close in [L2](readable/jargon_l2.md), then their
[standard deviation](readable/jargon_standard_deviation.md) values under the
target [distribution](readable/jargon_distribution.md) are close.

Intuition: [L2](readable/jargon_l2.md) closeness bounds
[second moments](readable/jargon_second_moment.md), which bounds the
[standard deviation](readable/jargon_standard_deviation.md) difference.

Formalization (Lean name): `attrSD diff le of L2Approx`

Formalization (math):
If `E[|s - t|^2] ≤ δ^2`, then `|attrSD ν_pop s - attrSD ν_pop t| ≤ 2 * δ`.

## paper identifies potMean from condMean status (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: For the status conjoint, the observed
[conditional mean](readable/jargon_conditional_mean.md) identifies the
[potential outcome](readable/jargon_potential_outcome.md) mean.

Intuition: The status design satisfies the identification assumptions, so the
generic identification result applies.

Formalization (Lean name): `paper identifies potMean from condMean status`

Formalization (math):
`condMean = potMean` under the status design assumptions.

## paper identifies amce from condMeans status (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: For the status conjoint, [AMCE](readable/jargon_amce.md) equals a
difference of observed [conditional means](readable/jargon_conditional_mean.md).

Intuition: The status design satisfies the identification assumptions, so the
generic AMCE identification result applies.

Formalization (Lean name): `paper identifies amce from condMeans status`

Formalization (math):
`condMean(x') - condMean(x) = amce`.

## paper gStar eq sum blocks of WellSpecified (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: If the [term](readable/jargon_term.md) model is
[well-specified](readable/jargon_well_specified.md) for `gStar`, then the causal
score equals the sum of [block](readable/jargon_block.md) scores.

Intuition: Well-specification makes the model score identical to the causal
score.

Formalization (Lean name): `paper gStar eq sum blocks of WellSpecified`

Formalization (math):
`WellSpecified -> gStar = sum b gBlock b`.

## paper sd blocks and total sequential consistency ae of bounded (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: With boundedness, the [block](readable/jargon_block.md) and total
[standard deviation](readable/jargon_standard_deviation.md)
[estimators](readable/jargon_estimator.md) are
[sequentially consistent](readable/jargon_sequential_consistency.md).

Intuition: Boundedness ensures moments exist and strengthens the
[consistency](readable/jargon_consistency.md) path.

Formalization (Lean name): `paper sd blocks and total sequential consistency ae of bounded`

Formalization (math):
Block and total `totalErr` go to 0 sequentially under bounded assumptions.

## paper sd blocks sequential consistency to true target ae (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: If [block](readable/jargon_block.md) scores match the true targets
[almost everywhere](readable/jargon_almost_everywhere.md), the block
[standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md) target transfers to the true
targets.

Intuition: A.E. equality implies equal
[standard deviation](readable/jargon_standard_deviation.md) values under the
target [distribution](readable/jargon_distribution.md).

Formalization (Lean name): `paper sd blocks sequential consistency to true target ae`

Formalization (math):
`attrSD ν_pop (gBlock ...) = attrSD ν_pop gTrueB` for each block.

## paper sd blocks sequential consistency to approx target ae (ApproxPaperWrappers)

File: `ConjointSD/ApproxPaperWrappers.lean`

Statement: If [blocks](readable/jargon_block.md) are approximately correct in
[L2](readable/jargon_l2.md), the block
[standard deviation](readable/jargon_standard_deviation.md) targets are within
an explicit bound.

Intuition: [L2](readable/jargon_l2.md) approximation bounds
[standard deviation](readable/jargon_standard_deviation.md) error.

Formalization (Lean name): `paper sd blocks sequential consistency to approx target ae`

Formalization (math):
`|attrSD ν_pop s - attrSD ν_pop t| ≤ bound` for each block.

## paper sd total sequential consistency to gStar approx ae of ApproxWellSpecifiedAE (ApproxPaperWrappers)

File: `ConjointSD/ApproxPaperWrappers.lean`

Statement: If the model is approximately
[well-specified](readable/jargon_well_specified.md)
ν_pop-[almost everywhere](readable/jargon_almost_everywhere.md), the total
[standard deviation](readable/jargon_standard_deviation.md) target is within an
explicit bound of the `gStar` target.

Intuition: Approximate [well-specification](readable/jargon_well_specified.md)
translates into [standard deviation](readable/jargon_standard_deviation.md)
error bounds.

Formalization (Lean name): `paper sd total sequential consistency to gStar approx ae of ApproxWellSpecifiedAE`

Formalization (math):
`|attrSD ν_pop gTotal - attrSD ν_pop gStar(μexp)| ≤ bound`.

## paper sd total sequential consistency to gStar approx ae of ApproxOracleAE (ApproxPaperWrappers)

File: `ConjointSD/ApproxPaperWrappers.lean`

Statement: If a flexible [oracle](readable/jargon_oracle.md) approximates
`gStar` and the model approximates the oracle, the total
[standard deviation](readable/jargon_standard_deviation.md) target is within a
combined bound of the `gStar` target.

Intuition: Two approximation errors add to a
[standard deviation](readable/jargon_standard_deviation.md) error bound.

Formalization (Lean name): `paper sd total sequential consistency to gStar approx ae of ApproxOracleAE`

Formalization (math):
`|attrSD ν_pop gTotal - attrSD ν_pop gStar(μexp)| ≤ bound`.

## paper ols normal eq of wellSpecified (PaperOLSConsistency)

File: `ConjointSD/PaperOLSConsistency.lean`

Statement: If `gStar` is [well-specified](readable/jargon_well_specified.md) by the paper’s feature map and the features are bounded/measurable, the paper’s population normal equations hold for `θ0`:
`(attrGram ν_pop φPaper).mulVec θ0 = attrCross ν_pop gStar φPaper`.

Intuition: well‑specification turns the cross‑moment into a linear combination of
feature cross‑moments, so the Gram matrix multiplies `θ0` to match the
feature–outcome cross moment.

Formalization (Lean name): `paper_ols_normal_eq_of_wellSpecified`

Formalization (math):
Normal equations for the population OLS coefficients follow from
`gStar = gLin θ0` and bounded/measurable features.

## paper ols attr moments of design ae (PaperOLSConsistency)

File: `ConjointSD/PaperOLSConsistency.lean`

Statement: Under design IID (`DesignAttrIID`), the paper’s design-side bundle
(`PaperOLSDesignAssumptions`, including observation-noise LLN) and full‑rank,
the inverse‑Gram and cross‑moment convergence statements hold almost everywhere
for the paper’s term set and causal estimand `gStar`.

Intuition: bounded/measurable features and a design‑IID attribute stream give the
Gram/cross LLNs, and full‑rank provides inverse‑Gram stability.

Formalization (Lean name): `paper_ols_attr_moments_of_design_ae`

Formalization (math):
Inverse‑Gram convergence and cross‑moment convergence hold a.e. given the design LLN and full‑rank.

## paper sd total sequential consistency to true target ae of paper ols design ae of NoInteractions of randomization (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under randomized assignment, the paper OLS design assumptions,
full main-effects terms, and no-interactions, there exists a coefficient
vector `theta0` such that the plug‑in SD for the total score
converges and equals the population‑mean score SD `attrSD ν_pop (gPop μpop gP)`,
using the respondent-sampling LLN bridge.

Intuition: randomization and OLS assumptions identify the additive
status‑assigning rule in the experiment; respondent sampling links the
experimental estimand to the population-mean score, so the evaluation SD
converges to the population SD.

Formalization (Lean name):
`paper sd total sequential consistency to true target ae of paper ols design ae of NoInteractions of randomization`

Formalization (math):
Sequential consistency of `attrSD ν_pop (gTotalΘ θ0)` plus the respondent-sampling
LLN bridge yields `attrSD ν_pop (gTotalΘ θ0) = attrSD ν_pop (gPop μpop gP)` a.e.

## Dependency tables

The dependency matrices live in `dependency_tables.md`.
