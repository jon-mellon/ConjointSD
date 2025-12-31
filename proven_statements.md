# Proven statements

This file lists key theorems that are already proved in the Lean development,
with the file they live in, an explanation, an intuition line, and a compact
formalization. The list is curated to cover identification,
[standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md),
transport, and model-to-target bridges.

## sdHatZ tendsto ae (PredictedSD)

File: `ConjointSD/PredictedSD.lean`

Statement: Under [IID](readable/jargon_iid.md) and moment assumptions, the
empirical [standard deviation](readable/jargon_standard_deviation.md) of a real
process [converges](readable/jargon_convergence.md) almost everywhere to the
[standard deviation](readable/jargon_standard_deviation.md) under the target
[distribution](readable/jargon_distribution.md) for the
[population](readable/jargon_population.md).

Intuition: If draws are i.i.d., the sample moments stabilize, so the sample
[standard deviation](readable/jargon_standard_deviation.md) approaches the true
[standard deviation](readable/jargon_standard_deviation.md) under the target
[distribution](readable/jargon_distribution.md) for the
[population](readable/jargon_population.md).

Formalization (Lean name): `sdHatZ tendsto ae`

Formalization (math):
`sdHatZ(Z) -> designSDZ(Z)` a.e. for score processes derived from `ScoreAssumptions`.

## sd component consistent (SDDecompositionFromConjoint)

File: `ConjointSD/SDDecompositionFromConjoint.lean`

Statement: For a score function `g` applied to attribute draws `A i`, the
empirical [standard deviation](readable/jargon_standard_deviation.md) of
`g(A i)` [converges](readable/jargon_convergence.md) to the
[standard deviation](readable/jargon_standard_deviation.md) under the target
[distribution](readable/jargon_distribution.md) for the
[population](readable/jargon_population.md) when the score process satisfies
[ScoreAssumptions](readable/Assumptions.md).

Intuition: Once you view each `g(A i)` as a real-valued i.i.d. sequence, the
standard [standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md) result applies to the induced
score process.

Formalization (Lean name): `sd component consistent`

Formalization (math):
`sdHatZ (fun i => g (A i)) -> designSDZ (fun i => g (A i))` a.e.

## sd component consistent of design (SDDecompositionFromConjoint)

File: `ConjointSD/SDDecompositionFromConjoint.lean`

Statement: If the attribute stream satisfies `ConjointRandomizationStream`, then
the SD consistency result for `g(A i)` holds under the standard measurability
and second-moment requirements.

Intuition: The randomization stream supplies the IID assumptions, so the
standard empirical SD convergence proof goes through.

Formalization (Lean name): `sd_component_consistent_of_design`

Formalization (math):
`ConjointRandomizationStream A Y -> sdHatZ (fun i => g (A i)) -> designSDZ (fun i => g (A i))`.

## gExp eq gPot (ConjointIdentification)

File: `ConjointSD/ConjointIdentification.lean`

Statement: Under conjoint identification assumptions, the observed
[conditional mean](readable/jargon_conditional_mean.md) score equals the causal
[potential outcome](readable/jargon_potential_outcome.md) score.

Intuition: Random assignment and consistency let observed conditional averages
recover causal averages.

Formalization (Lean name): `gExp eq gPot`

Formalization (math):
`gExp = gPot` under `ConjointIdRandomized`.

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

## wellSpecified of no interactions full main effects (WellSpecifiedFromNoInteractions)

File: `ConjointSD/WellSpecifiedFromNoInteractions.lean`

Statement: If the causal target is additive (no interactions) and the chosen
term features are rich enough to represent any additive main-effect surface,
then the linear-in-terms model is [well-specified](readable/jargon_well_specified.md).

Intuition: Additivity gives the shape of the target, and the full main-effect
term set guarantees the regression basis can match that shape exactly.

Formalization (Lean name): `wellSpecified_of_noInteractions_of_fullMainEffects`

Formalization (math):
`NoInteractions ∧ FullMainEffectsTerms φ -> ∃ β, WellSpecified μ Y β φ`.

## approx wellSpecified of approx no interactions (WellSpecifiedFromNoInteractions)

File: `ConjointSD/WellSpecifiedFromNoInteractions.lean`

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

## sequential consistency ae (SequentialConsistency)

File: `ConjointSD/SequentialConsistency.lean`

Statement: With evaluation-sample moment assumptions and [plug-in](readable/jargon_plug_in.md)
moment [convergence](readable/jargon_convergence.md), the two-stage
[standard deviation](readable/jargon_standard_deviation.md)
[estimator](readable/jargon_estimator.md) is
[sequentially consistent](readable/jargon_sequential_consistency.md) (training
size then evaluation size), targeting the attribute-law SD under `ν` with
`EvalWeightMatchesAttrMoments` matching weighted evaluation moments to `ν`.

Intuition: First the fitted score stabilizes, then the evaluation
[standard deviation](readable/jargon_standard_deviation.md) converges to the
[standard deviation](readable/jargon_standard_deviation.md) under the target
[distribution](readable/jargon_distribution.md) for the
[population](readable/jargon_population.md) of that stabilized score.

Formalization (Lean name): `sequential consistency ae`

Formalization (math):
`sdEst w m n -> attrSD nu (g theta0)` sequentially, under
`SplitEvalWeightAssumptions`, raw parameter convergence, and
`FunctionalContinuityAssumptions`.

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
size then evaluation size), with `EvalWeightMatchesAttrMoments` tying weighted evaluation moments to `ν`.

Intuition: [parameter](readable/jargon_parameter.md)
[convergence](readable/jargon_convergence.md) plus
[continuity](readable/jargon_continuity.md) yields [plug-in](readable/jargon_plug_in.md)
moment convergence, which then feeds the sequential
[standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md) chain.

Formalization (Lean name): `paper sd total sequential consistency ae`

Formalization (math):
`totalErr μ A ν w (gTotalΘ gB) θ0 θhat m n -> 0` sequentially in `m,n`.

## paper sd total sequential consistency to true target ae (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Adds an external validity assumption (`InvarianceAE`) so the total
score target can be replaced by a declared true target `gTrue`, and then
states the target [standard deviation](readable/jargon_standard_deviation.md).

Intuition: If the model score equals the true
[population](readable/jargon_population.md) score on the
[population support](readable/jargon_population_support.md), their
[standard deviation](readable/jargon_standard_deviation.md) values under the
target [distribution](readable/jargon_distribution.md) are identical.

Formalization (Lean name): `paper sd total sequential consistency to true target ae`

Formalization (math):
Sequential consistency for `gTotalΘ gB`, plus
`attrSD ν (gTotalΘ gB θ0) = attrSD ν gTrue`.

## paper sd total sequential consistency to gPot ae of identification (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: If the model targets the observed score and the observed score equals
the causal score, then the sequential
[standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md) target is the causal score.

Intuition: Identification turns the observed score into the causal score, so the
[standard deviation](readable/jargon_standard_deviation.md) equality under the
target [distribution](readable/jargon_distribution.md) transfers to `gPot`.

Formalization (Lean name): `paper sd total sequential consistency to gPot ae of identification`

Formalization (math):
Sequential consistency for `gTotalΘ gB`, plus
`attrSD ν (gTotalΘ gB θ0) = attrSD ν (gPot μexp Y)`.

## paper total sd estimator consistency ae of gBTerm (PaperCoreEstimand)

File: `ConjointSD/PaperCoreEstimand.lean`

Statement: The paper’s total [standard deviation](readable/jargon_standard_deviation.md)
[estimator](readable/jargon_estimator.md) (plugging a [term](readable/jargon_term.md)
model into the target human [population](readable/jargon_population.md) attribute
[distribution](readable/jargon_distribution.md), with `EvalWeightMatchesAttrMoments` connecting
weighted evaluation moments to `ν`)
[converges](readable/jargon_convergence.md) to the paper’s total
[standard deviation](readable/jargon_standard_deviation.md) target.

Intuition: This is the paper-facing version of
[sequential consistency](readable/jargon_sequential_consistency.md), specialized
to the [term](readable/jargon_term.md) model used in the manuscript.

Formalization (Lean name): `paper total sd estimator consistency ae of gBTerm`

Formalization (math):
`|paperTotalSDEst μ A w blk βOf φ θhat m n - paperTotalSD ν blk β0 φ| < ε` a.e. eventually.

## paper sd total sequential consistency to gStar ae of gBTerm (PaperCoreEstimand)

File: `ConjointSD/PaperCoreEstimand.lean`

Statement: If the [term](readable/jargon_term.md) model is
[well specified](readable/jargon_well_specified.md)
for `gStar`, then the sequential
[standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md) target can be stated for the
`gStar` [standard deviation](readable/jargon_standard_deviation.md).

Intuition: Well specification identifies the causal score with the model score,
so the [standard deviation](readable/jargon_standard_deviation.md) target under
the target [distribution](readable/jargon_distribution.md) transfers to `gStar`.

Formalization (Lean name): `paper sd total sequential consistency to gStar ae of gBTerm`

Formalization (math):
Sequential consistency for `gTotalΘ (gBTerm ...)`, plus
`attrSD ν (gTotalΘ (gBTerm ...) θ0) = attrSD ν (gStar μexp Y)`.

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
If `E[|s - t|^2] ≤ δ^2`, then `|attrSD ν s - attrSD ν t| ≤ 2 * δ`.

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
`attrSD ν (gBlock ...) = attrSD ν gTrueB` for each block.

## paper sd blocks sequential consistency to approx target ae (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: If [blocks](readable/jargon_block.md) are approximately correct in
[L2](readable/jargon_l2.md), the block
[standard deviation](readable/jargon_standard_deviation.md) targets are within
an explicit bound.

Intuition: [L2](readable/jargon_l2.md) approximation bounds
[standard deviation](readable/jargon_standard_deviation.md) error.

Formalization (Lean name): `paper sd blocks sequential consistency to approx target ae`

Formalization (math):
`|attrSD ν s - attrSD ν t| ≤ bound` for each block.

## paper sd total sequential consistency to gStar approx ae of ApproxWellSpecifiedAE (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: If the model is approximately
[well-specified](readable/jargon_well_specified.md)
ν-[almost everywhere](readable/jargon_almost_everywhere.md), the total
[standard deviation](readable/jargon_standard_deviation.md) target is within an
explicit bound of the `gStar` target.

Intuition: Approximate [well-specification](readable/jargon_well_specified.md)
translates into [standard deviation](readable/jargon_standard_deviation.md)
error bounds.

Formalization (Lean name): `paper sd total sequential consistency to gStar approx ae of ApproxWellSpecifiedAE`

Formalization (math):
`|attrSD ν gTotal - attrSD ν gStar(μexp)| ≤ bound`.

## paper sd total sequential consistency to gStar approx ae of ApproxOracleAE (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: If a flexible [oracle](readable/jargon_oracle.md) approximates
`gStar` and the model approximates the oracle, the total
[standard deviation](readable/jargon_standard_deviation.md) target is within a
combined bound of the `gStar` target.

Intuition: Two approximation errors add to a
[standard deviation](readable/jargon_standard_deviation.md) error bound.

Formalization (Lean name): `paper sd total sequential consistency to gStar approx ae of ApproxOracleAE`

Formalization (math):
`|attrSD ν gTotal - attrSD ν gStar(μexp)| ≤ bound`.

## paper sd blocks and total sequential consistency ae of paper ols moments (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under paper [OLS](readable/jargon_ols.md) moment assumptions and
bounded/measurable paper features, block and total
[sequential consistency](readable/jargon_sequential_consistency.md) holds for
the [term](readable/jargon_term.md) model.

Intuition: [OLS](readable/jargon_ols.md) [consistency](readable/jargon_consistency.md)
yields the [plug-in](readable/jargon_plug_in.md) moment assumptions, and bounded
features supply functional continuity, together driving the
[standard deviation](readable/jargon_standard_deviation.md)
[consistency](readable/jargon_consistency.md) chain.

Formalization (Lean name): `paper sd blocks and total sequential consistency ae of paper ols moments`

Formalization (math):
Block and total `totalErr` go to 0 sequentially under OLS moment assumptions.

## paper sd total sequential consistency ae of paper ols gStar total (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under paper [OLS](readable/jargon_ols.md) moment assumptions,
bounded/measurable paper features, and
[well-specification](readable/jargon_well_specified.md), the total sequential
[consistency](readable/jargon_consistency.md) target is the
[standard deviation](readable/jargon_standard_deviation.md) of `gStar`.

Intuition: [OLS](readable/jargon_ols.md) [consistency](readable/jargon_consistency.md),
bounded-feature continuity, and
[well-specification](readable/jargon_well_specified.md) transfer the
[standard deviation](readable/jargon_standard_deviation.md) target to the causal
score.

Formalization (Lean name): `paper sd total sequential consistency ae of paper ols gStar total`

Formalization (math):
`attrSD ν gTotal = attrSD ν gStar(μexp)` under OLS moments and well-spec.

## paper sd total sequential consistency ae of paper ols design total ae (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under the paper’s design-side OLS bundle (`PaperOLSDesignAssumptions`),
the full‑rank condition (`PaperOLSFullRankAssumptions`), and
well‑specification, the total
sequential [consistency](readable/jargon_consistency.md) result holds a.e. over
training draws, and the total-score [standard deviation](readable/jargon_standard_deviation.md)
target equals the `gStar` target.

Intuition: the design‑side assumptions yield raw parameter convergence (with
normal equations derived from well‑specification and bounded features) and
bounded-feature continuity along almost all training sample paths, so the
sequential consistency chain can be applied without separately assuming
plug‑in moment convergence or functional continuity.

Formalization (Lean name): `paper_sd_total_sequential_consistency_ae_of_paper_ols_design_total_ae`

Formalization (math):
For a.e. training draw, total `totalErr` goes to 0 sequentially and
`attrSD ν gTotal = attrSD ν gStar(μexp)`.

## paper ols normal eq of wellSpecified (PaperOLSConsistency)

File: `ConjointSD/PaperOLSConsistency.lean`

Statement: If `gStar` is [well-specified](readable/jargon_well_specified.md) by the paper’s feature map and the features are bounded/measurable, the paper’s population normal equations hold for `θ0`:
`(attrGram ν φPaper).mulVec θ0 = attrCross ν gStar φPaper`.

Intuition: well‑specification turns the cross‑moment into a linear combination of
feature cross‑moments, so the Gram matrix multiplies `θ0` to match the
feature–outcome cross moment.

Formalization (Lean name): `paper_ols_normal_eq_of_wellSpecified`

Formalization (math):
Normal equations for the population OLS coefficients follow from
`gStar = gLin θ0` and bounded/measurable features.

## paper ols attr moments of design ae (PaperOLSConsistency)

File: `ConjointSD/PaperOLSConsistency.lean`

Statement: Under the paper’s design-side bundle (`PaperOLSDesignAssumptions`),
plus inverse‑Gram stability and identification, the OLS moment assumptions
(`OLSMomentAssumptionsOfAttr`) hold almost everywhere for the paper’s
term set and causal estimand `gStar`.

Intuition: bounded/measurable features and a design‑IID attribute stream give the
Gram/cross LLNs; transport of those moments to the target `ν` plus invertibility
and normal‑equation identification complete the OLS moment package.

Formalization (Lean name): `paper_ols_attr_moments_of_design_ae`

Formalization (math):
`OLSMomentAssumptionsOfAttr` holds a.e. given design LLN, inverse Gram convergence,
and identification under `ν`.

## paper sd total sequential consistency to gStar ae of WellSpecified of hGTotal (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: If raw parameter convergence and
`FunctionalContinuityAssumptions` hold and the model is
[well-specified](readable/jargon_well_specified.md) for `gStar`, the total
[standard deviation](readable/jargon_standard_deviation.md) target is the
`gStar` [standard deviation](readable/jargon_standard_deviation.md).

Intuition: functional continuity plus θ-hat convergence drive the same
[standard deviation](readable/jargon_standard_deviation.md) target transfer as
plug‑in moment convergence.

Formalization (Lean name): `paper sd total sequential consistency to gStar ae of WellSpecified of hGTotal`

Formalization (math):
`attrSD ν gTotal = attrSD ν gStar(μexp)` under θ-hat convergence,
`FunctionalContinuityAssumptions`, and well-spec.

## paper sd total sequential consistency to gStar ae of NoInteractions (PaperWrappers)

File: `ConjointSD/PaperWrappers.lean`

Statement: Under the no-[interactions](readable/jargon_interaction.md)
assumption, the total
[standard deviation](readable/jargon_standard_deviation.md) target is the
`gStar` [standard deviation](readable/jargon_standard_deviation.md).

Intuition: No-[interactions](readable/jargon_interaction.md) implies
[well-specification](readable/jargon_well_specified.md), which transfers the
[standard deviation](readable/jargon_standard_deviation.md) target to `gStar`.

Formalization (Lean name): `paper sd total sequential consistency to gStar ae of NoInteractions`

Formalization (math):
`attrSD ν gTotal = attrSD ν gStar(μexp)` under no-interactions.

## Dependency tables

The dependency matrices live in `dependency_tables.md`.
