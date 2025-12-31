# ConjointSD project map

This map links to the readable summaries for each `.lean` file and how it connects to the rest of the project.

## Top-level entry

- [ConjointSD.lean](readable/ConjointSD.md) imports the main theory files in a single module for downstream use.

## Shared definitions and assumptions

- [ConjointSD/Defs.lean](readable/Defs.md) centralizes core definitions used across the project (attribute-distribution/experimental-design moments for the target human [population](readable/jargon_population.md), [plug-in](readable/jargon_plug_in.md) scores, [OLS](readable/jargon_ols.md) helpers, and conjoint primitives).
- [ConjointSD/Assumptions.lean](readable/Assumptions.md) collects all assumption bundles (transport, [IID](readable/jargon_iid.md)/score, [regression](readable/jargon_regression.md)/[OLS](readable/jargon_ols.md), identification, paper-specific packages, plus the [additive-projection](readable/jargon_additive_projection.md) oracle definition for component targets).

## Core probability/SD machinery

- [ConjointSD/PredictedSD.lean](readable/PredictedSD.md) defines empirical/experimental-design [mean](readable/jargon_mean.md), [second moment](readable/jargon_second_moment.md), [variance](readable/jargon_variance.md), and [SD](readable/jargon_standard_deviation.md) for a real-valued process; proves [LLN](readable/jargon_lln.md)-based [consistency](readable/jargon_consistency.md) `sdHatZ -> designSDZ`.
- [ConjointSD/SDDecompositionFromConjoint.lean](readable/SDDecompositionFromConjoint.md) lifts `PredictedSD` to conjoint scores and proves [SD](readable/jargon_standard_deviation.md) [consistency](readable/jargon_consistency.md) for single scores and [block](readable/jargon_block.md) families using assumption bundles from `Assumptions.lean`.
- [ConjointSD/VarianceDecompositionFromBlocks.lean](readable/VarianceDecompositionFromBlocks.md) defines [block](readable/jargon_block.md)-total scores and proves a [variance](readable/jargon_variance.md) proxy decomposition into sums of [covariances](readable/jargon_covariance.md); relies on [block](readable/jargon_block.md) scores from `SDDecompositionFromConjoint`.

## Population targets and transport

- [ConjointSD/Transport.lean](readable/Transport.md) re-exports attribute-distribution functionals and transport assumptions now centralized in `Defs.lean`/`Assumptions.lean`.
- [ConjointSD/DesignAttributeBridge.lean](readable/DesignAttributeBridge.md) bridges moments under `μ` for `g(A0)` to moments under `ν` for `g`; uses `Transport` and `SDDecompositionFromConjoint`.
- [ConjointSD/SurveyWeights.lean](readable/SurveyWeights.md) adds weighted target-human-[population](readable/jargon_population.md) [estimands](readable/jargon_estimand.md) and finite-[population](readable/jargon_population.md) targets; builds on `Transport`.
- [ConjointSD/TargetEquivalence.lean](readable/TargetEquivalence.md) shows target human [population](readable/jargon_population.md) moments/[SDs](readable/jargon_standard_deviation.md) are equal when scores agree `ν`-[a.e.](readable/jargon_almost_everywhere.md); includes approximate/misspecification bounds, [L2](readable/jargon_l2.md)/[RMSE](readable/jargon_rmse.md) mean and SD bounds, and a triangle-inequality lemma for chaining approximations; uses `Transport`.

## Identification and design

- [ConjointSD/ConjointIdentification.lean](readable/ConjointIdentification.md) formalizes conjoint identification assumptions and derives observed-[mean](readable/jargon_mean.md) identification of [potential outcomes](readable/jargon_potential_outcome.md) and [AMCE](readable/jargon_amce.md); defines `gExp`/`gPot` equality under assumptions.
- [ConjointSD/StatusConjointDesign.lean](readable/StatusConjointDesign.md) encodes the specific status-conjoint randomization (uniform over [profiles](readable/jargon_profile.md)/tasks) and proves it satisfies `ConjointIdRandomized`, plus an explicit positivity lemma for assignments.
- [ConjointSD/StatusSurveyWeights.lean](readable/StatusSurveyWeights.md) introduces status-conjoint survey-weight placeholders and links weighted SD targets to target human population SDs under moment matching.

## Estimation and sequential consistency

- [ConjointSD/EstimatedG.lean](readable/EstimatedG.md) derives [variance](readable/jargon_variance.md)/[SD](readable/jargon_standard_deviation.md) [convergence](readable/jargon_convergence.md) from `GEstimationAssumptions` (now in `Assumptions.lean`) and the plug-in score `gHat` (now in `Defs.lean`).
- [ConjointSD/SampleSplitting.lean](readable/SampleSplitting.md) proves evaluation-stage [SD](readable/jargon_standard_deviation.md) [convergence](readable/jargon_convergence.md) for fixed training index `m` using `SDDecompositionFromConjoint`, `DesignAttributeBridge`, and `EstimatedG`.
- [ConjointSD/SequentialConsistency.lean](readable/SequentialConsistency.md) defines `sdEst`, training error, and total error; proves [sequential consistency](readable/jargon_sequential_consistency.md) (m then n) using `SampleSplitting` and `EstimatedG`.
- [ConjointSD/DecompositionSequentialConsistency.lean](readable/DecompositionSequentialConsistency.md) lifts [sequential consistency](readable/jargon_sequential_consistency.md) to [block](readable/jargon_block.md) scores and total scores (single `M` for all blocks); uses `SequentialConsistency`, `SampleSplitting`, `EstimatedG`, and `Transport`.

## [Regression](readable/jargon_regression.md)/continuity bridge (Route 2)

- [ConjointSD/RegressionConsistencyBridge.lean](readable/RegressionConsistencyBridge.md) derives `GEstimationAssumptions` from `θhat -> θ0` and functional continuity assumptions defined in `Assumptions.lean`; also provides [block](readable/jargon_block.md) versions.
- [ConjointSD/DeriveGEstimationAssumptions.lean](readable/DeriveGEstimationAssumptions.md) thin wrappers that produce `GEstimationAssumptions` (and block versions) from `θhat -> θ0` + continuity; depends on `RegressionConsistencyBridge`.
- [ConjointSD/RegressionEstimator.lean](readable/RegressionEstimator.md) formalizes the [OLS](readable/jargon_ols.md)-style [estimator](readable/jargon_estimator.md) sequence and bridges [estimator](readable/jargon_estimator.md) [consistency](readable/jargon_consistency.md) to `GEstimationAssumptions`; assumption packages now live in `Assumptions.lean`.
- [ConjointSD/PaperOLSConsistency.lean](readable/PaperOLSConsistency.md) specializes the [OLS](readable/jargon_ols.md) [estimator](readable/jargon_estimator.md) to the paper [term](readable/jargon_term.md) set and causal target `gStar`, providing [a.e.](readable/jargon_almost_everywhere.md) and deterministic bridges to `GEstimationAssumptions`, plus a bridge from `gPaper` to the block-sum total score (via `gTotalΘ`).

## Model/[term](readable/jargon_term.md)/[block](readable/jargon_block.md) bridges

- [ConjointSD/ModelBridge.lean](readable/ModelBridge.md) defines [block](readable/jargon_block.md) allocation `gBlockTerm` and bridges well-specification/approximation to [block](readable/jargon_block.md) sums; core definitions (`gLin`, paper term set) are in `Defs.lean`, and well-specification definitions now live in `ModelBridge.lean`.
- [ConjointSD/WellSpecifiedFromNoInteractions.lean](readable/WellSpecifiedFromNoInteractions.md) shows an additive/no-interactions causal [estimand](readable/jargon_estimand.md) implies `WellSpecified` for a [linear model](readable/jargon_linear_model.md)-in-[terms](readable/jargon_term.md) model; depends on `ModelBridge`.
- [ConjointSD/TermModelBlocks.lean](readable/TermModelBlocks.md) defines the [block](readable/jargon_block.md)-score model `gBTerm` induced by [term](readable/jargon_term.md) coefficients; proves a [block](readable/jargon_block.md)-specification lemma; depends on `PaperWrappers` (for the wrapper APIs).
- [ConjointSD/TrueBlockEstimand.lean](readable/TrueBlockEstimand.md) defines the “true [block](readable/jargon_block.md) score” from a [term](readable/jargon_term.md) model and proves [convergence](readable/jargon_convergence.md) statements to those targets; depends on `TermModelBlocks` and [sequential consistency](readable/jargon_sequential_consistency.md) wrappers.

## Paper-facing wrappers and estimands

- [ConjointSD/PaperWrappers.lean](readable/PaperWrappers.md) presents paper-friendly theorems: identification, model-to-[block](readable/jargon_block.md) decomposition, route-2 [sequential consistency](readable/jargon_sequential_consistency.md), target-equivalence wrappers (exact and approximate, including two-stage oracle bounds), weighted-target transfer lemmas, `hGTotal`-based total-score variants, and [OLS](readable/jargon_ols.md)-based links from paper regressions into the SD-consistency chain; central hub for exported statements.
- [ConjointSD/PaperCoreEstimand.lean](readable/PaperCoreEstimand.md) defines the paper’s core [estimands](readable/jargon_estimand.md) ([block](readable/jargon_block.md)/total [SDs](readable/jargon_standard_deviation.md)) and main [estimator](readable/jargon_estimator.md); combines `TrueBlockEstimand`, `PaperWrappers`, `SurveyWeights`, and [block](readable/jargon_block.md)-[term](readable/jargon_term.md) machinery (including weighted target-human-population SD targets).

## Tooling


## Scratchpad

- [Scratch.lean](readable/Scratch.md) is a local scratch file that prints key structures/theorems for inspection; no production dependencies.
