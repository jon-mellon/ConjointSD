# ConjointSD project map

This map summarizes each `.lean` file and how it connects to the rest of the project.

## Top-level entry

- `ConjointSD.lean` imports the main theory files in a single module for downstream use.

## Core probability/SD machinery

- `ConjointSD/PredictedSD.lean` defines empirical/[population](readable/jargon_population.md) [mean](readable/jargon_mean.md), [second moment](readable/jargon_second_moment.md), [variance](readable/jargon_variance.md), and [SD](readable/jargon_standard_deviation.md) for a real-valued process; proves SLLN-based [consistency](readable/jargon_consistency.md) `sdHatZ -> popSDZ`.
- `ConjointSD/SDDecompositionFromConjoint.lean` lifts `PredictedSD` to conjoint scores: defines [population](readable/jargon_population.md) [IID](readable/jargon_iid.md) assumptions for attributes, score assumptions, and [SD](readable/jargon_standard_deviation.md) [consistency](readable/jargon_consistency.md) for single scores and [block](readable/jargon_block.md) families.
- `ConjointSD/VarianceDecompositionFromBlocks.lean` defines [block](readable/jargon_block.md)-total scores and proves a [variance](readable/jargon_variance.md) proxy decomposition into sums of [covariances](readable/jargon_covariance.md); relies on [block](readable/jargon_block.md) scores from `SDDecompositionFromConjoint`.

## Population targets and transport

- `ConjointSD/Transport.lean` defines [population](readable/jargon_population.md) moment/[SD](readable/jargon_standard_deviation.md) functionals under a target [distribution](readable/jargon_distribution.md) `ν` and transport assumptions (`Overlap`, `InvarianceAE`).
- `ConjointSD/PopulationBridge.lean` bridges moments under `μ` for `g(A0)` to moments under `ν` for `g`; uses `Transport` and `SDDecompositionFromConjoint`.
- `ConjointSD/OracleSDConsistency.lean` restates [SD](readable/jargon_standard_deviation.md) [consistency](readable/jargon_consistency.md) with the `popSDAttr ν g` target using `SDDecompositionFromConjoint` + `PopulationBridge`.
- `ConjointSD/SurveyWeights.lean` adds weighted [population](readable/jargon_population.md) estimands and finite-[population](readable/jargon_population.md) targets; builds on `Transport`.
- `ConjointSD/TargetEquivalence.lean` shows [population](readable/jargon_population.md) moments/[SDs](readable/jargon_standard_deviation.md) are equal when scores agree `ν`-[a.e.](readable/jargon_almost_everywhere.md); includes approximate/misspecification bounds; uses `Transport`.

## Identification and design

- `ConjointSD/ConjointIdentification.lean` formalizes conjoint identification assumptions and derives observed-[mean](readable/jargon_mean.md) identification of [potential outcomes](readable/jargon_potential_outcome.md) and AMCE; defines `gExp`/`gPot` equality under assumptions.
- `ConjointSD/StatusConjointDesign.lean` encodes the specific status-conjoint randomization (uniform over [profiles](readable/jargon_profile.md)/tasks) and proves it satisfies `ConjointSingleShotDesign` from `ConjointIdentification`.

## Estimation and sequential consistency

- `ConjointSD/EstimatedG.lean` defines plug-in score `gHat` and `GEstimationAssumptions` ([mean](readable/jargon_mean.md)/[second moment](readable/jargon_second_moment.md) [convergence](readable/jargon_convergence.md)); derives [variance](readable/jargon_variance.md)/[SD](readable/jargon_standard_deviation.md) [convergence](readable/jargon_convergence.md); depends on `Transport`.
- `ConjointSD/SampleSplitting.lean` proves evaluation-stage [SD](readable/jargon_standard_deviation.md) [convergence](readable/jargon_convergence.md) for fixed training index `m` using `OracleSDConsistency` and `EstimatedG`.
- `ConjointSD/SequentialConsistency.lean` defines `sdEst`, training error, and total error; proves [sequential consistency](readable/jargon_sequential_consistency.md) (m then n) using `SampleSplitting` and `EstimatedG`.
- `ConjointSD/DecompositionSequentialConsistency.lean` lifts [sequential consistency](readable/jargon_sequential_consistency.md) to [block](readable/jargon_block.md) scores and total scores (single `M` for all blocks); uses `SequentialConsistency`, `SampleSplitting`, `EstimatedG`, and `Transport`.

## [Regression](readable/jargon_regression.md)/continuity bridge (Route 2)

- `ConjointSD/RegressionConsistencyBridge.lean` introduces functional continuity assumptions and derives `GEstimationAssumptions` from `θhat -> θ0`; also provides [block](readable/jargon_block.md) versions.
- `ConjointSD/FunctionalContinuityAssumptions.lean` provides helper lemmas to extract continuity and derive moment [convergence](readable/jargon_convergence.md) without relying on field names; builds on `RegressionConsistencyBridge` and `Transport`.
- `ConjointSD/DeriveGEstimationAssumptions.lean` thin wrappers that produce `GEstimationAssumptions` (and block versions) from `θhat -> θ0` + continuity; depends on `RegressionConsistencyBridge`.
- `ConjointSD/RegressionEstimator.lean` formalizes the [OLS](readable/jargon_ols.md)-style [estimator](readable/jargon_estimator.md) sequence and bridges [estimator](readable/jargon_estimator.md) [consistency](readable/jargon_consistency.md) to `GEstimationAssumptions`; uses `ModelBridge` and `RegressionConsistencyBridge`.
- `ConjointSD/PaperOLSConsistency.lean` specializes the [OLS](readable/jargon_ols.md) [estimator](readable/jargon_estimator.md) to the paper [term](readable/jargon_term.md) set and causal target `gStar`, providing [a.e.](readable/jargon_almost_everywhere.md) and deterministic bridges to `GEstimationAssumptions`.

## Model/[term](readable/jargon_term.md)/[block](readable/jargon_block.md) bridges

- `ConjointSD/ModelBridge.lean` defines [linear-model](readable/jargon_linear_model.md)-in-[terms](readable/jargon_term.md) score `gLin`, [block](readable/jargon_block.md) allocation `gBlockTerm`, and bridges well-specification/approximation to [block](readable/jargon_block.md) sums; includes the paper’s parametric [term](readable/jargon_term.md) set.
- `ConjointSD/WellSpecifiedFromNoInteractions.lean` shows an additive/no-interactions causal estimand implies `WellSpecified` for a [linear model](readable/jargon_linear_model.md)-in-[terms](readable/jargon_term.md) model; depends on `ModelBridge`.
- `ConjointSD/TermModelBlocks.lean` defines the [block](readable/jargon_block.md)-score model `gBTerm` induced by [term](readable/jargon_term.md) coefficients; proves a [block](readable/jargon_block.md)-specification lemma; depends on `PaperWrappers` (for the wrapper APIs).
- `ConjointSD/TrueBlockEstimand.lean` defines the “true [block](readable/jargon_block.md) score” from a [term](readable/jargon_term.md) model and proves [convergence](readable/jargon_convergence.md) statements to those targets; depends on `TermModelBlocks` and [sequential consistency](readable/jargon_sequential_consistency.md) wrappers.

## Paper-facing wrappers and estimands

- `ConjointSD/PaperWrappers.lean` presents paper-friendly theorems: identification, model-to-[block](readable/jargon_block.md) decomposition, route-2 [sequential consistency](readable/jargon_sequential_consistency.md), and target-equivalence wrappers; central hub for exported statements.
- `ConjointSD/PaperCoreEstimand.lean` defines the paper’s core estimands ([block](readable/jargon_block.md)/total [SDs](readable/jargon_standard_deviation.md)) and main [estimator](readable/jargon_estimator.md); combines `TrueBlockEstimand`, `PaperWrappers`, and [block](readable/jargon_block.md)-[term](readable/jargon_term.md) machinery.
- `ConjointSD/FinalCleanEstimate.lean` collects clean plug-in [convergence](readable/jargon_convergence.md) statements for [population](readable/jargon_population.md) moments/[SD](readable/jargon_standard_deviation.md) under `ν`; uses `EstimatedG` and `Transport`.

## Scratchpad

- `Scratch.lean` is a local scratch file that prints key structures/theorems for inspection; no production dependencies.
