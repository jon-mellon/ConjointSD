# ConjointSD project map

This map links to the readable summaries for each `.lean` file and how it connects to the rest of the project.

## Top-level entry

- [ConjointSD.lean](readable/ConjointSD.md) imports the main theory files in a single module for downstream use.

## Shared definitions and assumptions

- [ConjointSD/Defs.lean](readable/Defs.md) centralizes core definitions used across the project (attribute-distribution/experimental-design moments for the target human [population](readable/jargon_population.md), [plug-in](readable/jargon_plug_in.md) scores, [OLS](readable/jargon_ols.md) helpers, and conjoint primitives).
- [ConjointSD/Assumptions.lean](readable/Assumptions.md) collects assumption bundles used in the main theorem chain (transport, [IID](readable/jargon_iid.md)/score, [regression](readable/jargon_regression.md)/[OLS](readable/jargon_ols.md), identification, and paper-specific packages).
- [ConjointSD/ApproxAssumptions.lean](readable/ApproxAssumptions.md) isolates approximation-only assumptions (approximate invariance/oracles and approximate additivity) used by the misspecification modules.
- [ConjointSD/IdentificationAssumptions.lean](readable/IdentificationAssumptions.md) isolates identification-only randomized-design assumptions (`ConjointIdRandomized`).

## Core probability/SD machinery

- [ConjointSD/PredictedSD.lean](readable/PredictedSD.md) defines empirical/experimental-design [mean](readable/jargon_mean.md), [second moment](readable/jargon_second_moment.md), [variance](readable/jargon_variance.md), and [SD](readable/jargon_standard_deviation.md) for a real-valued process, plus basic measurability helpers; LLN-based SD consistency now lives in the score-based pipeline.
- [ConjointSD/SDDecompositionFromConjoint.lean](readable/SDDecompositionFromConjoint.md) lifts `PredictedSD` to conjoint scores and proves [SD](readable/jargon_standard_deviation.md) [consistency](readable/jargon_consistency.md) for single scores and [block](readable/jargon_block.md) families using assumption bundles from `Assumptions.lean`.
- [ConjointSD/VarianceDecompositionFromBlocks.lean](readable/VarianceDecompositionFromBlocks.md) defines [block](readable/jargon_block.md)-total scores and proves a [variance](readable/jargon_variance.md) proxy decomposition into sums of [covariances](readable/jargon_covariance.md); relies on [block](readable/jargon_block.md) scores from `SDDecompositionFromConjoint`.

## Population targets and transport

- [ConjointSD/Transport.lean](readable/Transport.md) gathers attribute-distribution functionals/assumptions from `Defs.lean`/`Assumptions.lean`.
- [ConjointSD/EvalSamplingSRS.lean](readable/EvalSamplingSRS.md) derives the weighted-moment assumption from an SRS evaluation law and uniform weights.
- [ConjointSD/SubjectSamplingLLNFromIID.lean](readable/SubjectSamplingLLNFromIID.md) derives the subject-sampling LLN to `gPop` from IID subject sampling and score regularity, and builds `SubjectSamplingLLN` using the assumed `SubjectSamplingLLNStar`.
- [ConjointSD/DesignAttributeBridge.lean](readable/DesignAttributeBridge.md) bridges moments under `μ` for `g(A0)` to moments under the pushforward attribute law `kappaDesign := Measure.map (A 0) μ` for `g`; uses `Transport` and `SDDecompositionFromConjoint`.
- [ConjointSD/TargetEquivalence.lean](readable/TargetEquivalence.md) shows target human [population](readable/jargon_population.md) moments/[SDs](readable/jargon_standard_deviation.md) are equal when scores agree `ν`-[a.e.](readable/jargon_almost_everywhere.md); uses `Transport`.
- [ConjointSD/ApproxTargetEquivalence.lean](readable/ApproxTargetEquivalence.md) collects approximate/misspecification bounds (triangle inequality and moment/SD bounds) under `ApproxInvarianceAE`/`L2Approx` plus `BoundedAE`.

## Identification and design

- [ConjointSD/ConjointIdentification.lean](readable/ConjointIdentification.md) formalizes conjoint identification assumptions and derives observed-[mean](readable/jargon_mean.md) identification of [potential outcomes](readable/jargon_potential_outcome.md) and [AMCE](readable/jargon_amce.md); defines `gExp` for score-level identification statements.
- [ConjointSD/StatusConjointDesign.lean](readable/StatusConjointDesign.md) encodes the specific status-conjoint randomization (uniform over [profiles](readable/jargon_profile.md)/tasks) and proves it satisfies `ConjointIdRandomized`, plus an explicit positivity lemma for assignments.
- [ConjointSD/IdentificationTheorems.lean](readable/IdentificationTheorems.md) packages the paper-facing identification wrappers for conditional means and the status conjoint; not used in the main SD theorem chain.

## Estimation and sequential consistency

- [ConjointSD/EstimatedG.lean](readable/EstimatedG.md) derives [variance](readable/jargon_variance.md)/[SD](readable/jargon_standard_deviation.md) [convergence](readable/jargon_convergence.md) from plug‑in mean/second‑moment convergence and the plug-in score `gHat` (now in `Defs.lean`).
- [ConjointSD/SampleSplitting.lean](readable/SampleSplitting.md) proves evaluation-stage [SD](readable/jargon_standard_deviation.md) [convergence](readable/jargon_convergence.md) for fixed training index `m` using `SDDecompositionFromConjoint`, `DesignAttributeBridge`, and `EstimatedG`.
- [ConjointSD/SequentialConsistency.lean](readable/SequentialConsistency.md) defines `sdEst`, training error, and total error; proves [sequential consistency](readable/jargon_sequential_consistency.md) (m then n) using `SampleSplitting` and `EstimatedG`.
- [ConjointSD/DecompositionSequentialConsistency.lean](readable/DecompositionSequentialConsistency.md) lifts [sequential consistency](readable/jargon_sequential_consistency.md) to [block](readable/jargon_block.md) scores and total scores (single `M` for all blocks); uses `SequentialConsistency`, `SampleSplitting`, `EstimatedG`, and `Transport`.

## [Regression](readable/jargon_regression.md)/continuity bridge (Route 2)

- [ConjointSD/RegressionConsistencyBridge.lean](readable/RegressionConsistencyBridge.md) derives plug‑in mean/second‑moment convergence from `θhat -> θ0` and functional continuity assumptions; also derives continuity for linear-in-terms scores from bounded features and provides [block](readable/jargon_block.md) versions.
- [ConjointSD/DeriveGEstimationAssumptions.lean](readable/DeriveGEstimationAssumptions.md) thin wrappers that produce plug‑in mean/second‑moment convergence (and block versions) from `θhat -> θ0` + continuity; depends on `RegressionConsistencyBridge`.
- [ConjointSD/RegressionEstimator.lean](readable/RegressionEstimator.md) formalizes the [OLS](readable/jargon_ols.md)-style [estimator](readable/jargon_estimator.md) sequence and bridges [estimator](readable/jargon_estimator.md) [consistency](readable/jargon_consistency.md) to plug‑in moment convergence; assumption packages now live in `Assumptions.lean`.
- [ConjointSD/PaperOLSConsistency.lean](readable/PaperOLSConsistency.md) specializes the [OLS](readable/jargon_ols.md) [estimator](readable/jargon_estimator.md) to the paper [term](readable/jargon_term.md) set and causal target `gStar`, providing [a.e.](readable/jargon_almost_everywhere.md) and deterministic bridges to plug‑in moment convergence, plus a bridge from `gPaper` to the block-sum total score (via `gTotalΘ`).

## Model/[term](readable/jargon_term.md)/[block](readable/jargon_block.md) bridges

- [ConjointSD/ModelBridge.lean](readable/ModelBridge.md) defines [block](readable/jargon_block.md) allocation `gBlockTerm` and bridges well-specification to [block](readable/jargon_block.md) sums; core definitions (`gLin`, paper term set) are in `Defs.lean`, and well-specification definitions live in `ModelBridge.lean`.
- [ConjointSD/ApproxModelBridge.lean](readable/ApproxModelBridge.md) provides approximate well-specification definitions and the ν-a.e. approximation bridge to block sums.
- [ConjointSD/WellSpecifiedFromNoInteractions.lean](readable/WellSpecifiedFromNoInteractions.md) shows an additive/no-interactions causal [estimand](readable/jargon_estimand.md) implies `WellSpecified` for a [linear model](readable/jargon_linear_model.md)-in-[terms](readable/jargon_term.md) model; depends on `ModelBridge`.
- [ConjointSD/ApproxWellSpecifiedFromNoInteractions.lean](readable/ApproxWellSpecifiedFromNoInteractions.md) derives approximate well-specification from `ApproxNoInteractions` and `FullMainEffectsTerms`.
- [ConjointSD/TermModelBlocks.lean](readable/TermModelBlocks.md) is currently a placeholder for term-to-block model notes; depends on `PaperWrappers` (for the wrapper APIs).
- [ConjointSD/TrueBlockEstimand.lean](readable/TrueBlockEstimand.md) defines the “true [block](readable/jargon_block.md) score” from a [term](readable/jargon_term.md) model and proves [convergence](readable/jargon_convergence.md) statements to those targets; depends on `TermModelBlocks` and [sequential consistency](readable/jargon_sequential_consistency.md) wrappers.

## Paper-facing wrappers and estimands

- [ConjointSD/PaperWrappers.lean](readable/PaperWrappers.md) presents paper-friendly theorems: model-to-[block](readable/jargon_block.md) decomposition, route-2 [sequential consistency](readable/jargon_sequential_consistency.md), exact target-equivalence wrappers, weighted-target transfer lemmas, and [OLS](readable/jargon_ols.md)-based links from paper regressions into the SD-consistency chain; now also depends on `SampleSplitting` to derive evaluation IID from randomization; central hub for exported statements.
- [ConjointSD/ApproxPaperWrappers.lean](readable/ApproxPaperWrappers.md) hosts approximate/misspecified variants of the paper-facing SD wrappers (approximate targets, ApproxWellSpecifiedAE, and oracle bounds).
- [ConjointSD/PaperCoreEstimand.lean](readable/PaperCoreEstimand.md) defines the paper’s core [estimands](readable/jargon_estimand.md) ([block](readable/jargon_block.md)/total [SDs](readable/jargon_standard_deviation.md)) and main [estimator](readable/jargon_estimator.md); combines `TrueBlockEstimand`, `PaperWrappers`, and [block](readable/jargon_block.md)-[term](readable/jargon_term.md) machinery.

## Tooling


## Scratchpad

- [Scratch.lean](readable/Scratch.md) is a local scratch file that prints key structures/theorems for inspection; no production dependencies.
