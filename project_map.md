# ConjointSD project map

This map summarizes each `.lean` file and how it connects to the rest of the project.

## Top-level entry

- `ConjointSD.lean` imports the main theory files in a single module for downstream use.

## Core probability/SD machinery

- `ConjointSD/PredictedSD.lean` defines empirical/population mean, second moment, variance, and SD for a real-valued process; proves SLLN-based consistency `sdHatZ -> popSDZ`.
- `ConjointSD/SDDecompositionFromConjoint.lean` lifts `PredictedSD` to conjoint scores: defines population IID assumptions for attributes, score assumptions, and SD consistency for single scores and block families.
- `ConjointSD/VarianceDecompositionFromBlocks.lean` defines block-total scores and proves a variance proxy decomposition into sums of covariances; relies on block scores from `SDDecompositionFromConjoint`.

## Population targets and transport

- `ConjointSD/Transport.lean` defines population moment/SD functionals under a target distribution `ν` and transport assumptions (`Overlap`, `InvarianceAE`).
- `ConjointSD/PopulationBridge.lean` bridges moments under `μ` for `g(A0)` to moments under `ν` for `g`; uses `Transport` and `SDDecompositionFromConjoint`.
- `ConjointSD/OracleSDConsistency.lean` restates SD consistency with the `popSDAttr ν g` target using `SDDecompositionFromConjoint` + `PopulationBridge`.
- `ConjointSD/SurveyWeights.lean` adds weighted population estimands and finite-population targets; builds on `Transport`.
- `ConjointSD/TargetEquivalence.lean` shows population moments/SDs are equal when scores agree `ν`-a.e.; includes approximate/misspecification bounds; uses `Transport`.

## Identification and design

- `ConjointSD/ConjointIdentification.lean` formalizes conjoint identification assumptions and derives observed-mean identification of potential outcomes and AMCE; defines `gExp`/`gPot` equality under assumptions.
- `ConjointSD/StatusConjointDesign.lean` encodes the specific status-conjoint randomization (uniform over profiles/tasks) and proves it satisfies `ConjointSingleShotDesign` from `ConjointIdentification`.

## Estimation and sequential consistency

- `ConjointSD/EstimatedG.lean` defines plug-in score `gHat` and `GEstimationAssumptions` (mean/m2 convergence); derives variance/SD convergence; depends on `Transport`.
- `ConjointSD/SampleSplitting.lean` proves evaluation-stage SD convergence for fixed training index `m` using `OracleSDConsistency` and `EstimatedG`.
- `ConjointSD/SequentialConsistency.lean` defines `sdEst`, training error, and total error; proves sequential consistency (m then n) using `SampleSplitting` and `EstimatedG`.
- `ConjointSD/DecompositionSequentialConsistency.lean` lifts sequential consistency to block scores and total scores (single `M` for all blocks); uses `SequentialConsistency`, `SampleSplitting`, `EstimatedG`, and `Transport`.

## Regression/continuity bridge (Route 2)

- `ConjointSD/RegressionConsistencyBridge.lean` introduces functional continuity assumptions and derives `GEstimationAssumptions` from `θhat -> θ0`; also provides block versions.
- `ConjointSD/FunctionalContinuityAssumptions.lean` provides helper lemmas to extract continuity and derive moment convergence without relying on field names; builds on `RegressionConsistencyBridge` and `Transport`.
- `ConjointSD/DeriveGEstimationAssumptions.lean` thin wrappers that produce `GEstimationAssumptions` (and block versions) from `θhat -> θ0` + continuity; depends on `RegressionConsistencyBridge`.
- `ConjointSD/RegressionEstimator.lean` formalizes the OLS-style estimator sequence and bridges estimator consistency to `GEstimationAssumptions`; uses `ModelBridge` and `RegressionConsistencyBridge`.

## Model/term/block bridges

- `ConjointSD/ModelBridge.lean` defines linear-in-terms score `gLin`, block allocation `gBlockTerm`, and bridges well-specification/approximation to block sums; includes the paper’s parametric term set.
- `ConjointSD/WellSpecifiedFromNoInteractions.lean` shows an additive/no-interactions causal estimand implies `WellSpecified` for a linear-in-terms model; depends on `ModelBridge`.
- `ConjointSD/TermModelBlocks.lean` defines the block-score model `gBTerm` induced by term coefficients; proves a block-specification lemma; depends on `PaperWrappers` (for the wrapper APIs).
- `ConjointSD/TrueBlockEstimand.lean` defines the “true block score” from a term model and proves convergence statements to those targets; depends on `TermModelBlocks` and sequential-consistency wrappers.

## Paper-facing wrappers and estimands

- `ConjointSD/PaperWrappers.lean` presents paper-friendly theorems: identification, model-to-block decomposition, route-2 sequential consistency, and target-equivalence wrappers; central hub for exported statements.
- `ConjointSD/PaperCoreEstimand.lean` defines the paper’s core estimands (block/total SDs) and main estimator; combines `TrueBlockEstimand`, `PaperWrappers`, and block-term machinery.
- `ConjointSD/FinalCleanEstimate.lean` collects clean plug-in convergence statements for population moments/SD under `ν`; uses `EstimatedG` and `Transport`.

## Scratchpad

- `Scratch.lean` is a local scratch file that prints key structures/theorems for inspection; no production dependencies.
