# Assumptions.lean

Lean file: [ConjointSD/Assumptions.lean](../ConjointSD/Assumptions.lean)

This file gathers all assumption bundles and assumption-level props in a single place
for auditability. Below is a detailed, assumption-by-assumption explanation of what
each package is asserting and why it matters.

The file depends on shared definitions in `ConjointSD/Defs.lean`.

Recent changes: removed unused transport bundles and a block-decomposition package.

## Transport

- `PopulationMomentAssumptions`: first- and [second moment](jargon_second_moment.md)
  existence for a score
  function `s` under a [population](jargon_population.md) measure `ν`, expressed
  as [integrable](jargon_integrable.md) `s` and `s^2`. This is the minimal setup
  for defining [population](jargon_population.md) [mean](jargon_mean.md),
  [variance](jargon_variance.md), and
  [standard deviation](jargon_standard_deviation.md) targets.
- `InvarianceAE`: almost-everywhere equality under `ν`, i.e., the experimental and
  [population](jargon_population.md) scores agree on the
  [population](jargon_population.md) support.

## PredictedSD

- `IIDAssumptions`: [IID](jargon_iid.md) and moment assumptions for a sequence
  `Z`. Requires [independent](jargon_independent.md) and
  [identically distributed](jargon_identically_distributed.md) draws, plus
  [integrability](jargon_integrable.md) of `Z 0` and `(Z 0)^2`. This is the
  standard input for a strong
  law for both the [mean](jargon_mean.md) and
  [second moment](jargon_second_moment.md), which
  delivers SD [consistency](jargon_consistency.md).

## SDDecomposition

- `PopIID`: i.i.d.-style conditions for the attribute process `A n`. Requires
  [measurable](jargon_measurable.md) `A i`, pairwise
  [independence](jargon_independent.md), and
  [identical distribution](jargon_identically_distributed.md) across `i`.
- `ScoreAssumptions`: combines `PopIID` with
  [measurability](jargon_measurable.md) of the score function `g`, plus
  [integrability](jargon_integrable.md) of `g(A 0)` and `g(A 0)^2`. This is the
  input needed to apply the [standard deviation](jargon_standard_deviation.md)
  law of large numbers to the induced score process.
- `DecompAssumptions`: bundles `PopIID`, [measurability](jargon_measurable.md) of
  each
  [block](jargon_block.md) score `g b`, and a uniform boundedness condition for
  every block. Boundedness guarantees all required moments and simplifies
  [variance](jargon_variance.md) decomposition arguments.

## VarianceDecomposition

- `BlockIntegrable`: [integrability](jargon_integrable.md) of each block score
  `g b(A 0)` and every product `g b(A 0) * g c(A 0)`. These are the minimal
  conditions to define block [means](jargon_mean.md) and
  [covariances](jargon_covariance.md) used in
  [variance](jargon_variance.md) decomposition.

## EstimatedG

- `GEstimationAssumptions`: [convergence](jargon_convergence.md) of
  [population](jargon_population.md) [mean](jargon_mean.md) and
  [second moment](jargon_second_moment.md) when
  replacing
  [oracle](jargon_oracle.md) `g θ0` with estimated `g (θhat n)`. This assumption
  is framed directly on the [population](jargon_population.md) functionals so
  [standard deviation](jargon_standard_deviation.md) and
  [variance](jargon_variance.md) [consistency](jargon_consistency.md) follow by
  algebra.

## SampleSplitting

- `SplitEvalAssumptions`: applies `ScoreAssumptions` to the evaluation score
  `gHat g θhat m` on the evaluation sample `A n`. This is the standard setup for
  showing the empirical [standard deviation](jargon_standard_deviation.md) of
  the estimated score [converges](jargon_convergence.md) to its
  [population](jargon_population.md) SD.
- `SplitEvalAssumptionsBounded`: alternative evaluation assumptions using
  `PopIID`, [measurability](jargon_measurable.md) of `gHat g θhat m`, and a
  global bound. This is a stronger but easier-to-check route to the same moment
  conditions.

## RegressionConsistencyBridge

- `FunctionalContinuityAssumptions`: [continuity](jargon_continuity.md) at `θ0`
  of the [population](jargon_population.md) [mean](jargon_mean.md) and
  [second moment](jargon_second_moment.md)
  functionals. These are the continuity inputs that let
  [regression](jargon_regression.md) [consistency](jargon_consistency.md)
  translate estimator [convergence](jargon_convergence.md) into moment
  [convergence](jargon_convergence.md).
- `BlockFunctionalContinuityAssumptions`: the blockwise version of functional
  continuity, requiring the above assumptions for each block score.

## RegressionEstimator

- `OLSConsistencyAssumptions`: a single assumption that the
  [OLS](jargon_ols.md) [estimator](jargon_estimator.md) sequence
  [converges](jargon_convergence.md) to the target `θ0`.
- `OLSMomentAssumptions`: a deterministic moment-limit package. It posits limits
  for the inverse Gram matrix and cross-product vector and states that `θ0`
  solves the limiting normal equations. This is the generic,
  non-[population](jargon_population.md) formulation.
- `OLSMomentAssumptionsOfPop`: the [population](jargon_population.md) version of
  the above, with the limits pinned to the
  [population](jargon_population.md) Gram and cross moments.
  This is the standard LLN + identifiability package for [OLS](jargon_ols.md).

## SurveyWeights

- `WeightAssumptions`: nonnegativity of weights a.e.,
  [integrability](jargon_integrable.md) of `w`, `w*s`, and `w*s^2`, plus strictly
  positive total weight. Together these ensure weighted moments
  ([mean](jargon_mean.md), [variance](jargon_variance.md),
  [standard deviation](jargon_standard_deviation.md)) are well-defined and
  nondegenerate.

## ConjointIdentification

- `ConjointIdAssumptions`: [measurability](jargon_measurable.md) of the observed
  and [potential outcomes](jargon_potential_outcome.md),
  [consistency](jargon_consistency.md) (`Yobs = Y(X)`), positivity of assignment,
  and a factorization condition (`rand`) that makes the
  [mean](jargon_mean.md) of `Y x` invariant to conditioning on `X = x0`. This is
  written to avoid explicit conditional expectations.
- `ConjointIdRandomized`: a randomized-design variant that assumes
  [measurable](jargon_measurable.md) assignment,
  [integrable](jargon_integrable.md) and uniformly bounded
  [potential outcomes](jargon_potential_outcome.md), positivity, and
  [independence](jargon_independent.md) between `X` and each `Y x`. These
  assumptions imply the `rand` factorization above.
- `ConjointSingleShotDesign`: a single-shot assignment law `ν` with positive mass
  on each [profile](jargon_profile.md), [measurable](jargon_measurable.md)
  assignment `X` with `Measure.map X μ = ν`, and bounded, measurable, consistent
  [potential outcomes](jargon_potential_outcome.md). Together with design
  [independence](jargon_independent.md), this implies `ConjointIdRandomized`.

## ModelBridge

- `WellSpecified`: exact [well-specified](jargon_well_specified.md): the causal
  estimand `gStar` equals the
  [linear-in-terms](jargon_linear_in_terms.md) model `gLin` for all
  [profiles](jargon_profile.md).
- `ApproxWellSpecified`: uniform approximation by `gLin`, with a fixed error
  tolerance `ε` at every [profile](jargon_profile.md).
- `ApproxWellSpecifiedAE`: the same approximation requirement, but only
  [almost everywhere](jargon_almost_everywhere.md) under a
  [population](jargon_population.md) measure.
- `ApproxOracleAE`: a two-stage approximation assumption: a flexible score
  approximates the true target `gStar`, and the model score approximates the
  flexible score, both [almost everywhere](jargon_almost_everywhere.md).
- `L2Approx`: an [L2](jargon_l2.md)/RMSE-style approximation assumption: the model score differs
  from the target by at most `δ` in mean-square (uses the [L2](jargon_l2.md) norm under `ν`).
- `ParametricMainInteractions`: the paper's parametric assumption that `gStar`
  is exactly an intercept plus the specified main effects and listed
  [interactions](jargon_interaction.md).

## WellSpecifiedFromNoInteractions

- `NoInteractions`: existence of an additive representation, formalizing the
  "no interactions" assumption used to justify
  [well-specification](jargon_well_specified.md).

## PaperOLSConsistency

- `PaperOLSLLNA`: entrywise law of large numbers for the sample Gram matrix and
  cross moment vector, [converging](jargon_convergence.md) to
  [population](jargon_population.md) targets for the paper basis.
- `PaperOLSInverseStability`: stability of the inverse Gram entries, ensuring
  [convergence](jargon_convergence.md) of the sample inverse to the
  [population](jargon_population.md) inverse.
- `PaperOLSIdentifiability`: the normal equations with
  [population](jargon_population.md) moments identify the target
  [parameter](jargon_parameter.md) `θ0`.
- `PaperOLSMomentAssumptions`: almost-everywhere (over sample paths) version of
  the [population](jargon_population.md) moment assumptions, applied to the
  realized sample sequences.
