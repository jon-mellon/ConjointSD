# Assumptions.lean

Lean file: [ConjointSD/Assumptions.lean](../ConjointSD/Assumptions.lean)

This file gathers all assumption bundles and assumption-level props in a single place
for auditability. Below is a detailed, assumption-by-assumption explanation of what
each package is asserting and why it matters.

The file depends on shared definitions in `ConjointSD/Defs.lean`.

Recent changes: added an explicit randomization-mechanism assumption for conjoint designs.

## Structural assumptions (by model choice)

These are not formalized as Lean assumption bundles; they arise from how the model is set up.

- Single-shot abstraction: each observation is treated as a standalone profile draw. This
  sidesteps any task-indexing or within-respondent carryover structure.
- No task-order effects: because there is no task index in the core model, the formalization
  does not represent profile order or task sequence effects.
- No attribute-order effects within a profile: profiles are abstract objects, so any ordering
  of attributes inside a profile is not represented.

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
  [population support](jargon_population_support.md). Intuitively, they may
  differ only on a set with zero probability under `ν`; this is the external
  validity/transport assumption that lets population targets be read off from
  the experimental score. Formally: `gExp = gPop` nu-a.e. (under `ν`). It does
  not by itself guarantee the fitted model
  matches that score; misspecification or estimation error can still break
  transfer. It also fails if the experimental setup elicits a different scoring
  rule than the real-world population process (beyond a ν-null set).

## PredictedSD

- `IIDAssumptions`: [IID](jargon_iid.md) and moment assumptions for a sequence
  `Z`. Requires [independent](jargon_independent.md) and
  [identically distributed](jargon_identically_distributed.md) draws, plus
  [integrability](jargon_integrable.md) of `Z 0` and `(Z 0)^2`. This is the
  standard input for a strong [LLN](jargon_lln.md)
  for both the [mean](jargon_mean.md) and
  [second moment](jargon_second_moment.md), which
  delivers SD [consistency](jargon_consistency.md).

## SDDecomposition

- `PopIID`: i.i.d.-style conditions for the attribute process `A n`. Requires
  [measurable](jargon_measurable.md) `A i`, pairwise
  [independence](jargon_independent.md), and
  [identical distribution](jargon_identically_distributed.md) across `i`. This
  is i.i.d. across the draw index (profiles/respondents/tasks), not within a
  profile, so attributes may still be correlated inside each profile.
- `ScoreAssumptions`: combines `PopIID` with
  [measurability](jargon_measurable.md) of the score function `g`, plus
  [integrability](jargon_integrable.md) of `g(A 0)` and `g(A 0)^2`. This is the
  input needed to apply the [standard deviation](jargon_standard_deviation.md)
  [LLN](jargon_lln.md) to the induced score process.
- `DecompAssumptions`: bundles `PopIID`, [measurability](jargon_measurable.md) of
  each
  [block](jargon_block.md) score `g b`, and a uniform boundedness condition for
  every block. Boundedness guarantees all required moments and simplifies
  [variance](jargon_variance.md) decomposition arguments. Concretely, there is
  a single constant `C` with `|g b(A i)| ≤ C` for all blocks `b` (and all draws
  `i`), so every block score is uniformly bounded. This gives integrability of
  each `g b` and every product `g b * g c`, ensures covariances exist, and lets
  you apply dominated-convergence or LLN-style steps without checking separate
  tail conditions for each block.

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
  This is the standard [LLN](jargon_lln.md) + identifiability package for [OLS](jargon_ols.md).

## SurveyWeights

- `WeightAssumptions`: nonnegativity of weights a.e.,
  [integrability](jargon_integrable.md) of `w`, `w*s`, and `w*s^2`, plus strictly
  positive total weight. Together these ensure weighted moments
  ([mean](jargon_mean.md), [variance](jargon_variance.md),
  [standard deviation](jargon_standard_deviation.md)) are well-defined and
  nondegenerate.
- `WeightMatchesPopMoments`: the weighted [mean](jargon_mean.md) and weighted
  [second moment](jargon_second_moment.md) match the population moments, a
  moment-matching condition used to transfer SD targets from the population to a
  weighted sample.

## ConjointIdentification

- `ConjointRandomizationMechanism`: models randomization explicitly by writing
  the assignment `X` as a measurable function of a randomization variable `U`
  that is [independent](jargon_independent.md) of every
  [potential outcome](jargon_potential_outcome.md). This is the mechanism-level
  assumption from which ignorability of `X` is derived later.
- `NoProfileOrderEffects`: formalizes Assumption 2 by requiring potential outcomes
  for a task to be invariant under permutations of the profile order.
- `ConjointIdAssumptions`: [measurability](jargon_measurable.md) of the observed
  and [potential outcomes](jargon_potential_outcome.md),
  [consistency](jargon_consistency.md) (`Yobs = Y(X)`), and a factorization
  condition (`rand`) that makes the
  [mean](jargon_mean.md) of `Y x` invariant to conditioning on `X = x0`. This is
  written to avoid explicit conditional expectations.
- `ConjointIdRandomized`: a randomized-design variant that assumes
  [measurable](jargon_measurable.md) assignment,
  [integrable](jargon_integrable.md) and uniformly bounded
  [potential outcomes](jargon_potential_outcome.md), and
  [independence](jargon_independent.md) between `X` and each `Y x`. These
  assumptions imply the `rand` factorization above.
- `ConjointSingleShotDesign`: a single-shot assignment law `ν` with positive mass
  on each [profile](jargon_profile.md), an explicit randomization mechanism for
  `X`, `Measure.map X μ = ν`, and bounded, measurable, consistent
  [potential outcomes](jargon_potential_outcome.md). The randomization mechanism
  is used to derive ignorability in `ConjointIdRandomized`.

## ModelBridge

- `WellSpecified`: exact [well-specified](jargon_well_specified.md): the causal
  [estimand](jargon_estimand.md) `gStar` equals the
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
- `L2Approx`: an [L2](jargon_l2.md)/[RMSE](jargon_rmse.md)-style approximation assumption: the model score differs
  from the target by at most `δ` in mean-square (uses the [L2](jargon_l2.md) norm under `ν`).
- `ParametricMainInteractions`: the paper's parametric assumption that `gStar`
  is exactly an intercept plus the specified main effects and listed
  [interactions](jargon_interaction.md).
- `AdditiveProjectionOracle`: defines the oracle as a linear-in-terms
  [additive projection](jargon_additive_projection.md) plus a residual orthogonal
  to each term feature, formalizing component targets when the oracle is nonlinear
  or interactive.

## WellSpecifiedFromNoInteractions

- `NoInteractions`: existence of an additive representation, formalizing the
  "no interactions" assumption used to justify
  [well-specification](jargon_well_specified.md).

## PaperOLSConsistency

- `PaperOLSLLNA`: entrywise [LLN](jargon_lln.md) for the sample Gram matrix and
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
