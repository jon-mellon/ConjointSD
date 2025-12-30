# Assumptions.lean

Lean file: [ConjointSD/Assumptions.lean](../ConjointSD/Assumptions.lean)

This file gathers all assumption bundles and assumption-level props in a single place
for auditability. Below is a detailed, assumption-by-assumption explanation of what
each package is asserting and why it matters.

The file depends on shared definitions in `ConjointSD/Defs.lean`.

Recent changes: probability-measure requirements were pushed into the moment bundles, and first-moment integrability is now derived from square-integrability where applicable.

## Structural assumptions (by model choice)

These are not formalized as Lean assumption bundles; they arise from how the model is set up.

- Single-shot abstraction: each observation is treated as a standalone profile draw. This
  sidesteps any task-indexing or within-respondent carryover structure. (Hainmueller Assumption 1, by omission)
- No task-order effects: because there is no task index in the core model, the formalization
  does not represent profile order or task sequence effects. (Related to Hainmueller Assumption 2, by omission)
- No attribute-order effects within a profile: profiles are abstract objects, so any ordering
  of attributes inside a profile is not represented. (Hainmueller footnote: attribute-order invariance)

## Transport

- `PopulationMomentAssumptions`: [population](jargon_population.md) moments for
  a score function `s` under a probability measure `ν`. It requires
  [almost-everywhere measurability](jargon_measurable.md) of `s` and
  [integrability](jargon_integrable.md) of `s^2`. The `s` integrability needed
  for [mean](jargon_mean.md) and [variance](jargon_variance.md) targets is
  derived from these conditions using `ν univ = 1`.
  - `PopulationMomentAssumptions.aemeas`: `s` is a.e. measurable under `ν`,
    so `s` can be integrated and is compatible with almost-everywhere
    statements used later in transport proofs. Intuition: we only need `s` to
    be well-defined except on a `ν`-null set, because population targets ignore
    measure-zero deviations. Formal: `AEMeasurable s ν`.
  - `PopulationMomentAssumptions.int2`: `s^2` is integrable under `ν`. This
    supplies finite second moments, which are the input for population
    [variance](jargon_variance.md) and [standard deviation](jargon_standard_deviation.md).
    Intuition: finite energy rules out heavy tails that would make SD undefined
    or unstable. Formal: `Integrable (fun a => (s a) ^ 2) ν`.
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

## BasicMeasure

- `ProbMeasureAssumptions`: bundles `IsProbabilityMeasure μ` as an explicit assumption
  package so theorems can avoid standalone probability-measure hypotheses.

## MapLaw

- `MapLawAssumptions`: bundles measurability of `A 0` with the pushforward law
  `Measure.map (A 0) μ = ν`, the standard transport assumption used to rewrite
  population moments from the joint space to the attribute space.
  - `MapLawAssumptions.measA0`: `A 0` is measurable, so pushforward and
    integrability statements about `A 0` are well-formed. Intuition: the
    attribute draw must be observable in a measure-theoretic sense to talk about
    its distribution. Formal: `Measurable (A 0)`.
  - `MapLawAssumptions.map_eq`: the distribution of `A 0` under `μ` equals `ν`,
    which justifies replacing population expectations under `ν` by expectations
    over the sample space. Intuition: the sample-space randomization induces the
    target population law on attributes. Formal: `Measure.map (A 0) μ = ν`.

## Convergence

- `ThetaTendstoAssumptions`: bundles estimator convergence `θhat → θ0` to keep
  convergence hypotheses explicit and reusable.
  - `ThetaTendstoAssumptions.tendsto`: the sequence `θhat` converges to `θ0`
    in the topology of `Θ`, the raw input for continuity-based arguments.
    Intuition: estimation noise vanishes asymptotically, so plugging in `θhat`
    is equivalent to using the truth. Formal: `Tendsto θhat atTop (nhds θ0)`.

## Positivity

- `EpsilonAssumptions`: bundles the positivity requirement `0 < ε` that appears
  in sequential consistency statements.

## PredictedSD

- `IIDAssumptions`: [IID](jargon_iid.md) assumptions for a sequence `Z` under a
  probability measure `μ`. Requires [independent](jargon_independent.md) and
  [identically distributed](jargon_identically_distributed.md) draws, plus
  [integrability](jargon_integrable.md) of `(Z 0)^2`. Integrability of `Z 0`
  is derived from square-integrability when `μ univ = 1`. This is the standard
  input for a strong [LLN](jargon_lln.md) for both the [mean](jargon_mean.md)
  and [second moment](jargon_second_moment.md), which delivers SD
  [consistency](jargon_consistency.md).
  - `IIDAssumptions.indep`: pairwise [independence](jargon_independent.md) of
    `Z i` and `Z j`, giving the stochastic decoupling needed for LLN arguments.
    Intuition: each draw contributes new information instead of repeating the
    same noise. Formal: `Pairwise (fun i j => IndepFun (Z i) (Z j) μ)`.
  - `IIDAssumptions.ident`: each `Z i` has the same law as `Z 0`, so empirical
    averages target a single population moment. Intuition: there is one stable
    data-generating process rather than a drifting distribution.
    Formal: `∀ i, IdentDistrib (Z i) (Z 0) μ μ`.
  - `IIDAssumptions.intZ2`: square-integrability of `Z 0`, ensuring finite
    second moments and enabling LLN for variance/SD targets. Intuition: rules
    out rare but huge observations that would dominate the SD.
    Formal: `Integrable (fun ω => (Z 0 ω) ^ 2) μ`.

## SDDecomposition

- `PopIID`: i.i.d.-style conditions for the attribute process `A n`. Requires
  [measurable](jargon_measurable.md) `A i`, pairwise
  [independence](jargon_independent.md), and
  [identical distribution](jargon_identically_distributed.md) across `i`. This
  is i.i.d. across the draw index (profiles/respondents/tasks), not within a
  profile, so attributes may still be correlated inside each profile.
- `ScoreAssumptions`: combines `PopIID` with
  [measurability](jargon_measurable.md) of the score function `g`, plus
  [integrability](jargon_integrable.md) of `g(A 0)^2` under a probability
  measure `μ`. Integrability of `g(A 0)` is derived from the second-moment
  condition. This is the input needed to apply the
  [standard deviation](jargon_standard_deviation.md)
  [LLN](jargon_lln.md) to the induced score process.
  - `ScoreAssumptions.meas_g`: the score `g` is measurable, so `g(A i)` is
    measurable when composed with each `A i`. Intuition: the score must be a
    well-defined observable function of attributes. Formal: `Measurable g`.
  - `ScoreAssumptions.int_g0_sq`: square-integrability of `g(A 0)`, which yields
    finite variance and supports LLN steps for SD consistency. Intuition: the
    score cannot have explosive tails if we want stable dispersion estimates.
    Formal: `Integrable (fun ω => (g (A 0 ω)) ^ 2) μ`.
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
  - `GEstimationAssumptions.mean_tendsto`: the estimated score's population
    mean converges to the oracle mean, so bias from estimation vanishes.
    Intuition: estimation error washes out in expectation even if pointwise
    predictions are noisy. Formal:
    `Tendsto (fun n => popMeanAttr ν (gHat g θhat n)) atTop (nhds (popMeanAttr ν (g θ0)))`.
  - `GEstimationAssumptions.m2_tendsto`: the estimated score's population
    second moment converges to the oracle second moment, enabling convergence
    of variance and SD by algebra. Intuition: the scale of the estimated score
    matches the oracle in the limit, not just the mean. Formal:
    `Tendsto (fun n => popM2Attr ν (gHat g θhat n)) atTop (nhds (popM2Attr ν (g θ0)))`.

## SampleSplitting

- `SplitEvalAssumptions`: applies `ScoreAssumptions` under a probability measure
  `μ` to the evaluation score
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
  - `OLSMomentAssumptionsOfPop.gramInv_tendsto`: entries of the inverse sample
    Gram matrix converge to the inverse population Gram, giving the stable
    design condition needed for OLS consistency. Intuition: the regressor
    geometry stabilizes, so the estimator does not amplify noise. Formal:
    `∀ i j, Tendsto (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j) atTop
      (nhds ((popGram (ν := ν) (φ := φ))⁻¹ i j))`.
  - `OLSMomentAssumptionsOfPop.cross_tendsto`: the sample cross-moment vector
    converges to the population cross moment, so the normal equations converge.
    Intuition: the empirical correlation between regressors and outcomes
    settles to its population value. Formal:
    `∀ i, Tendsto (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i) atTop
      (nhds (popCross (ν := ν) (g := g) (φ := φ) i))`.

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
  assumption from which ignorability of `X` is derived later. (Hainmueller Assumption 3)
- `NoProfileOrderEffects`: formalizes Assumption 2 by requiring potential outcomes
  for a task to be invariant under permutations of the profile order. (Hainmueller Assumption 2)
- `ConjointIdAssumptions`: [measurability](jargon_measurable.md) of the observed
  and [potential outcomes](jargon_potential_outcome.md),
  [consistency](jargon_consistency.md) (`Yobs = Y(X)`), and a factorization
  condition (`rand`) that makes the
  [mean](jargon_mean.md) of `Y x` invariant to conditioning on `X = x0`. This is
  written to avoid explicit conditional expectations.
  - `ConjointIdAssumptions.measYobs`: the observed outcome is measurable, so it
    can be integrated and restricted to events. Intuition: realized outcomes
    must be genuine observables, not just abstract potential values. Formal:
    `Measurable Yobs`.
  - `ConjointIdAssumptions.measY`: each potential outcome `Y x` is measurable,
    enabling conditional restriction arguments and mean comparisons. Intuition:
    counterfactual outcomes are regular enough to integrate even if unobserved.
    Formal: `∀ x, Measurable (Y x)`.
  - `ConjointIdAssumptions.consistency`: observed outcomes equal the potential
    outcome for the realized profile, the standard consistency requirement.
    Intuition: the measurement process does not distort outcomes. Formal:
    `∀ ω, Yobs ω = Y (X ω) ω`.
  - `ConjointIdAssumptions.rand`: factorization of means under restriction to
    `{X = x0}`, which encodes ignorability without conditional expectations.
    Intuition: assignment does not systematically change potential outcomes,
    so conditioning on treatment does not change their mean. Formal:
    `∀ x x0,
      (∫ ω, Y x ω ∂(μ.restrict (eventX (X := X) x0)))
        = (μ (eventX (X := X) x0)).toReal * (∫ ω, Y x ω ∂μ)`.
- `ConjointIdRandomized`: a randomized-design variant under a probability
  measure `μ`. It assumes [measurable](jargon_measurable.md) assignment,
  uniformly bounded [potential outcomes](jargon_potential_outcome.md), and
  [independence](jargon_independent.md) between `X` and each `Y x`. Integrability
  of outcomes is derived from boundedness. These assumptions imply the `rand`
  factorization above. (Hainmueller Assumption 3)
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
