# Assumptions.lean

Lean file: [ConjointSD/Assumptions.lean](../ConjointSD/Assumptions.lean)

This file gathers all assumption bundles and assumption-level props in a single place
for auditability. Below is a detailed, assumption-by-assumption explanation of what
each package is asserting and why it matters.

The file depends on shared definitions in `ConjointSD/Defs.lean`.

## Transport

- `PopulationMomentAssumptions`: first- and second-moment existence for a score
  function `s` under a [population](jargon_population.md) measure `ν`, expressed
  as [integrable](jargon_integrable.md) `s` and `s^2`. This is the minimal setup
  for defining population [mean](jargon_mean.md), [variance](jargon_variance.md),
  and [standard deviation](jargon_standard_deviation.md) targets.
- `Overlap`: absolute continuity `ν ≪ π` between population and design measures.
  Substantively, any attribute profile with zero design probability also has
  zero population probability, so transport from design to population is not
  extrapolating outside support.
- `Invariance`: pointwise equality `gExp = gPop` for all attribute profiles.
  This is the strongest transport assumption: experimental and population scores
  coincide everywhere.
- `InvarianceAE`: almost-everywhere equality under `ν`. This weakens `Invariance`
  to a support condition: equality only needs to hold on the population support.
- `TransportAssumptions`: bundles probability-measure status of `ν` and `π`,
  `Overlap`, and `InvarianceAE` into a single package for transport arguments.

## PredictedSD

- `IIDAssumptions`: [IID](jargon_iid.md) and moment assumptions for a sequence
  `Z`. Requires [independent](jargon_independent.md) and
  [identically distributed](jargon_identically_distributed.md) draws, plus
  integrability of `Z 0` and `(Z 0)^2`. This is the standard input for a strong
  law for both the mean and second moment, which delivers SD consistency.

## SDDecomposition

- `PopIID`: i.i.d.-style conditions for the attribute process `A n`. Requires
  [measurable](jargon_measurable.md) `A i`, pairwise independence, and identical
  distribution across `i`.
- `ScoreAssumptions`: combines `PopIID` with measurability of the score function
  `g`, plus integrability of `g(A 0)` and `g(A 0)^2`. This is the input needed to
  apply the [standard deviation](jargon_standard_deviation.md) law of large
  numbers to the induced score process.
- `DecompAssumptions`: bundles `PopIID`, measurability of each
  [block](jargon_block.md) score `g b`, and a uniform boundedness condition for
  every block. Boundedness guarantees all required moments and simplifies
  [variance](jargon_variance.md) decomposition arguments.

## VarianceDecomposition

- `BlockIntegrable`: integrability of each block score `g b(A 0)` and every
  product `g b(A 0) * g c(A 0)`. These are the minimal conditions to define
  block means and [covariances](jargon_covariance.md) used in
  [variance](jargon_variance.md) decomposition.

## EstimatedG

- `GEstimationAssumptions`: convergence of population mean and second moment when
  replacing oracle `g θ0` with estimated `g (θhat n)`. This assumption is framed
  directly on the population functionals so
  [standard deviation](jargon_standard_deviation.md) and
  [variance](jargon_variance.md) consistency follow by algebra.

## SampleSplitting

- `SplitEvalAssumptions`: applies `ScoreAssumptions` to the evaluation score
  `gHat g θhat m` on the evaluation sample `A n`. This is the standard setup for
  showing the empirical [standard deviation](jargon_standard_deviation.md) of
  the estimated score converges to its population SD.
- `SplitEvalAssumptionsBounded`: alternative evaluation assumptions using
  `PopIID`, measurability of `gHat g θhat m`, and a global bound. This is a
  stronger but easier-to-check route to the same moment conditions.

## RegressionConsistencyBridge

- `FunctionalContinuityAssumptions`: [continuity](jargon_continuity.md) at `θ0`
  of the population mean and second moment functionals. These are the continuity
  inputs that let regression consistency translate estimator convergence into
  moment convergence.
- `BlockFunctionalContinuityAssumptions`: the blockwise version of functional
  continuity, requiring the above assumptions for each block score.

## RegressionEstimator

- `OLSConsistencyAssumptions`: a single assumption that the OLS estimator
  sequence converges to the target `θ0`.
- `OLSMomentAssumptions`: a deterministic moment-limit package. It posits limits
  for the inverse Gram matrix and cross-product vector and states that `θ0`
  solves the limiting normal equations. This is the generic, non-population
  formulation.
- `OLSMomentAssumptionsOfPop`: the population version of the above, with the
  limits pinned to the population Gram and cross moments. This is the standard
  LLN + identifiability package for [OLS](jargon_ols.md).

## SurveyWeights

- `WeightAssumptions`: nonnegativity of weights a.e., integrability of `w`,
  `w*s`, and `w*s^2`, plus strictly positive total weight. Together these ensure
  weighted moments (mean, [variance](jargon_variance.md),
  [standard deviation](jargon_standard_deviation.md)) are well-defined and
  nondegenerate.

## ConjointIdentification

- `ConjointIdAssumptions`: measurability of the observed and potential outcomes,
  consistency (`Yobs = Y(X)`), positivity of assignment, and a factorization
  condition (`rand`) that makes the mean of `Y x` invariant to conditioning on
  `X = x0`. This is written to avoid explicit conditional expectations.
- `ConjointIdRandomized`: a randomized-design variant that assumes measurable
  assignment, integrable and uniformly bounded potential outcomes, positivity,
  and [independence](jargon_independent.md) between `X` and each `Y x`. These
  assumptions imply the `rand` factorization above.
- `ConjointSingleShotDesign`: a single-shot assignment law `ν` with positive mass
  on each profile, measurable assignment `X` with `Measure.map X μ = ν`, and
  bounded, measurable, consistent potential outcomes. Together with design
  independence, this implies `ConjointIdRandomized`.

## ModelBridge

- `WellSpecified`: exact well-specification: the causal estimand `gStar` equals
  the linear-in-terms model `gLin` for all profiles.
- `ApproxWellSpecified`: uniform approximation by `gLin`, with a fixed error
  tolerance `ε` at every profile.
- `ApproxWellSpecifiedAE`: the same approximation requirement, but only
  [almost everywhere](jargon_almost_everywhere.md) under a population measure.
- `ParametricMainInteractions`: the paper's parametric assumption that `gStar`
  is exactly an intercept plus the specified main effects and listed
  [interactions](jargon_interaction.md).

## WellSpecifiedFromNoInteractions

- `AdditiveGStar`: exact additivity of `gStar` across attributes: an intercept
  plus a sum of per-attribute main effects.
- `NoInteractions`: existence of an additive representation, formalizing the
  "no interactions" assumption used to justify well-specification.

## PaperOLSConsistency

- `PaperOLSLLNA`: entrywise law of large numbers for the sample Gram matrix and
  cross moment vector, converging to population targets for the paper basis.
- `PaperOLSInverseStability`: stability of the inverse Gram entries, ensuring
  convergence of the sample inverse to the population inverse.
- `PaperOLSIdentifiability`: the normal equations with population moments
  identify the target parameter `θ0`.
- `PaperOLSMomentAssumptions`: almost-everywhere (over sample paths) version of
  the population moment assumptions, applied to the realized sample sequences.
