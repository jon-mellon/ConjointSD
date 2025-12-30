# Assumptions.lean

Lean file: [ConjointSD/Assumptions.lean](../ConjointSD/Assumptions.lean)

This file gathers all assumption bundles and assumption-level props in a single place
for auditability. Below is a detailed, assumption-by-assumption explanation of what
each package is asserting and why it matters.

The file depends on shared definitions in `ConjointSD/Defs.lean`.

Recent changes: probability-measure requirements were pushed into the moment bundles, and first-moment integrability is now derived from square-integrability where applicable.

## Notation and scope

Throughout, `ν` denotes the *attribute distribution* (a target
[distribution](jargon_distribution.md)) for the target human
[population](jargon_population.md), while `μ` denotes the *experimental design
distribution* (a [distribution](jargon_distribution.md) on the sample space
`Ω`, the draw process for the study). In this document, “population” always
means the target human [population](jargon_population.md); we avoid using it as
a synonym for a measure. When we say “[population](jargon_population.md)
mean/variance/SD,” we mean those quantities computed with respect to `ν`, the
attribute distribution for the target human
[population](jargon_population.md).

## Structural assumptions (by model choice)

These are not formalized as Lean assumption bundles; they arise from how the model is set up.

- Single-shot abstraction: each observation is treated as a standalone profile draw. This
  sidesteps any task-indexing or within-respondent carryover structure. (Hainmueller Assumption 1, by omission)
  Intuition: the model abstracts away repeated choices by treating each profile as a fresh draw.
  Formal: not represented as a Lean predicate; this is a modeling choice in the definition of the data structure.
- No task-order effects: because there is no task index in the core model, the formalization
  does not represent profile order or task sequence effects. (Related to Hainmueller Assumption 2, by omission)
  Intuition: outcomes are invariant to when a task occurs because time/order is not modeled.
  Formal: not represented as a Lean predicate; task index is absent from the model.
- No attribute-order effects within a profile: profiles are abstract objects, so any ordering
  of attributes inside a profile is not represented. (Hainmueller footnote: attribute-order invariance)
  Intuition: attribute order is irrelevant because profiles are unordered records.
  Formal: not represented as a Lean predicate; profiles are modeled without ordered attribute positions.

## Transport

- `AttrMomentAssumptions`: [population](jargon_population.md) moments for
  a score function `s` under the attribute distribution `ν` on `Attr`
  (the attribute distribution representing the target human
  [population](jargon_population.md)). It requires
  [almost-everywhere measurability](jargon_measurable.md) of `s` and
  [integrability](jargon_integrable.md) of `s^2`. The `s` integrability needed
  for [mean](jargon_mean.md) and [variance](jargon_variance.md) targets is
  derived from these conditions using `ν univ = 1`.
  - `AttrMomentAssumptions.aemeas`: `s` is a.e. measurable under `ν`,
    so `s` can be integrated and is compatible with almost-everywhere
    statements used later in transport proofs. Intuition: we only need `s` to
    be well-defined except on a `ν`-null set, because
    [population](jargon_population.md) targets ignore
    measure-zero deviations. Formal: `AEMeasurable s ν`.
  - `AttrMomentAssumptions.int2`: `s^2` is integrable under the attribute
    distribution `ν` ([population](jargon_population.md) attribute distribution). This
    supplies finite second moments, which are the input for
    [population](jargon_population.md)
    [variance](jargon_variance.md) and [standard deviation](jargon_standard_deviation.md).
    Intuition: finite energy rules out heavy tails that would make SD undefined
    or unstable. Formal: `Integrable (fun a => (s a) ^ 2) ν`.
- `InvarianceAE`: almost-everywhere equality under the attribute distribution
  `ν`, i.e., the experimental and [population](jargon_population.md) scores
  agree on the [population support](jargon_population_support.md) (support of
  `ν`).
  Intuitively, they may
  differ only on a set with zero probability under `ν`; this is the external
  validity/transport assumption that lets [population](jargon_population.md)
  targets be read off from
  the experimental score. Formally: `gExp = gPop` nu-a.e. (under `ν`). It does
  not by itself guarantee the fitted model
  matches that score; misspecification or estimation error can still break
  transfer. It also fails if the experimental setup elicits a different scoring
  rule than the real-world [population](jargon_population.md) process (beyond a
  ν-null set). Intuition: the experiment and target human
  [population](jargon_population.md) differ only on events that never occur in
  the [population](jargon_population.md). Formal:
  `∀ᵐ x ∂ν, gExp x = gPop x`.

## BasicMeasure

- `ProbMeasureAssumptions`: bundles `IsProbabilityMeasure μ` as an explicit
  assumption package so theorems can avoid standalone probability-measure
  hypotheses. Intuition: we are working with a genuine probability law, not
  just a finite measure; the same wrapper is used for the target distribution
  `ν` and the experimental design distribution `μ` as needed. Formal:
  `IsProbabilityMeasure μ`.

## MapLaw

- `MapLawAssumptions`: bundles measurability of `A 0` with the pushforward law
  `Measure.map (A 0) μ = ν`, the standard transport assumption used to rewrite
  [population](jargon_population.md) moments from the experimental design
  distribution (`μ` on `Ω`) to the attribute distribution (`ν` on `Attr`).
  - `MapLawAssumptions.measA0`: `A 0` is measurable, so pushforward and
    integrability statements about `A 0` are well-formed. Intuition: the
    attribute draw must be observable in a measure-theoretic sense to talk about
    its distribution. Formal: `Measurable (A 0)`.
  - `MapLawAssumptions.map_eq`: the distribution of `A 0` under the
    experimental design distribution `μ` equals the attribute distribution `ν`,
    which justifies replacing [population](jargon_population.md) expectations under `ν` by expectations
    over the sample space. Intuition: the sample-space randomization induces the
    target [population](jargon_population.md) law on attributes. Formal: `Measure.map (A 0) μ = ν`.

## Convergence

- `ThetaTendstoAssumptions`: bundles estimator convergence `θhat → θ0` to keep
  convergence hypotheses explicit and reusable; this is a sample-side
  assumption about an estimator sequence under the experimental design
  distribution `μ`.
  - `ThetaTendstoAssumptions.tendsto`: the sequence `θhat` converges to `θ0`
    in the topology of `Θ`, the raw input for continuity-based arguments.
    Intuition: estimation noise vanishes asymptotically, so plugging in `θhat`
    is equivalent to using the truth. Formal: `Tendsto θhat atTop (nhds θ0)`.

## Positivity

- `EpsilonAssumptions`: bundles the positivity requirement `0 < ε` that appears
  in sequential consistency statements. This is a deterministic condition (no
  [population](jargon_population.md)/sample measure involved).
  - `EpsilonAssumptions.pos`: positivity of the tolerance/approximation scale.
    Intuition: a strict error tolerance avoids degenerate bounds.
    Formal: `0 < ε`.

## PredictedSD

- `IIDAssumptions`: [IID](jargon_iid.md) assumptions for a sequence `Z` under a
  probability measure `μ` on the sample space `Ω`. Requires
  [independent](jargon_independent.md) and
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
    averages target a single [population](jargon_population.md) moment (defined
    via the target distribution `ν`).
    Intuition: there is one stable data-generating process rather than a
    drifting distribution.
    Formal: `∀ i, IdentDistrib (Z i) (Z 0) μ μ`.
  - `IIDAssumptions.intZ2`: square-integrability of `Z 0`, ensuring finite
    second moments and enabling LLN for variance/SD targets. Intuition: rules
    out rare but huge observations that would dominate the SD.
    Formal: `Integrable (fun ω => (Z 0 ω) ^ 2) μ`.

## SDDecomposition

- `DesignAttrIID`: i.i.d.-style conditions for the attribute process `A n` under
  the experimental design distribution `μ`. Requires
  [measurable](jargon_measurable.md) `A i`, pairwise
  [independence](jargon_independent.md), and
  [identical distribution](jargon_identically_distributed.md) across `i`. This
  is i.i.d. across the draw index (profiles/respondents/tasks) under the
  experimental design distribution `μ` on `Ω`, not within a profile, so
  attributes may still be
  correlated inside each profile.
  - `DesignAttrIID.measA`: measurability of each draw `A i`.
    Intuition: each attribute draw is a valid random variable.
    Formal: `∀ i, Measurable (A i)`.
  - `DesignAttrIID.indepA`: pairwise independence of draws across indices.
    Intuition: different profiles are stochastically independent.
    Formal: `Pairwise (fun i j => IndepFun (A i) (A j) μ)`.
  - `DesignAttrIID.identA`: identical distribution across indices.
    Intuition: all profiles are drawn from the same distribution.
    Formal: `∀ i, IdentDistrib (A i) (A 0) μ μ`.
- `ScoreAssumptions`: combines `DesignAttrIID` with
  [measurability](jargon_measurable.md) of the score function `g`, plus
  [integrability](jargon_integrable.md) of `g(A 0)^2` under the experimental
  design distribution `μ`. Integrability of `g(A 0)` is derived from the
  second-moment
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
- `DecompAssumptions`: bundles `DesignAttrIID`, [measurability](jargon_measurable.md) of
  each
  [block](jargon_block.md) score `g b`, and a uniform boundedness condition for
  every block. Boundedness guarantees all required moments and simplifies
  [variance](jargon_variance.md) decomposition arguments. Concretely, there is
  a single constant `C` with `|g b(A i)| ≤ C` for all blocks `b` (and all draws
  `i`), so every block score is uniformly bounded. This gives integrability of
  each `g b` and every product `g b * g c`, ensures covariances exist, and lets
  you apply dominated-convergence or LLN-style steps without checking separate
  tail conditions for each block. These assumptions live on the sample draw
  process `A` under the experimental design distribution `μ`.
  - `DecompAssumptions.designAttrIID`: the attribute draws satisfy `DesignAttrIID`.
    Intuition: block scores are evaluated on i.i.d. attribute draws.
    Formal: `DesignAttrIID (μ := μ) A`.
  - `DecompAssumptions.meas_g`: each block score is measurable.
    Intuition: each block score is a valid observable function.
    Formal: `∀ b, Measurable (g b)`.
  - `DecompAssumptions.bound_g`: uniform boundedness across blocks.
    Intuition: no block has arbitrarily large magnitude, ensuring all block moments exist.
    Formal: `∀ b, ∃ C, 0 ≤ C ∧ ∀ a, |g b a| ≤ C`.

## VarianceDecomposition

- `BlockIntegrable`: [integrability](jargon_integrable.md) of each block score
  `g b(A 0)` and every product `g b(A 0) * g c(A 0)`. These are the minimal
  conditions to define block [means](jargon_mean.md) and
  [covariances](jargon_covariance.md) used in
  [variance](jargon_variance.md) decomposition under the experimental design
  distribution `μ`.
  - `BlockIntegrable.intX`: integrability of each block score.
    Intuition: block means are finite.
    Formal: `∀ b, Integrable (fun ω => g b (A 0 ω)) μ`.
  - `BlockIntegrable.intMul`: integrability of each block-product.
    Intuition: block covariances are finite.
    Formal: `∀ b c, Integrable (fun ω => g b (A 0 ω) * g c (A 0 ω)) μ`.

## EstimatedG

- `GEstimationAssumptions`: [convergence](jargon_convergence.md) of
  [population](jargon_population.md) [mean](jargon_mean.md) and
  [second moment](jargon_second_moment.md) when
  replacing
  [oracle](jargon_oracle.md) `g θ0` with estimated `g (θhat n)`. This assumption
  is framed directly on the [population](jargon_population.md) functionals so
  [standard deviation](jargon_standard_deviation.md) and
  [variance](jargon_variance.md) [consistency](jargon_consistency.md) follow by
  algebra. This is a [population](jargon_population.md)-side assumption under
  the attribute distribution `ν`.
  - `GEstimationAssumptions.mean_tendsto`: the estimated score's [population](jargon_population.md)
    mean converges to the oracle mean, so bias from estimation vanishes.
    Intuition: estimation error washes out in expectation even if pointwise
    predictions are noisy. Formal:
    `Tendsto (fun n => attrMean ν (gHat g θhat n)) atTop (nhds (attrMean ν (g θ0)))`.
  - `GEstimationAssumptions.m2_tendsto`: the estimated score's [population](jargon_population.md)
    second moment converges to the oracle second moment, enabling convergence
    of variance and SD by algebra. Intuition: the scale of the estimated score
    matches the oracle in the limit, not just the mean. Formal:
    `Tendsto (fun n => attrM2 ν (gHat g θhat n)) atTop (nhds (attrM2 ν (g θ0)))`.

## SampleSplitting

- `SplitEvalAssumptions`: applies `ScoreAssumptions` under a probability measure
  `μ` (the evaluation-sample experimental design distribution) to the evaluation score
  `gHat g θhat m` on the evaluation sample `A n`. This is the standard setup for
  showing the empirical [standard deviation](jargon_standard_deviation.md) of
  the estimated score [converges](jargon_convergence.md) to its
  [population](jargon_population.md) SD.
  - `SplitEvalAssumptions.hScore`: the evaluation score satisfies `ScoreAssumptions`.
    Intuition: the evaluation draw is i.i.d. with finite second moment for the estimated score.
    Formal: `ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m)`.
- `SplitEvalAssumptionsBounded`: alternative evaluation assumptions using
  `DesignAttrIID`, [measurability](jargon_measurable.md) of `gHat g θhat m`, and a
  global bound. This is a stronger but easier-to-check route to the same moment
  conditions under the experimental design distribution `μ`.
  - `SplitEvalAssumptionsBounded.hPop`: evaluation draws satisfy `DesignAttrIID`.
    Intuition: the sample is i.i.d. at the attribute level under `μ`.
    Formal: `DesignAttrIID (μ := μ) A`.
  - `SplitEvalAssumptionsBounded.hMeas`: the estimated score is measurable.
    Intuition: the score is a valid observable function of attributes.
    Formal: `Measurable (gHat g θhat m)`.
  - `SplitEvalAssumptionsBounded.hBound`: uniform boundedness of the score.
    Intuition: bounded scores guarantee finite moments without extra tail work.
    Formal: `∃ C, 0 ≤ C ∧ ∀ a, |gHat g θhat m a| ≤ C`.

## RegressionConsistencyBridge

- `FunctionalContinuityAssumptions`: [continuity](jargon_continuity.md) at `θ0`
  of the [population](jargon_population.md) [mean](jargon_mean.md) and
  [second moment](jargon_second_moment.md)
  functionals. These are the continuity inputs that let
  [regression](jargon_regression.md) [consistency](jargon_consistency.md)
  translate estimator [convergence](jargon_convergence.md) into moment
  [convergence](jargon_convergence.md). This is a
  [population](jargon_population.md)-side assumption
  under the attribute distribution `ν`.
  - `FunctionalContinuityAssumptions.cont_mean`: mean functional is continuous at `θ0`.
    Intuition: small parameter perturbations do not change the mean much.
    Formal: `ContinuousAt (attrMeanΘ (ν := ν) g) θ0`.
  - `FunctionalContinuityAssumptions.cont_m2`: second-moment functional is continuous at `θ0`.
    Intuition: the scale of the score changes smoothly with parameters.
    Formal: `ContinuousAt (attrM2Θ (ν := ν) g) θ0`.
- `BlockFunctionalContinuityAssumptions`: the blockwise version of functional
  continuity, requiring the above assumptions for each block score under the
  attribute distribution `ν`.
  - `BlockFunctionalContinuityAssumptions.cont`: each block score satisfies
    `FunctionalContinuityAssumptions` at `θ0`.
    Intuition: every block mean/second moment is stable under small parameter changes.
    Formal: `∀ b, FunctionalContinuityAssumptions (ν := ν) (blockScoreΘ (gB := gB) b) θ0`.

## RegressionEstimator

- `OLSConsistencyAssumptions`: a single assumption that the
  [OLS](jargon_ols.md) [estimator](jargon_estimator.md) sequence
  [converges](jargon_convergence.md) to the target `θ0`. This is a
  sample-sequence assumption about `ols.θhat` under the experimental design
  distribution `μ`.
  - `OLSConsistencyAssumptions.tendsto_theta`: convergence of the estimator sequence.
    Intuition: the estimator settles at the true coefficient vector.
    Formal: `Tendsto ols.θhat atTop (nhds θ0)`.
- `OLSMomentAssumptions`: a deterministic moment-limit package. It posits limits
  for the inverse Gram matrix and cross-product vector and states that `θ0`
  solves the limiting normal equations. This is the generic,
  non-[population](jargon_population.md) formulation (purely sample-side limits
  under the experimental design distribution `μ`).
  - `OLSMomentAssumptions.gramInvLimit`: limit of inverse Gram entries.
    Intuition: the design stabilizes to a fixed geometry.
    Formal: `gramInvLimit : Matrix Term Term ℝ`.
  - `OLSMomentAssumptions.crossLimit`: limit of cross moments.
    Intuition: empirical regressor-outcome correlations stabilize.
    Formal: `crossLimit : Term → ℝ`.
  - `OLSMomentAssumptions.gramInv_tendsto`: convergence of inverse Gram entries.
    Intuition: the sample inverse Gram converges entrywise.
    Formal:
    `∀ i j, Tendsto (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j) atTop
      (nhds (gramInvLimit i j))`.
  - `OLSMomentAssumptions.cross_tendsto`: convergence of cross-moment entries.
    Intuition: empirical cross moments converge to their limits.
    Formal:
    `∀ i, Tendsto (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i) atTop
      (nhds (crossLimit i))`.
  - `OLSMomentAssumptions.theta0_eq`: normal equations identify `θ0`.
    Intuition: the limiting moments solve for the target coefficients.
    Formal: `θ0 = gramInvLimit.mulVec crossLimit`.
- `OLSMomentAssumptionsOfAttr`: the [population](jargon_population.md) version of
  the above, with the limits pinned to the
  [population](jargon_population.md) Gram and cross moments (under the
  attribute distribution `ν`).
  This is the standard [LLN](jargon_lln.md) + identifiability package for
  [OLS](jargon_ols.md): sample sequences `A, Y` under the experimental design
  distribution `μ` converge to [population](jargon_population.md) targets under
  `ν`.
  - `OLSMomentAssumptionsOfAttr.gramInv_tendsto`: entries of the inverse sample
    Gram matrix converge to the inverse
    [population](jargon_population.md) Gram, giving the stable
    design condition needed for OLS consistency. Intuition: the regressor
    geometry stabilizes, so the estimator does not amplify noise. Formal:
    `∀ i j, Tendsto (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j) atTop
      (nhds ((attrGram (ν := ν) (φ := φ))⁻¹ i j))`.
  - `OLSMomentAssumptionsOfAttr.cross_tendsto`: the sample cross-moment vector
    converges to the [population](jargon_population.md) cross moment, so the
    normal equations converge. Intuition: the empirical correlation between
    regressors and outcomes settles to its
    [population](jargon_population.md) value. Formal:
    `∀ i, Tendsto (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i) atTop
      (nhds (attrCross (ν := ν) (g := g) (φ := φ) i))`.

## SurveyWeights

- `WeightAssumptions`: nonnegativity of weights a.e.,
  [integrability](jargon_integrable.md) of `w`, `w*s`, and `w*s^2`, plus strictly
  positive total weight. Together these ensure weighted moments
  ([mean](jargon_mean.md), [variance](jargon_variance.md),
  [standard deviation](jargon_standard_deviation.md)) are well-defined and
  nondegenerate. These are [population](jargon_population.md) moment conditions
  under the attribute distribution `ν`, used to define weighted
  [population](jargon_population.md) targets.
  - `WeightAssumptions.nonneg`: weights are nonnegative a.e.
    Intuition: weights behave like sampling probabilities.
    Formal: `∀ᵐ a ∂ν, 0 ≤ w a`.
  - `WeightAssumptions.intW`: weights are integrable.
    Intuition: total weight is finite.
    Formal: `Integrable w ν`.
  - `WeightAssumptions.intWs`: weighted score is integrable.
    Intuition: weighted mean exists.
    Formal: `Integrable (fun a => w a * s a) ν`.
  - `WeightAssumptions.intWs2`: weighted square is integrable.
    Intuition: weighted variance exists.
    Formal: `Integrable (fun a => w a * (s a) ^ 2) ν`.
  - `WeightAssumptions.mass_pos`: total weight is strictly positive.
    Intuition: the weighted sample is nondegenerate.
    Formal: `0 < ∫ a, w a ∂ν`.
- `WeightMatchesAttrMoments`: the weighted [mean](jargon_mean.md) and weighted
  [second moment](jargon_second_moment.md) match the
  [population](jargon_population.md) moments, a
  moment-matching condition used to transfer SD targets from the
  [population](jargon_population.md) to a weighted sample. This is a
  [population](jargon_population.md)-side matching condition under the
  attribute distribution `ν`.
  - `WeightMatchesAttrMoments.mean_eq`: weighted mean equals
    [population](jargon_population.md) mean.
    Intuition: reweighting fixes the mean target.
    Formal: `(∫ a, w a * s a ∂ν) / (∫ a, w a ∂ν) = attrMean ν s`.
  - `WeightMatchesAttrMoments.m2_eq`: weighted second moment equals
    [population](jargon_population.md) second moment.
    Intuition: reweighting fixes the variance scale.
    Formal: `(∫ a, w a * (s a) ^ 2 ∂ν) / (∫ a, w a ∂ν) = attrM2 ν s`.

## ConjointIdentification

- `ConjointRandomizationMechanism`: models randomization explicitly by writing
  the assignment `X` as a measurable function of a randomization variable `U`
  that is [independent](jargon_independent.md) of every
  [potential outcome](jargon_potential_outcome.md). This is the mechanism-level
  assumption from which ignorability of `X` is derived later; it is a sample-side
  assumption under the experimental design distribution `μ`. (Hainmueller Assumption 3)
  - `ConjointRandomizationMechanism.exists_randomization`: there is a latent
    randomization variable and measurable map generating `X`, independent of outcomes.
    Intuition: assignment is produced by an explicit random device.
    Formal:
    `∃ (R : Type 0) (_ : MeasurableSpace R) (U : Ω → R) (f : R → Attr),
      Measurable U ∧ Measurable f ∧ X = (fun ω => f (U ω)) ∧
      ∀ x, (fun ω => U ω) ⟂ᵢ[μ] (fun ω => Y x ω)`.
- `NoProfileOrderEffects`: formalizes Assumption 2 by requiring potential outcomes
  for a task to be invariant under permutations of the profile order, under the
  experimental design distribution `μ`. (Hainmueller Assumption 2)
  - `NoProfileOrderEffects.permute`: invariance to permutations of profile order.
    Intuition: only the set of profiles matters, not their ordering.
    Formal: `∀ k t (π : Equiv.Perm J), Y k (permuteProfiles π t) = Y k t`.
- `ConjointIdAssumptions`: [measurability](jargon_measurable.md) of the observed
  and [potential outcomes](jargon_potential_outcome.md),
  [consistency](jargon_consistency.md) (`Yobs = Y(X)`), and a factorization
  condition (`rand`) that makes the
  [mean](jargon_mean.md) of `Y x` invariant to conditioning on `X = x0`. This is
  written to avoid explicit conditional expectations. These assumptions apply to
  the experimental design distribution `μ` on `Ω`.
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
  measure `μ` (experimental design distribution). It assumes
  [measurable](jargon_measurable.md) assignment,
  uniformly bounded [potential outcomes](jargon_potential_outcome.md), and
  [independence](jargon_independent.md) between `X` and each `Y x`. Integrability
  of outcomes is derived from boundedness. These assumptions imply the `rand`
  factorization above. (Hainmueller Assumption 3)
  - `ConjointIdRandomized.measX`: assignment is measurable.
    Intuition: treatment is a well-defined random variable.
    Formal: `Measurable X`.
  - `ConjointIdRandomized.measYobs`: observed outcomes are measurable.
    Intuition: outcomes are observable random variables.
    Formal: `Measurable Yobs`.
  - `ConjointIdRandomized.measY`: potential outcomes are measurable.
    Intuition: counterfactual outcomes are integrable.
    Formal: `∀ x, Measurable (Y x)`.
  - `ConjointIdRandomized.consistency`: observed equals realized potential outcome.
    Intuition: no measurement distortion.
    Formal: `∀ ω, Yobs ω = Y (X ω) ω`.
  - `ConjointIdRandomized.bounded`: uniform boundedness of potential outcomes.
    Intuition: outcomes have finite moments by design.
    Formal: `∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Y x ω| ≤ C`.
  - `ConjointIdRandomized.ignorability`: assignment is independent of each `Y x`.
    Intuition: randomization breaks confounding.
    Formal: `∀ x, (fun ω => X ω) ⟂ᵢ[μ] (fun ω => Y x ω)`.
- `ConjointSingleShotDesign`: a single-shot assignment law `ν` with positive mass
  on each [profile](jargon_profile.md), an explicit randomization mechanism for
  `X`, `Measure.map X μ = ν`, and bounded, measurable, consistent
  [potential outcomes](jargon_potential_outcome.md). The randomization mechanism
  is used to derive ignorability in `ConjointIdRandomized`. This bridges the
  sample assignment process `μ` to the assignment law `ν` for the target human
  [population](jargon_population.md).
  - `ConjointSingleShotDesign.rand`: explicit randomization mechanism for `X`.
    Intuition: assignment is generated by a random device.
    Formal: `ConjointRandomizationMechanism (μ := μ) (X := X) (Y := Y)`.
  - `ConjointSingleShotDesign.lawX`: pushforward of `X` equals the assignment law.
    Intuition: the design distribution for profiles is fixed and known.
    Formal: `Measure.map X μ = ν`.
  - `ConjointSingleShotDesign.ν_pos`: each profile has positive mass.
    Intuition: every profile can be assigned with nonzero probability.
    Formal: `∀ x, ν {x} ≠ 0`.
  - `ConjointSingleShotDesign.measYobs`: observed outcome is measurable.
    Intuition: outcomes are valid random variables.
    Formal: `Measurable Yobs`.
  - `ConjointSingleShotDesign.measY`: potential outcomes are measurable.
    Intuition: counterfactual outcomes are integrable.
    Formal: `∀ x, Measurable (Y x)`.
  - `ConjointSingleShotDesign.consistency`: observed equals realized potential outcome.
    Intuition: no measurement distortion.
    Formal: `∀ ω, Yobs ω = Y (X ω) ω`.
  - `ConjointSingleShotDesign.bounded`: outcomes are uniformly bounded.
    Intuition: boundedness ensures integrability without extra assumptions.
    Formal: `∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Y x ω| ≤ C`.

## ModelBridge

- `WellSpecified`: exact [well-specified](jargon_well_specified.md): the causal
  [estimand](jargon_estimand.md) `gStar` equals the
  [linear-in-terms](jargon_linear_in_terms.md) model `gLin` for all
  [profiles](jargon_profile.md).
  Intuition: the model class contains the true causal response surface under
  the experimental design distribution `μ`.
  Formal: `∀ x, gLin (β := β) (φ := φ) x = gStar (μ := μ) (Y := Y) x`.
- `ApproxWellSpecified`: uniform approximation by `gLin`, with a fixed error
  tolerance `ε` at every [profile](jargon_profile.md).
  Intuition: the model is uniformly close to truth, with bounded approximation
  error under the experimental design distribution `μ`.
  Formal: `∀ x, |gLin (β := β) (φ := φ) x - gStar (μ := μ) (Y := Y) x| ≤ ε`.
- `ApproxWellSpecifiedAE`: the same approximation requirement, but only
  [almost everywhere](jargon_almost_everywhere.md) under the attribute
  distribution `ν`.
  Intuition: approximation may fail on a `ν`-null set with no
  [population](jargon_population.md) impact.
  Formal: `∀ᵐ x ∂ν, |gLin (β := β) (φ := φ) x - gStar (μ := μ) (Y := Y) x| ≤ ε`.
- `ApproxOracleAE`: a two-stage approximation assumption: a flexible score
  approximates the true target `gStar`, and the model score approximates the
  flexible score, both [almost everywhere](jargon_almost_everywhere.md) under
  the attribute distribution `ν`.
  Intuition: use a rich intermediate score to bridge to the target.
  Formal:
  `(∀ᵐ x ∂ν, |gModel x - gFlex x| ≤ δModel) ∧ (∀ᵐ x ∂ν, |gFlex x - gStar x| ≤ δOracle)`.
- `L2Approx`: an [L2](jargon_l2.md)/[RMSE](jargon_rmse.md)-style approximation assumption: the model score differs
  from the target by at most `δ` in mean-square (uses the [L2](jargon_l2.md) norm under `ν`).
  Intuition: the average squared error is bounded by `δ^2`.
  Formal:
  `MemLp (fun a => gModel a - gTarget a) (ENNReal.ofReal 2) ν ∧
    Real.sqrt (∫ a, |gModel a - gTarget a| ^ 2 ∂ν) ≤ δ`.
- `ParametricMainInteractions`: the paper's parametric assumption that `gStar`
  is exactly an intercept plus the specified main effects and listed
  [interactions](jargon_interaction.md).
  Intuition: the causal surface is fully captured by the stated main and
  interaction terms under the experimental design distribution `μ`.
  Formal:
  `∀ x, gStar (μ := μ) (Y := Y) x =
    β0 + (∑ m, βMain m * fMain m x) + (∑ i, βInter i * fInter i x)`.
- `AdditiveProjectionOracle`: defines the oracle as a linear-in-terms
  [additive projection](jargon_additive_projection.md) plus a residual orthogonal
  to each term feature, formalizing component targets when the oracle is nonlinear
  or interactive.
  Intuition: the oracle decomposes into a best linear projection plus an
  orthogonal error under the attribute distribution `ν` for the target human
  [population](jargon_population.md).
  Formal:
  `(∀ x, gOracle x = gLin (β := β) (φ := φ) x + r x) ∧
    (∀ t, Integrable (fun x => r x * φ t x) ν) ∧
    (∀ t, ∫ x, r x * φ t x ∂ν = 0)`.

## WellSpecifiedFromNoInteractions

- `NoInteractions`: existence of an additive representation, formalizing the
  "no interactions" assumption used to justify
  [well-specification](jargon_well_specified.md).
  Intuition: only main effects matter; there are no interaction terms under the
  experimental design distribution `μ`.
  Formal:
  `∃ (μ0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V, gStar (μ := μ) (Y := Y) x = μ0 + ∑ k : K, main k (x k)`.

## PaperOLSConsistency

- `PaperOLSLLNA`: entrywise [LLN](jargon_lln.md) for the sample Gram matrix and
  cross moment vector, [converging](jargon_convergence.md) to
  [population](jargon_population.md) targets for the paper basis (sample
  sequences under the experimental design distribution `μ`, targets under `ν`).
  - `PaperOLSLLNA.gram_tendsto`: entrywise LLN for the Gram matrix.
    Intuition: sample regressor covariances converge to
    [population](jargon_population.md) covariances.
    Formal:
    `∀ i j, Tendsto
      (fun n => gramMatrix (A := A) (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) n i j)
      atTop
      (nhds (attrGram (ν := ν) (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i j))`.
  - `PaperOLSLLNA.cross_tendsto`: entrywise LLN for the cross moments.
    Intuition: sample regressor-outcome correlations converge to
    [population](jargon_population.md) values.
    Formal:
    `∀ i, Tendsto
      (fun n => crossVec (A := A) (Y := Yobs)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) n i)
      atTop
      (nhds (attrCross (ν := ν) (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) i))`.
- `PaperOLSInverseStability`: stability of the inverse Gram entries, ensuring
  [convergence](jargon_convergence.md) of the sample inverse to the
  [population](jargon_population.md) inverse.
  - `PaperOLSInverseStability.gramInv_tendsto`: entrywise inverse-gram convergence.
    Intuition: the inverse design matrix stabilizes.
    Formal:
    `∀ i j, Tendsto
      (fun n => (gramMatrix (A := A)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)) n)⁻¹ i j)
      atTop
      (nhds ((attrGram (ν := ν)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹ i j))`.
- `PaperOLSIdentifiability`: the normal equations with
  [population](jargon_population.md) moments identify the target
  [parameter](jargon_parameter.md) `θ0`.
  Intuition: the [population](jargon_population.md) linear system has a unique
  solution equal to the target.
  Formal:
  `θ0 =
    (attrGram (ν := ν) (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))⁻¹.mulVec
      (attrCross (ν := ν) (g := gStar (μ := μ) (Y := Y))
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter)))`.
- `PaperOLSMomentAssumptions`: almost-everywhere (over sample paths) version of
  the [population](jargon_population.md) moment assumptions, applied to the
  realized sample sequences.
  Intuition: for almost every sample path under the experimental design
  distribution `μ`, the [population](jargon_population.md)-moment assumptions
  (under `ν`) apply to the realized sequence.
  Formal:
  `∀ᵐ ω ∂μ,
    OLSMomentAssumptionsOfAttr
      (ν := ν)
      (A := fun n => Aω n ω) (Y := fun n => Yobsω n ω)
      (g := gStar (μ := μ) (Y := Y))
      (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))
      θ0`.
