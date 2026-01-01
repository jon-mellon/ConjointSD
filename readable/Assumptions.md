# Assumptions.lean

Lean file: [ConjointSD/Assumptions.lean](../ConjointSD/Assumptions.lean)

This file gathers all assumption bundles and assumption-level props in a single place
for auditability. Below is a detailed, assumption-by-assumption explanation of what
each package is asserting and why it matters.

Note on OLS: the regression section uses the standard **consistency** assumptions
(LLN for `X'X/n` and `X'Y/n`, full-rank/invertible limit, and normal-equation identification),
not the classical Gauss–Markov/BLUE conditions.

The file depends on shared definitions in `ConjointSD/Defs.lean`.

Recent changes: probability-measure requirements were pushed into the moment bundles, and first-moment integrability is now derived from square-integrability where applicable.

## Notation and scope

Throughout, `ν` denotes the *attribute distribution* (a target
[distribution](jargon_distribution.md)) for the target human
[population](jargon_population.md). We use `μexp` for the experimental design
distribution (the law generating the conjoint experiment data) and `μ` for the
evaluation-law used to compute SDs; `EvalWeightMatchesAttrMoments` ties weighted
evaluation draws to `ν`.
In this document, “population” always means the target human
[population](jargon_population.md); we avoid using it as a synonym for a
measure. When we say “[population](jargon_population.md) mean/variance/SD,” we
mean those quantities computed with respect to `ν`, the attribute distribution
for the target human [population](jargon_population.md).

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
- `EvalWeightMatchesAttrMoments`: weighted transport assumption for a specific score `s`.
  It asserts that the evaluation draw’s *weighted* [mean](jargon_mean.md) and
  [second moment](jargon_second_moment.md) (under weights `w`) match the target
  [population](jargon_population.md) moments under `ν`. This supports SD targets
  without full law equality, but requires the weighting step explicitly.
  - `EvalWeightMatchesAttrMoments.measA0`: `A 0` is measurable.
    Intuition: the evaluation draw is a well-defined random variable.
    Formal: `Measurable (A 0)`.
  - `EvalWeightMatchesAttrMoments.mean_eq`: weighted evaluation mean equals target mean.
    Intuition: reweighted evaluation averages match the population target.
    Formal: `(∫ w a * s a)/(∫ w a) = attrMean ν s` under `Measure.map (A 0) μ`.
  - `EvalWeightMatchesAttrMoments.m2_eq`: weighted evaluation second moment equals target second moment.
    Intuition: reweighted evaluation scale matches the population target.
    Formal: `(∫ w a * s a^2)/(∫ w a) = attrM2 ν s` under `Measure.map (A 0) μ`.
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

- `ProbMeasureAssumptions` (trivial): bundles `IsProbabilityMeasure μ` as an explicit
  assumption package so theorems can avoid standalone probability-measure
  hypotheses. Intuition: we are working with a genuine probability law, not
  just a finite measure; the same wrapper is used for the target distribution
  `ν` and the experimental design distribution `μ` as needed. Formal:
  `IsProbabilityMeasure μ`.

## Positivity

- `EpsilonAssumptions` (trivial): bundles the positivity requirement `0 < ε` that appears
  in sequential consistency statements. This is a deterministic condition (no
  [population](jargon_population.md)/sample measure involved).
  - `EpsilonAssumptions.pos`: positivity of the tolerance/approximation scale.
    Intuition: a strict error tolerance avoids degenerate bounds.
    Formal: `0 < ε`.
  - Usage note: throughout the repo, `ε` is always a nonnegative tolerance on
  magnitude. In sequential consistency results it bounds nonnegative error
  quantities like `totalErr ... < ε`. In approximation assumptions it appears
  as an absolute-error bound such as `|...| ≤ ε` (e.g., approximate
  well-specification or no-interactions). There are no uses where `ε` encodes
  a signed directional error; if that were desired, the assumptions would need
  one-sided inequalities instead of absolute-value bounds. This makes
  `EpsilonAssumptions` a bookkeeping convention that records the “ε is a
  tolerance” intent explicitly in hypotheses.

## SDDecomposition

- `DesignAttrIID`: i.i.d.-style conditions for the attribute draw process `A`
  under the experimental design distribution `μ` (measurability of each `A i`,
  pairwise independence across draws, and identical distribution across draws).
  Intuition: the attribute profiles are sampled in a stable, independent way
  under the design. Formal:
  `∀ i, Measurable (A i) ∧
    Pairwise (fun i j => IndepFun (A i) (A j) μ) ∧
    ∀ i, IdentDistrib (A i) (A 0) μ μ`.
- `ScoreAssumptions`: combines attribute-stream i.i.d. properties (derived from
  `ConjointRandomizationStream`) with [measurability](jargon_measurable.md) of
  the score function `g`, plus [integrability](jargon_integrable.md) of
  `g(A 0)^2` under the experimental design distribution `μ`. Integrability of
  `g(A 0)` is derived from the second-moment condition. This is the input
  needed to apply the score-based [standard deviation](jargon_standard_deviation.md)
  [LLN](jargon_lln.md) lemmas for the induced score process (e.g.,
  `sdHatZ_tendsto_ae_of_score`).
  - `ScoreAssumptions.meas_g`: the score `g` is measurable, so `g(A i)` is
    measurable when composed with each `A i`. Intuition: the score must be a
    well-defined observable function of attributes. Formal: `Measurable g`.
  - `ScoreAssumptions.int_g0_sq`: square-integrability of `g(A 0)`, which yields
    finite variance and supports LLN steps for SD consistency. Intuition: the
    score cannot have explosive tails if we want stable dispersion estimates.
    Formal: `Integrable (fun ω => (g (A 0 ω)) ^ 2) μ`.
- `DecompAssumptions`: bundles attribute-stream i.i.d. properties (derived from
  `ConjointRandomizationStream`), [measurability](jargon_measurable.md) of each
  [block](jargon_block.md) score `g b`, and a uniform boundedness condition for
  every block. Boundedness guarantees all required moments and simplifies
  [variance](jargon_variance.md) decomposition arguments. Concretely, there is
  a single constant `C` with `|g b(A i)| ≤ C` for all blocks `b` (and all draws
  `i`), so every block score is uniformly bounded. This gives integrability of
  each `g b` and every product `g b * g c`, ensures covariances exist, and lets
  you apply dominated-convergence or LLN-style steps without checking separate
  tail conditions for each block. These assumptions live on the sample draw
  process `A` under the experimental design distribution `μ`.
  - `DecompAssumptions.meas_g`: each block score is measurable.
    Intuition: each block score is a valid observable function.
    Formal: `∀ b, Measurable (g b)`.
  - `DecompAssumptions.bound_g`: uniform boundedness across blocks.
    Intuition: no block has arbitrarily large magnitude, ensuring all block moments exist.
    Formal: `∀ b, ∃ C, 0 ≤ C ∧ ∀ a, |g b a| ≤ C`.

## SampleSplitting

- `SplitEvalWeightAssumptions`: weighted evaluation-stage assumptions for sample splitting.
  For a fixed training index `m`, the estimated score `gHat g θhat m` is treated as
  a fixed [score](jargon_score.md), and the evaluation draws are paired with weights
  `w` so that weighted LLNs apply. This lets the weighted empirical
  [standard deviation](jargon_standard_deviation.md) of the estimated score
  [converge](jargon_convergence.md) to the population SD target.
  - `SplitEvalWeightAssumptions.hScore`: unweighted score assumptions for `gHat g θhat m`.
    Formal: `ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m)`.
  - `SplitEvalWeightAssumptions.hWeight`: score assumptions for the weights `w`.
    Formal: `ScoreAssumptions (μ := μ) (A := A) (g := w)`.
  - `SplitEvalWeightAssumptions.hWeightScore`: score assumptions for the weighted score `w * gHat`.
  - `SplitEvalWeightAssumptions.hWeightScoreSq`: score assumptions for `w * (gHat)^2`.
  - `SplitEvalWeightAssumptions.hW0`: the weight mean is nonzero so ratios are well-defined.
- `SplitEvalAssumptions`: the unweighted evaluation-stage assumptions used as part of
  weighted setups. It still packages `ScoreAssumptions` for the fixed score.
- `SplitEvalAssumptionsBounded`: alternative evaluation assumptions that replace
  the full `ScoreAssumptions` bundle with a stronger, more concrete checklist:
  [measurability](jargon_measurable.md) of the fixed evaluation score
  `gHat g θhat m`, and a global bound on that score. The attribute-stream
  i.i.d. properties are supplied separately (e.g., via `ConjointRandomizationStream`)
  when converting to `ScoreAssumptions`. This is a stronger but easier-to-check
  route to the same moment conditions under the experimental design distribution `μ`.
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

Reader mapping to standard OLS assumptions:
- `OLSMomentAssumptions` / `OLSMomentAssumptionsOfAttr` correspond to LLN for
  the Gram matrix `X'X/n` and cross moments `X'Y/n`, plus invertibility/full‑rank
  of the limiting Gram, and identification via the normal equations.
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
- `ObservationNoiseAssumptions`: a paper-facing noise bundle that asserts the
  feature-weighted outcome noise averages to 0 along sample paths, relative to
  the causal score `gStar`. It also records a conditional-mean formulation
  (event-wise `condMean` on `A i = a`) to make the intended mean-zero noise
  story explicit. The LLN is stated directly for the noise cross term
  `φ(A k) * (Yobs k - gStar (A k))`, and is used to replace the noiseless
  identity `Yobs = gStar ∘ A` in the design-side OLS bundle.
- `PaperOLSDesignAssumptions`: a paper-specific bundle that is strong enough to
  *derive* the OLS LLN hypotheses for Gram and cross moments from the
  experimental design once combined with a separate `DesignAttrIID` assumption.
  It packages measurability and boundedness of the paper feature map `φPaper`,
  boundedness of the conjoint causal estimand `gStar`, the observation-noise
  LLN needed for the cross moment, and equality of the design and target
  Gram/cross moments (so LLN limits can be expressed under `ν`).
  - `PaperOLSDesignAssumptions.meas_fMain` / `meas_fInter`: measurability of
    the main/interaction feature maps.
  - `PaperOLSDesignAssumptions.bound_fMain` / `bound_fInter`: boundedness of
    each feature map (used to get integrability and LLN).
  - `PaperOLSDesignAssumptions.meas_gStar` / `bound_gStar`: measurability and
    boundedness of the conjoint causal estimand.
  - `PaperOLSDesignAssumptions.obs_noise`: an `ObservationNoiseAssumptions`
    instance specialized to the paper feature map `φPaper`, ensuring the
    noise cross term averages to 0 and the cross-moment LLN targets
    `attrCross ν gStar φPaper`.
  - `PaperOLSDesignAssumptions.gram_eq` / `cross_eq`: the design Gram/cross
    moments match the target moments under `ν`.
- `PaperOLSFullRankAssumptions`: a minimal full‑rank condition for the
  population Gram matrix of the paper feature map under `ν`. This is the
  invertibility condition needed to turn normal equations into a unique `θ0`.
  - `PaperOLSFullRankAssumptions.gram_isUnit`: the Gram matrix is invertible
    as a matrix in the ambient algebra. Intuition: the paper’s feature set has
    enough variation in the target [population](jargon_population.md).
    Formal: `IsUnit (attrGram (ν := ν) (φ := φPaper ...))`.
  The normal equations are now derived from
  [well-specification](jargon_well_specified.md) and bounded/measurable paper
  features in `ConjointSD/PaperOLSConsistency.lean`.
- `PaperOLSOrthogonalAssumptions`: an interpretable feature‑variation condition
  implying full‑rank. It says off‑diagonal feature cross moments vanish and
  each feature has nonzero second moment under `ν`, so the Gram matrix is
  diagonal with nonzero entries.
  - `PaperOLSOrthogonalAssumptions.gram_diag`: off‑diagonal cross moments are 0.
  - `PaperOLSOrthogonalAssumptions.gram_pos`: diagonal moments are nonzero.
- `PaperOLSPosDefAssumptions`: a more general feature‑variation condition that
  directly asserts the population Gram matrix is positive definite.
  - `PaperOLSPosDefAssumptions.gram_posdef`: the Gram matrix is `PosDef`, which
    implies full‑rank in `PaperOLSConsistency.lean`.

## EvaluationWeights
- `EvalWeightMatchesAttrMoments`: evaluation-weight transport assumption. It
  says the weighted mean/second moment of the evaluation draw `A 0` under `μ`
  (i.e., under `Measure.map (A 0) μ`) match the target human
  [population](jargon_population.md) moments under `ν`. This is the explicit
  bridge from an evaluation sample to population targets without assuming full
  law equality.
  - `EvalWeightMatchesAttrMoments.measA0`: `A 0` is measurable.
    Intuition: the evaluation draw is a well-defined random variable.
    Formal: `Measurable (A 0)`.
  - `EvalWeightMatchesAttrMoments.mean_eq`: weighted evaluation mean equals
    [population](jargon_population.md) mean.
    Intuition: reweighting fixes the mean target.
    Formal: `(∫ a, w a * s a ∂Measure.map (A 0) μ) / (∫ a, w a ∂Measure.map (A 0) μ) = attrMean ν s`.
  - `EvalWeightMatchesAttrMoments.m2_eq`: weighted evaluation second moment
    equals [population](jargon_population.md) second moment.
    Intuition: reweighting fixes the variance scale.
    Formal: `(∫ a, w a * (s a) ^ 2 ∂Measure.map (A 0) μ) / (∫ a, w a ∂Measure.map (A 0) μ) = attrM2 ν s`.

## ConjointIdentification

- `ConjointRandomizationStream`: randomization mechanism for the
  full attribute stream `A i` in the experiment. Each draw is generated by a
  measurable function of an i.i.d. randomization variable, and each draw is
  [independent](jargon_independent.md) of every [potential outcome](jargon_potential_outcome.md).
  This makes the profile assignments random in the experimental design.
- `NoProfileOrderEffects`: formalizes Assumption 2 by requiring potential outcomes
  for a task to be invariant under permutations of the profile order, under the
  experimental design distribution `μ`. (Hainmueller Assumption 2)
  - `NoProfileOrderEffects.permute`: invariance to permutations of profile order.
    Intuition: only the set of profiles matters, not their ordering.
    Formal: `∀ k t (π : Equiv.Perm J), Y k (permuteProfiles π t) = Y k t`.
- `ConjointIdRandomized`: a randomized-design variant under a probability
  measure `μ` (experimental design distribution). It assumes
  [measurable](jargon_measurable.md) assignment,
  uniformly bounded [potential outcomes](jargon_potential_outcome.md), and
  [independence](jargon_independent.md) between `X` and each `Y x`. Integrability
  of outcomes is derived from boundedness. (Hainmueller Assumption 3)
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

## ModelBridge

- `ApproxOracleAE` (not used for consistency or identification): a two-stage approximation assumption: a flexible score
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

## WellSpecifiedFromNoInteractions

- `FullMainEffectsTerms`: the term basis `φ` is rich enough to represent any
  additive main-effect surface (intercept plus per-attribute effects). This is
  the "full set of main-effect terms" condition used to derive
  [well-specification](jargon_well_specified.md) from `NoInteractions`.
  Intuition: the regression terms are expressive enough to match any additive
  causal surface. Formal:
  `∀ μ0 main, ∃ β, ∀ x, gLin β φ x = μ0 + ∑ k, main k (x k)`.
- `NoInteractions`: existence of an additive representation, formalizing the
  "no interactions" assumption used to justify
  [well-specification](jargon_well_specified.md).
  Intuition: only main effects matter; there are no interaction terms under the
  experimental design distribution `μ`.
  Formal:
  `∃ (μ0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V, gStar (μ := μ) (Y := Y) x = μ0 + ∑ k : K, main k (x k)`.
- `ApproxNoInteractions`: approximate additivity of `gStar` within `ε` of a
  main-effects surface.
  Intuition: interactions are small enough that an additive model is uniformly
  close to the causal target.
  Formal:
  `∃ (μ0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V,
      |gStar (μ := μ) (Y := Y) x - (μ0 + ∑ k : K, main k (x k))| ≤ ε`.
