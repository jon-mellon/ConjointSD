# Assumptions.lean

Lean file: [ConjointSD/Assumptions.lean](../ConjointSD/Assumptions.lean)

This file gathers all assumption bundles and assumption-level props in a single place
for auditability. Below is a detailed, assumption-by-assumption explanation of what
each package is asserting and why it matters.

Note on OLS: the regression section uses the standard **[consistency](jargon_consistency.md)** assumptions
([LLN](jargon_lln.md) for the [Gram matrix](jargon_gram_matrix.md) `X'X/n` and
[cross moments](jargon_cross_moment.md) `X'Y/n`, [full-rank](jargon_full_rank.md)/invertible
limit, and [normal equations](jargon_normal_equations.md) [identification](jargon_identification.md)),
not the classical Gauss–Markov/BLUE conditions.

The file depends on shared definitions in `ConjointSD/Defs.lean`.

Recent changes: [probability-measure](jargon_probability_measure.md) requirements were pushed into the moment bundles, and first-moment integrability is now derived from square-integrability where applicable.

## Notation and scope

Notation:
- `ν_pop` is reserved for the target attribute [distribution](jargon_distribution.md) of the target human
  [population](jargon_population.md). Non-target attribute laws must be written as `xiAttr` (generic)
  or `kappaDesign` (design/evaluation pushforward).
- `xiAttr` is a generic attribute distribution used in continuity/moment lemmas; in the
  first-stage OLS setting it is instantiated as `kappaDesign`. In transport statements,
  we write `ν_pop` directly (no `xiAttr`).
- `kappaDesign := Measure.map (A 0) μexp` is the [pushforward](jargon_pushforward.md) attribute law for
  the experimental design distribution.
- `kappaDesign := Measure.map (A 0) ρ` is the pushforward attribute law for
  the evaluation sample used in transport.
- `μexp` is the experimental design distribution used to fit/identify the score.
- `ρ` is the evaluation-sample law used in the SD/transport stage.
Scope: “population” always means the target human
[population](jargon_population.md). When we say “[population](jargon_population.md)
mean/variance/SD,” we mean those quantities computed with respect to `ν_pop`.

## Structural assumptions (by model choice)

These are not formalized as Lean assumption bundles; they arise from how the model is set up.

- Single-shot abstraction: each observation is treated as a standalone profile draw. This
  sidesteps any task-indexing or within-subject carryover structure. (Hainmueller Assumption 1, by omission)
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

- `AttrMomentAssumptions`: target [population](jargon_population.md) moments for
  a score function `s` under the attribute distribution `ν_pop` on `Attr`
  (the attribute distribution representing the target human
  [population](jargon_population.md)). It requires
  [almost-everywhere measurability](jargon_measurable.md) of `s` and
  [integrability](jargon_integrable.md) of `s^2`. The `s` integrability needed
  for [mean](jargon_mean.md) and [variance](jargon_variance.md) targets is
  derived from these conditions using `ν_pop univ = 1`.
  - `AttrMomentAssumptions.aemeas`: `s` is a.e. measurable under `ν_pop`,
    so `s` can be integrated and is compatible with almost-everywhere
    statements used later in transport proofs. Intuition: we only need `s` to
    be well-defined except on a `ν_pop`-null set, because target population targets
    under `ν_pop` ignore
    measure-zero deviations. Formal: `AEMeasurable s ν_pop`.
  - `AttrMomentAssumptions.int2`: `s^2` is integrable under the attribute
    distribution `ν_pop` (the target population attribute distribution). This
    supplies finite second moments, which are the input for target population
    [variance](jargon_variance.md) and [standard deviation](jargon_standard_deviation.md).
    Intuition: finite energy rules out heavy tails that would make SD undefined
    or unstable. Formal: `Integrable (fun a => (s a) ^ 2) ν_pop`.
- `EvalAttrLawEqPop`: evaluation attributes are sampled IID from the target population law `ν_pop`.
  It states each evaluation draw has law `ν_pop` under `ρ`.
  - `EvalAttrLawEqPop.measA`: each `A i` is measurable.
  - `EvalAttrLawEqPop.indepA`: evaluation draws are pairwise independent under `ρ`.
  - `EvalAttrLawEqPop.identA`: each evaluation draw has law `ν_pop`.
  Intuition: the evaluation sample is a simple random sample from the population.
- `SubjectSamplingIID`: IID experiment-subject sampling from the population law `μpop`.
  It separates the subject draw from the profile randomization.
  - `SubjectSamplingIID.measR`: subject draws are measurable.
  - `SubjectSamplingIID.indepR`: subject draws are pairwise independent under `μexp`.
  - `SubjectSamplingIID.identR`: the subject draws' distribution equals `μpop`.
  Intuition: the experiment subjects are a random sample of the target population.
- `SubjectScoreAssumptions`: measurability/boundedness of the subject-level score under `μpop`.
  - `SubjectScoreAssumptions.meas_gP`: each fixed-profile score `gP(·,x)` is measurable.
  - `SubjectScoreAssumptions.bound_gP`: each fixed-profile score `gP(·,x)` is uniformly bounded.
  Intuition: subject-level scores are well-defined and have finite means under the population law.
- `SubjectSamplingLLNStar`: pointwise LLN for subject-level scores to the experimental estimand.
  - `SubjectSamplingLLNStar.lln_gStar`: the subject-average score converges to `gStar`.
  Intuition: averaging subject scores in the experiment recovers the experiment’s causal score.
The LLN to `gPop` is derived from `SubjectSamplingIID` + `SubjectScoreAssumptions` via the strong LLN
and boundedness-driven integrability.
  The ν_pop-a.e. equality `gStar = gPop` is then *derived* by uniqueness of limits.
- `SubjectSamplingLLN`: bundles both LLN statements (`gStar` and `gPop`) in one structure.
- `BoundedAE`: uniform boundedness on the target [population](jargon_population.md)
  support. Intuition: scores stay within `C` almost everywhere under `ν_pop`, so
  moment bounds and approximation lemmas can use a global envelope. Formal:
  `∀ᵐ x ∂ν_pop, |s x| ≤ C`.
## BasicMeasure

- `ProbMeasureAssumptions` (trivial): bundles `IsProbabilityMeasure κ` as an explicit
  assumption package so theorems can avoid standalone [probability-measure](jargon_probability_measure.md)
  hypotheses. Intuition: we are working with a genuine probability law, not
  just a finite measure; the same wrapper is used for the target distribution
  `ν_pop` and the experimental design distribution `μexp` as needed. Formal:
  `IsProbabilityMeasure κ`.

## Positivity

- `EpsilonAssumptions` (trivial): bundles the positivity requirement `0 < ε` that appears
  in sequential consistency statements. This is a deterministic condition (no
  target [population](jargon_population.md)/sample measure involved).
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

- `DesignAttrIID`: [i.i.d.](jargon_iid.md)-style conditions for the attribute draw process `A`
  under the experimental design distribution `μexp` (measurability of each `A i`,
  pairwise [independence](jargon_independent.md) across draws, and
  [identically distributed](jargon_identically_distributed.md) across draws).
  Intuition: the attribute profiles are sampled in a stable, independent way
  under the design. Formal:
  `∀ i, Measurable (A i) ∧
    Pairwise (fun i j => IndepFun (A i) (A j) μexp) ∧
    ∀ i, IdentDistrib (A i) (A 0) μexp μexp`.
- `EvalAttrIID`: the same [i.i.d.](jargon_iid.md)-style conditions, but explicitly
  for an evaluation attribute stream under the evaluation law `ρ`. This is
  i.i.d. across profile draws, not a claim about independence of components
  within a single profile. It is intentionally distinct from `DesignAttrIID` so
  evaluation sampling can be assumed independently of design randomization.
- `ScoreAssumptions`: score-level [measurability](jargon_measurable.md) of
  the score function `g` plus [integrability](jargon_integrable.md) of
  `g(A 0)^2` under the experimental design distribution `μexp`. Integrability of
  `g(A 0)` is derived from the second-moment condition. [i.i.d.](jargon_iid.md)
  properties of the attribute stream are now tracked separately in
  `DesignAttrIID` (design) or `EvalAttrIID` (evaluation), and are typically
  derived from `ConjointRandomizationStream` on the design side.
  The score-based [standard deviation](jargon_standard_deviation.md) [LLN](jargon_lln.md)
  lemmas (e.g., `meanHatZ_tendsto_ae_of_score`) require both `DesignAttrIID` and
  `ScoreAssumptions`.
  - `ScoreAssumptions.meas_g`: the score `g` is measurable, so `g(A i)` is
    measurable when composed with each `A i`. Intuition: the score must be a
    well-defined observable function of attributes. Formal: `Measurable g`.
  - `ScoreAssumptions.int_g0_sq`: square-integrability of `g(A 0)`, which yields
    finite variance and supports LLN steps for SD consistency. Intuition: the
    score cannot have explosive tails if we want stable dispersion estimates.
    Formal: `Integrable (fun ω => (g (A 0 ω)) ^ 2) μexp`.
## SampleSplitting

- `SplitEvalAssumptionsBounded`: boundedness-based evaluation assumptions.
  This replaces score/integrability conditions with explicit bounds on the estimated score
  and then derives the needed moment conditions.
  - `SplitEvalAssumptionsBounded.hIID`: i.i.d. assumptions for the evaluation draws.
  - `SplitEvalAssumptionsBounded.hMeasG` / `hBoundG`: measurability and boundedness of
    `gHat g θhat m`.

## RegressionConsistencyBridge

- `FunctionalContinuityAssumptions`: [continuity](jargon_continuity.md) at `θ0`
  of the attribute-distribution [mean](jargon_mean.md) and
  [second moment](jargon_second_moment.md)
  functionals under `xiAttr`. These are the continuity inputs that let
  [regression](jargon_regression.md) [consistency](jargon_consistency.md)
  translate estimator [convergence](jargon_convergence.md) into moment
  [convergence](jargon_convergence.md). In the first-stage OLS setting, take
  `xiAttr := kappaDesign`; in the transport stage, use the target population `ν_pop`.
  - `FunctionalContinuityAssumptions.cont_mean`: mean functional is continuous at `θ0`.
    Intuition: small parameter perturbations do not change the mean much.
    Formal: `ContinuousAt (attrMeanΘ (xiAttr := xiAttr) g) θ0`.
  - `FunctionalContinuityAssumptions.cont_m2`: second-moment functional is continuous at `θ0`.
    Intuition: the scale of the score changes smoothly with parameters.
    Formal: `ContinuousAt (attrM2Θ (xiAttr := xiAttr) g) θ0`.
- `PlugInMomentAssumptions`: direct plug-in convergence of the attribute-distribution
  mean and second moment under `ν_pop` for `gHat g θhat n`. This is the Route‑1 input:
  we assume moment convergence outright, without relying on parameter continuity.
  - `PlugInMomentAssumptions.mean_tendsto`: mean convergence to the oracle mean.
    Formal: `Tendsto (fun n => attrMean ν_pop (gHat g θhat n)) atTop (nhds (attrMean ν_pop (g θ0)))`.
  - `PlugInMomentAssumptions.m2_tendsto`: second-moment convergence to the oracle second moment.
    Formal: `Tendsto (fun n => attrM2 ν_pop (gHat g θhat n)) atTop (nhds (attrM2 ν_pop (g θ0)))`.
- `BlockFunctionalContinuityAssumptions`: the blockwise version of functional
  continuity, requiring the above assumptions for each block score under the
  attribute distribution `xiAttr`.
  - `BlockFunctionalContinuityAssumptions.cont`: each block score satisfies
    `FunctionalContinuityAssumptions` at `θ0`.
    Intuition: every block mean/second moment is stable under small parameter changes.
    Formal: `∀ b, FunctionalContinuityAssumptions (xiAttr := xiAttr) (blockScoreΘ (gB := gB) b) θ0`.

## RegressionEstimator

Reader mapping to standard OLS assumptions:
- `OLSMomentAssumptions` / `OLSMomentAssumptionsOfAttr` correspond to [LLN](jargon_lln.md) for
  the [Gram matrix](jargon_gram_matrix.md) `X'X/n` and [cross moments](jargon_cross_moment.md) `X'Y/n`,
  plus invertibility/[full‑rank](jargon_full_rank.md) of the limiting Gram.
  [Identification](jargon_identification.md) via the [normal equations](jargon_normal_equations.md) is handled
  separately.
- `OLSMomentAssumptions`: a deterministic moment-limit package. It posits limits
  for the inverse [Gram matrix](jargon_gram_matrix.md) and [cross-product](jargon_cross_moment.md) vector. This is the generic,
  non-target [population](jargon_population.md) formulation (purely sample-side limits
  under the experimental design distribution `μexp`).
  - `OLSMomentAssumptions.gramInvLimit`: limit of inverse Gram entries.
    Intuition: the design stabilizes to a fixed geometry.
    Social‑science intuition: if attributes are independently randomized and feature
    coding is stable, then regressor correlations settle down, the [Gram matrix](jargon_gram_matrix.md) stays
    well‑conditioned, and its inverse converges. This becomes implausible with sparse
    cells, near‑collinearity, or designs where some features are effectively deterministic
    functions of others.
    Formal: `gramInvLimit : Matrix Term Term ℝ`.
  - `OLSMomentAssumptions.crossLimit`: limit of cross moments.
    Intuition: empirical regressor-outcome correlations stabilize.
    Social‑science intuition: with randomized features and stable outcome
    measurement, average feature–outcome associations settle to a fixed target.
    This is less plausible when outcomes drift over time, when measurement
    error is correlated with certain attributes, or when the design makes some
    feature–outcome cells too rare for stable averages.
    Scope note: this assumption only says the limit exists; it does not identify
    the limit with any population moment unless additional assumptions are added
    (e.g., `OLSMomentAssumptionsOfAttr`).
    Formal: `crossLimit : Term → ℝ`.
  - `OLSMomentAssumptions.gramInv_tendsto`: convergence of inverse Gram entries.
    Intuition: the sample inverse Gram converges entrywise.
    Social‑science intuition: repeated randomized designs produce a stable
    regressor geometry, so the inverse of the empirical feature covariance
    matrix settles down rather than exploding. This is less plausible with
    multicollinearity, sparse feature cells, or drifting feature coding.
    Scope note: this is a pure convergence claim; it does not say what the
    limit equals beyond the named object `gramInvLimit`.
    Formal:
    `∀ i j, Tendsto (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j) atTop
      (nhds (gramInvLimit i j))`.
  - `OLSMomentAssumptions.cross_tendsto`: convergence of cross-moment entries.
    Intuition: empirical cross moments converge to their limits.
    Social‑science intuition: with stable measurement and randomized attributes,
    feature–outcome correlations average out to a steady association as sample
    size grows. This is less plausible with time trends, outcome drift, or
    rare feature levels that make cross moments noisy. Scope note: this only
    asserts convergence to `crossLimit`, not that the limit equals any
    population cross moment unless additional assumptions are imposed.
    Formal:
    `∀ i, Tendsto (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i) atTop
      (nhds (crossLimit i))`.
  - Identification note: `OLSMomentAssumptions` only fixes the limiting moments.
    Turning those limits into a specific coefficient target `θ0` requires a
    separate [identification](jargon_identification.md) step (e.g., [normal equations](jargon_normal_equations.md)
    derived from [well‑specification](jargon_well_specified.md) plus [full‑rank](jargon_full_rank.md)).
- `OLSMomentAssumptionsOfAttr`: the attribute‑distribution version of the above,
  with the limits pinned to the Gram and cross moments under a chosen attribute
  distribution `xiAttr`. Identification of `θ0` from these limits is handled separately
  (e.g., via [normal equations](jargon_normal_equations.md) and [full‑rank](jargon_full_rank.md) assumptions).
  Core‑idea note: for design‑side OLS, take `xiAttr := kappaDesign (κ := μexp)`
  and use that in `OLSMomentAssumptionsOfAttr`; the target population `ν_pop` enters
  only at the transport stage via the evaluation sampling law.
  - `OLSMomentAssumptionsOfAttr.gramInv_tendsto`: entries of the inverse sample
    [Gram matrix](jargon_gram_matrix.md) converge to the inverse
    attribute‑distribution Gram, giving the stable
    design condition needed for OLS consistency. Intuition: the regressor
    geometry stabilizes, so the estimator does not amplify noise. Formal:
    `∀ i j, Tendsto (fun n => (gramMatrix (A := A) (φ := φ) n)⁻¹ i j) atTop
      (nhds ((attrGram (xiAttr := xiAttr) (φ := φ))⁻¹ i j))`.
  - `OLSMomentAssumptionsOfAttr.cross_tendsto`: the sample [cross-moment](jargon_cross_moment.md) vector
    converges to the cross moment under the chosen attribute distribution `xiAttr`, so the
    [normal equations](jargon_normal_equations.md) converge. Intuition: the empirical correlation between
    regressors and outcomes settles to its `xiAttr`-based value (target population if
    `xiAttr = ν_pop`, design-law if `xiAttr = kappaDesign`).
    Formal:
    `∀ i, Tendsto (fun n => crossVec (A := A) (Y := Y) (φ := φ) n i) atTop
      (nhds (attrCross (xiAttr := xiAttr) (g := g) (φ := φ) i))`.
- `ObservationNoiseAssumptions`: a paper-facing noise bundle that asserts the
  feature-weighted outcome noise averages to 0 along sample paths, relative to
  the causal score `gStar`. It also records a conditional-mean formulation
  (event-wise `condMean` on `A i = a`) to make the intended mean-zero noise
  story explicit. The LLN is stated directly for the noise cross term
  `φ(A k) * (Yobs k - gStar (A k))`, and is used to replace the noiseless
  identity `Yobs = gStar ∘ A` in the design-side OLS bundle.
  - `ObservationNoiseAssumptions.condMean_zero`: conditional mean-zero noise.
    Intuition: conditional on the assigned profile, residual outcome noise has no
    systematic bias (e.g., no survey mode or measurement error that correlates with
    the profile once conditioning on it).
    Formal:
    `∀ i a, condMean (κ := μexp)
        (fun ω => Yobs i ω - gStar (μexp := μexp) (Y := Y) (A i ω))
        (eventX (X := A i) a) = 0`.
  - `ObservationNoiseAssumptions.noise_lln`: feature-weighted noise averages vanish.
    Intuition: over many tasks, random noise does not line up with specific features,
    so feature-noise correlations wash out in large samples.
    Formal:
    `∀ i, ∀ᵐ ω ∂μexp, Tendsto
        (fun n : ℕ => ((n : ℝ)⁻¹) * ∑ k ∈ Finset.range n,
          φ i (A k ω) * (Yobs k ω - gStar (μexp := μexp) (Y := Y) (A k ω)))
        atTop (nhds 0)`.
- `PaperOLSDesignAssumptions`: a paper-specific bundle that is strong enough to
  *derive* the OLS LLN hypotheses for the [Gram matrix](jargon_gram_matrix.md) and
  [cross moments](jargon_cross_moment.md) from the
  experimental design once combined with a separate `DesignAttrIID` assumption.
  It packages measurability and [boundedness](jargon_boundedness.md) of the paper feature map `φPaper`,
  boundedness of the conjoint causal estimand `gStar`, and the observation-noise
  LLN needed for the cross moment. Transport to a target population distribution
  is handled separately.
  - `PaperOLSDesignAssumptions.meas_fMain` / `meas_fInter`: measurability of
    the main/interaction feature maps.
    Intuition: the coded attributes/features are clearly defined and consistently
    measured in the experiment.
    Formal: `∀ m, Measurable (fMain m)` and `∀ i, Measurable (fInter i)`.
  - `PaperOLSDesignAssumptions.bound_fMain` / `bound_fInter`: [boundedness](jargon_boundedness.md) of
    each feature map (used to get integrability and LLN).
    Intuition: features cannot take implausibly large values; the design keeps attribute
    levels within a reasonable range.
    Formal: `∀ m, ∃ C, 0 ≤ C ∧ ∀ a, |fMain m a| ≤ C` and
    `∀ i, ∃ C, 0 ≤ C ∧ ∀ a, |fInter i a| ≤ C`.
  - `PaperOLSDesignAssumptions.meas_gStar` / `bound_gStar`: measurability and
    [boundedness](jargon_boundedness.md) of the conjoint causal estimand.
    Intuition: the target outcome is well-defined for every profile and not dominated
    by extreme outliers.
    Formal: `Measurable (gStar (μexp := μexp) (Y := Y))` and
    `∃ C, 0 ≤ C ∧ ∀ a, |gStar (μexp := μexp) (Y := Y) a| ≤ C`.
  - `PaperOLSDesignAssumptions.obs_noise`: an `ObservationNoiseAssumptions`
    instance specialized to the paper feature map `φPaper`, ensuring the
    noise cross term averages to 0 and the cross-moment LLN targets
    `attrCross kappaDesign gStar φPaper`.
    Intuition: after accounting for features, remaining noise does not systematically
    align with any feature in the design.
    Formal:
    `ObservationNoiseAssumptions
        (μexp := μexp) (A := A) (Y := Y) (Yobs := Yobs)
        (φ := φPaper (Attr := Attr) (fMain := fMain) (fInter := fInter))`.
- `PaperOLSFullRankAssumptions`: a minimal [full‑rank](jargon_full_rank.md) condition for the
  [Gram matrix](jargon_gram_matrix.md) of the paper feature map under the chosen attribute distribution
  `xiAttr` (use `xiAttr := kappaDesign (κ := μexp)` in the first-stage OLS setting). This is the invertibility
  condition needed to turn normal equations into a unique `θ0`.
  - `PaperOLSFullRankAssumptions.gram_isUnit`: the [Gram matrix](jargon_gram_matrix.md) is invertible
    as a matrix in the ambient algebra. Intuition: the paper’s feature set has
    enough variation under `xiAttr` to identify the coefficients.
    Formal: `IsUnit (attrGram (xiAttr := xiAttr) (φ := φPaper ...))`.
  The [normal equations](jargon_normal_equations.md) are now derived from
  [well-specification](jargon_well_specified.md) and bounded/measurable paper
  features in `ConjointSD/PaperOLSConsistency.lean`.
## EvaluationSampling
- `EvalAttrLawEqPop`: evaluation attributes are sampled IID from the target population law `ν_pop`.
  This is the SRS-style representativeness assumption used in the main theorem chain.
  - `EvalAttrLawEqPop.measA`: each `A i` is measurable.
    Intuition: each evaluation draw is a well-defined random variable.
    Formal: `∀ i, Measurable (A i)`.
  - `EvalAttrLawEqPop.indepA`: evaluation draws are pairwise independent under `ρ`.
    Intuition: draws are independent across indices.
    Formal: `Pairwise (fun i j => IndepFun (A i) (A j) ρ)`.
  - `EvalAttrLawEqPop.identA`: each evaluation draw has law `ν_pop`.
    Intuition: the evaluation sample is an IID draw from the population.
    Formal: `∀ i, Measure.map (A i) ρ = ν_pop`.

## ConjointIdentification

- `ConjointRandomizationStream`: randomization mechanism for the
  full attribute stream `A i` in the experiment. Each draw is generated by a
  measurable function of an [i.i.d.](jargon_iid.md) [random variable](jargon_random_variable.md), and each draw is
  [independent](jargon_independent.md) of every [potential outcome](jargon_potential_outcome.md).
  This makes the profile assignments random in the experimental design.
  Intuition: assignment uses a clean randomization device (e.g., survey randomizer)
  that is independent of subjects’ potential outcomes, so there is no selection bias.
  Formal:
  `∃ R U f, (∀ i, Measurable (U i)) ∧ Measurable f ∧ (∀ i, A i = fun ω => f (U i ω)) ∧
    Pairwise (fun i j => IndepFun (U i) (U j) μexp) ∧ (∀ i, IdentDistrib (U i) (U 0) μexp μexp) ∧
    ∀ i x, (fun ω => U i ω) ⟂ᵢ[μexp] (fun ω => Y x ω)`.
Identification-specific randomized-design assumptions now live in
`readable/IdentificationAssumptions.md`.

## Approximation-only assumptions

Approximation-specific assumptions now live in `readable/ApproxAssumptions.md`.

## WellSpecifiedFromNoInteractions

- `FullMainEffectsTerms`: the term basis `φ` is rich enough to represent any
  additive main-effect surface (intercept plus per-attribute effects). This is
  the "full set of main-effect terms" condition used to derive
  [well-specification](jargon_well_specified.md) from `NoInteractions`.
  Intuition: the regression terms are expressive enough to match any additive
  causal surface. Formal:
  `∀ α0 main, ∃ β, ∀ x, gLin β φ x = α0 + ∑ k, main k (x k)`.
- `NoInteractions`: existence of an additive representation, formalizing the
  "no interactions" assumption used to justify
  [well-specification](jargon_well_specified.md).
  Intuition: only main effects matter; there are no interaction terms under the
  experimental design distribution `μexp`.
  Formal:
  `∃ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V, gStar (μexp := μexp) (Y := Y) x = α0 + ∑ k : K, main k (x k)`.
