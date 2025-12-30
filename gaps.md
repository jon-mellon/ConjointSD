Gaps in the formal proof relative to the paper’s causal identification and [consistency](readable/jargon_consistency.md) claims
==========================================================================================

Lean entrypoint: [ConjointSD.lean](ConjointSD.lean)

1) [Population](readable/jargon_population.md) process for attributes is assumed [i.i.d.](readable/jargon_iid.md) without justification ([SDDecompositionFromConjoint.lean](ConjointSD/SDDecompositionFromConjoint.lean), [SampleSplitting.lean](ConjointSD/SampleSplitting.lean))
   - PopIID requires pairwise [independence](readable/jargon_independent.md) and [identical distribution](readable/jargon_identically_distributed.md) of the attribute draws A i, but the conjoint has respondent-level clustering and finite attribute pools. No proof that survey design or resampling yields these properties.
   - To fix: model respondent/task structure, show exchangeability/[independence](readable/jargon_independent.md) under the actual sampling and randomization, or replace with a dependence-aware [convergence](readable/jargon_convergence.md) result (e.g., triangular arrays, martingale [SLLN](readable/jargon_lln.md)).

2) Link the paper [estimator](readable/jargon_estimator.md) to θ̂ [convergence](readable/jargon_convergence.md) assumptions ([EstimatedG.lean](ConjointSD/EstimatedG.lean), [RegressionConsistencyBridge.lean](ConjointSD/RegressionConsistencyBridge.lean), [DeriveGEstimationAssumptions.lean](ConjointSD/DeriveGEstimationAssumptions.lean), [RegressionEstimator.lean](ConjointSD/RegressionEstimator.lean), [PaperOLSConsistency.lean](ConjointSD/PaperOLSConsistency.lean))
   - Remaining gap: the paper’s main estimates are Bayesian hierarchical regressions; the Lean path only proves consistency for an OLS-style estimator. A bridge is still needed showing that the posterior summaries used in the paper correspond to the OLS-style limits (or that the Bayesian estimator satisfies the same moment/[convergence](readable/jargon_convergence.md) assumptions).
   - Remaining gap: instantiate the [LLN](readable/jargon_lln.md)/identifiability assumptions (`PaperOLSMomentAssumptions`) from the actual status-conjoint sampling scheme (and any other arms), then supply continuity at `θ0` and thread the resulting `GEstimationAssumptions` into the paper-facing [SD](readable/jargon_standard_deviation.md) [consistency](readable/jargon_consistency.md) results.
   - Remaining gap: justify inverse-Gram convergence (prove [LLN](readable/jargon_lln.md) for Gram/cross moments under the status-conjoint sampling process; prove full-rank of the population Gram matrix; show stability of inverses).

3) [Block](readable/jargon_block.md)/[term](readable/jargon_term.md) well-specification is assumed, not proved ([ModelBridge.lean](ConjointSD/ModelBridge.lean), [WellSpecifiedFromNoInteractions.lean](ConjointSD/WellSpecifiedFromNoInteractions.lean), [TrueBlockEstimand.lean](ConjointSD/TrueBlockEstimand.lean), [PaperCoreEstimand.lean](ConjointSD/PaperCoreEstimand.lean))
   - Remaining gap: instantiate `β0`, `βMain`, `βInter`, `fMain`, `fInter`, and the paper’s [block](readable/jargon_block.md) map for the status conjoint (and any other arms), and supply concrete bounds (C, δ) or [variance](readable/jargon_variance.md) nonnegativity needed to apply the approximation lemmas.
   - Empirical bound sketch (not formalized): use a sample split to estimate an approximation error ε between the linear-in-terms model and a richer benchmark, then plug ε into the approximate SD targets.

4) [Sequential consistency](readable/jargon_sequential_consistency.md) proofs do not connect to the paper’s sampling/estimation workflow ([SequentialConsistency.lean](ConjointSD/SequentialConsistency.lean), [DecompositionSequentialConsistency.lean](ConjointSD/DecompositionSequentialConsistency.lean), [PaperWrappers.lean](ConjointSD/PaperWrappers.lean))
   - Sequential results require SplitEvalAssumptions ([i.i.d.](readable/jargon_iid.md) eval sample, [integrability](readable/jargon_integral.md)) and `GEstimationAssumptions` but are never instantiated with the paper’s two-stage estimation (train/eval splits, number of tasks per respondent, weighting).
   - To fix: formalize the training/evaluation split used in the paper, show the assumptions hold for that procedure, and state rates or limits for the specific m,n regimes relevant to the data size.

5) Survey-weighted [population](readable/jargon_population.md) targets are only partially integrated
   - Current state: weighted population SD targets are defined, but the sequential [consistency](readable/jargon_consistency.md) and identification wrappers still target unweighted `popSDAttr ν`.
   - Remaining gap: instantiate the actual survey weights/nonresponse model for the status study and prove the required weighting assumptions (e.g., mass positivity, [integrability](readable/jargon_integral.md)), then connect the consistency chain to `weightSDAttr` (or a finite-[population](readable/jargon_population.md) target) for the paper’s population predictions.

6) Main [SD](readable/jargon_standard_deviation.md) [estimator](readable/jargon_estimator.md) not instantiated for the status conjoint
   - Remaining gap: specialize the [theorem](readable/jargon_theorem.md) to the status conjoint by instantiating the paper’s [term](readable/jargon_term.md) set, [block](readable/jargon_block.md) map, features, and coefficient map (`blk`, `φ`, `βOf`, `β0`) and by proving the SplitEvalAssumptions / continuity / [convergence](readable/jargon_convergence.md) hypotheses from the design.

7) Missingness and “not sure” responses are not modeled
   - The formalized outcomes are bounded real values on [0,100] and do not model the “not sure” response option or any missingness mechanism.
   - To fix: justify treating “not sure” as ignorable, or add a missingness/selection model and connect it to the [estimands](readable/jargon_estimand.md).

8) Status [estimand](readable/jargon_estimand.md) may need explicit [marginalization](readable/jargon_marginalization.md) over the paired profile
   - If outcomes depend on both profiles shown in a task, the estimand should be stated as the expected response to a focal profile, averaged over the randomized partner profile (and respondent conditions), matching standard conjoint [AMCE](readable/jargon_amce.md) targets.
   - To fix: re-express the estimand and identification statements to [marginalize](readable/jargon_marginalization.md) over the partner profile distribution, or justify a no-interference assumption if the paper targets profile-only potential outcomes.

9) Component [SD](readable/jargon_standard_deviation.md) targets require an [additive-projection](readable/jargon_additive_projection.md) definition
   - We want bounds for component SDs even when the oracle includes nonlinear/interactive structure. That requires defining components as the additive [L2](readable/jargon_l2.md) projection of the oracle onto the linear/main-effects span, with a residual capturing non-additive effects.
   - Remaining gap: formalize the projection target, prove the residual is orthogonal (so its [L2](readable/jargon_l2.md) norm equals the “nonlinear component” size), and relate the fitted OLS components to this projection (estimation error vs approximation error). Without this definition, component SDs are not identified by overall [RMSE](readable/jargon_rmse.md).

10) Empirical [RMSE](readable/jargon_rmse.md)s vs population [L2](readable/jargon_l2.md) bounds are not linked
   - The proof uses population [L2](readable/jargon_l2.md) distances under `ν`, but the R workflow computes test-set [RMSE](readable/jargon_rmse.md)s. A generalization/[LLN](readable/jargon_lln.md) step is needed to show the sample RMSE converges to the population `L2(ν)` distance (or to a weighted population target).
   - To fix: add a sample-to-population convergence lemma for the [RMSE](readable/jargon_rmse.md) estimator (possibly under the same IID/weighting assumptions as the SD consistency results), and thread it into the [L2](readable/jargon_l2.md)-approximation assumptions used in the bounds.
