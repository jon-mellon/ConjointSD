Gaps in the formal proof relative to the paper’s causal identification and [consistency](readable/jargon_consistency.md) claims
==========================================================================================

Lean entrypoint: [ConjointSD.lean](ConjointSD.lean)

1) [Block](readable/jargon_block.md)/[term](readable/jargon_term.md) well-specification is assumed, not proved ([ModelBridge.lean](ConjointSD/ModelBridge.lean), [WellSpecifiedFromNoInteractions.lean](ConjointSD/WellSpecifiedFromNoInteractions.lean), [TrueBlockEstimand.lean](ConjointSD/TrueBlockEstimand.lean), [PaperCoreEstimand.lean](ConjointSD/PaperCoreEstimand.lean))
   - Remaining gap: instantiate `β0`, `βMain`, `βInter`, `fMain`, `fInter`, and the paper’s [block](readable/jargon_block.md) map for the status conjoint (and any other arms), and supply concrete bounds (C, δ) or [variance](readable/jargon_variance.md) nonnegativity needed to apply the approximation lemmas.
   - Empirical bound sketch (not formalized): use a sample split to estimate an approximation error ε between the linear-in-terms model and a richer benchmark, then plug ε into the approximate SD targets.

2) [Sequential consistency](readable/jargon_sequential_consistency.md) proofs do not connect to the paper’s sampling/estimation workflow ([SequentialConsistency.lean](ConjointSD/SequentialConsistency.lean), [DecompositionSequentialConsistency.lean](ConjointSD/DecompositionSequentialConsistency.lean), [PaperWrappers.lean](ConjointSD/PaperWrappers.lean))
   - Sequential results require SplitEvalAssumptions ([i.i.d.](readable/jargon_iid.md) eval sample; second-moment conditions with integrability derived under a probability measure) and `GEstimationAssumptions` but are never instantiated with the paper’s two-stage estimation (train/eval splits, number of tasks per respondent, weighting).
   - To fix: formalize the training/evaluation split used in the paper, show the assumptions hold for that procedure, and state rates or limits for the specific m,n regimes relevant to the data size.

3) Main [SD](readable/jargon_standard_deviation.md) [estimator](readable/jargon_estimator.md) not instantiated for the status conjoint
   - Remaining gap: specialize the [theorem](readable/jargon_theorem.md) to the status conjoint by instantiating the paper’s [term](readable/jargon_term.md) set, [block](readable/jargon_block.md) map, features, and coefficient map (`blk`, `φ`, `βOf`, `β0`) and by proving the SplitEvalAssumptions / continuity / [convergence](readable/jargon_convergence.md) hypotheses from the design.

4) Missingness and “not sure” responses are not modeled
   - The formalized outcomes are bounded real values on [0,100] and do not model the “not sure” response option or any missingness mechanism.
   - To fix: justify treating “not sure” as ignorable, or add a missingness/selection model and connect it to the [estimands](readable/jargon_estimand.md).
   - Patch plan (MAR/MCAR): (i) introduce a missingness indicator `R` and observed outcome `Yobs := if R=1 then Y else default`, plus a notation that treats “not sure” as `R=0`; (ii) add a bundled assumption in `ConjointSD/Assumptions.lean` for MCAR (`R ⟂ (Y, A, X)` with `P(R=1)>0`) or MAR (`R ⟂ Y | (A, X)` with positivity `P(R=1 | A, X) >= c`); (iii) show the target estimand is identifiable from observed data under MAR by rewriting expectations as `E[Y | A, X] = E[Yobs | A, X, R=1]` and then integrating over `(A, X)`; (iv) update the estimator definitions to either (a) treat missing as ignorable and use complete cases under MCAR, or (b) add inverse-probability weights `1/P(R=1 | A, X)` under MAR; (v) thread the new assumptions into the consistency theorems by replacing outcome integrability with conditional integrability given `R=1`, and adding the positivity bound needed for LLN/variance control; (vi) update docs (`readable/Assumptions.md`, any affected `readable/*.md`, `proven_statements.md`, `gaps.md`) and rerun the dependency tables.

5) Component [SD](readable/jargon_standard_deviation.md) targets require an [additive-projection](readable/jargon_additive_projection.md) definition
   - We want bounds for component SDs even when the oracle includes nonlinear/interactive structure. That requires defining components as the additive [L2](readable/jargon_l2.md) projection of the oracle onto the linear/main-effects span, with a residual capturing non-additive effects.
   - Remaining gap: formalize the projection target, prove the residual is orthogonal (so its [L2](readable/jargon_l2.md) norm equals the “nonlinear component” size), and relate the fitted OLS components to this projection (estimation error vs approximation error). Without this definition, component SDs are not identified by overall [RMSE](readable/jargon_rmse.md).

6) Empirical [RMSE](readable/jargon_rmse.md)s vs target-human-population [L2](readable/jargon_l2.md) bounds are not linked
   - The proof uses target-human-population [L2](readable/jargon_l2.md) distances under `ν`, but the R workflow computes test-set [RMSE](readable/jargon_rmse.md)s. A generalization/[LLN](readable/jargon_lln.md) step is needed to show the sample RMSE converges to the target-human-population `L2(ν)` distance (or to a weighted target-human-population target).
   - To fix: add a sample-to-target-human-population convergence lemma for the [RMSE](readable/jargon_rmse.md) estimator (possibly under the same IID/weighting assumptions as the SD consistency results), and thread it into the [L2](readable/jargon_l2.md)-approximation assumptions used in the bounds.

7) OLS cross-moment convergence is assumed rather than derived
   - The `PaperOLSLLNA.cross_tendsto` assumption is a law-of-large-numbers statement about the empirical cross moments `X'Y/n`. It is not derived from the current randomization assumptions, which only ensure randomized assignment of profiles and independence from potential outcomes.
   - To fix: either (i) add an explicit joint-draw LLN package for `(A i, Yobs i)` (independence across draws + finite second moments) and derive `cross_tendsto`, or (ii) add a cluster-level LLN (independent respondents, within-respondent dependence allowed) and derive a clustered version of `cross_tendsto` consistent with robust inference practice.

8) Functional continuity is assumed rather than derived from the linear/additive model
   - The `FunctionalContinuityAssumptions` bundle in `ConjointSD/Assumptions.lean` is currently required by several sequential consistency results, but it should follow from the paper’s linear/additive score specification plus bounded features.
   - Sketch to close the gap:
     - Prove pointwise continuity: for fixed attribute profile `a`, show `θ ↦ g θ a` is continuous for the specific model (e.g., `gPaper`, `gBlockTerm`, `gTotalΘ`) by unfolding the finite sum in `θ` and using continuity of addition/multiplication and finite sums.
     - Add a domination lemma: if the feature map is bounded or has an integrable envelope, then `|g θ a|` is uniformly dominated for all θ in a neighborhood of `θ0`, and likewise for `|g θ a|^2`.
     - Use dominated convergence to show `θ ↦ attrMeanΘ ν g` and `θ ↦ attrM2Θ ν g` are continuous at `θ0`, yielding `FunctionalContinuityAssumptions`.
     - Replace `FunctionalContinuityAssumptions` hypotheses in paper-facing theorems with the concrete linear-model + bounded-feature assumptions, and drop the standalone assumption from `ConjointSD/Assumptions.lean` once the derivation is wired through.

9) Population moment assumptions are weaker than the paper’s bounded-score intuition
   - `AttrMomentAssumptions` currently assumes only a.e. measurability and square-integrability under the target population attribute distribution `ν`. In the paper, status scores are implicitly bounded (0–100), so square-integrability should follow from boundedness plus measurability.
   - To fix: add a bounded-score assumption for population scores (or reuse existing boundedness bundles), derive `AttrMomentAssumptions.int2` from it, and replace direct `AttrMomentAssumptions` usage in paper-facing statements with the bounded version.
