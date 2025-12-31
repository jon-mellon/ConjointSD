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

10) Consistency of the OLS estimator is not derived; `ThetaTendstoAssumptions` (and `GEstimationAssumptions`) are still used as premises in paper-facing results
   - Current state: we can prove `Tendsto` for `olsThetaHat` **if** `OLSMomentAssumptionsOfAttr` is given (see `ConjointSD/PaperOLSConsistency.lean`), but those moment assumptions are still assumed. As a result, downstream results often require `ThetaTendstoAssumptions` or `GEstimationAssumptions` as standalone hypotheses rather than deriving them from the experimental design.
   - Goal: derive `ThetaTendstoAssumptions` for the paper’s OLS estimator from the randomized conjoint design + measurement assumptions, then *derive* `GEstimationAssumptions` from that convergence (plus functional continuity), and finally remove both assumptions from paper-facing statements.
   - Execution plan (do not implement yet):
     - Inventory current OLS pipeline: identify the minimal lemma chain from `ScoreAssumptions` to `paper_ols_lln_of_score_assumptions_ae` to `OLSMomentAssumptionsOfAttr` to `theta_tendsto_of_paper_ols_moments`.
     - Add a single assumption bundle for OLS LLN under IID (likely in `ConjointSD/Assumptions.lean`) that packages (i) `DesignAttrIID` on `A`, (ii) measurability/boundedness of `φPaper` terms, (iii) measurability/boundedness of `gStar` (or `Yobs = gStar ∘ A`), and (iv) any integrability needed for LLN.
     - Prove helper lemmas that turn this bundle into the `ScoreAssumptions` required by `paper_ols_lln_of_score_assumptions_ae` for each Gram and cross term.
     - Use the existing `paper_ols_lln_of_score_assumptions_ae` and `paper_ols_attr_moments_of_lln_fullrank_ae` to produce `OLSMomentAssumptionsOfAttr` almost everywhere.
     - Derive `Tendsto (olsThetaHat ...)` and wrap it as `ThetaTendstoAssumptions`, or swap downstream theorems to consume the `Tendsto` statement directly.
     - Add a bridging lemma: `ThetaTendstoAssumptions` + `FunctionalContinuityAssumptions` ⇒ `GEstimationAssumptions` (or use the existing bridge in `ConjointSD/RegressionConsistencyBridge.lean` if it already provides this statement for the paper’s `g`).
     - Replace explicit `GEstimationAssumptions` premises in paper-facing results with the derived bridge lemma; only then drop `GEstimationAssumptions` from those theorem statements.
     - Only after the above is complete, replace explicit `ThetaTendstoAssumptions` premises in `PaperWrappers.lean` and other paper-facing results with the derived OLS path.
     - Update documentation (`readable/Assumptions.md`, `readable/PaperOLSConsistency.md`, `proven_statements.md`, `gaps.md`, `Scratch.lean`) and refresh `dependency_tables.Rmd` / `dependency_tables.md`.
     - Run `lake build` to validate.
   - Plan (formal work needed):
     - Add a bundled “paper OLS LLN” assumption in `ConjointSD/Assumptions.lean` (or reuse/extend existing `ScoreAssumptions`) that implies the Gram and cross LLN statements needed by `paper_ols_lln_of_score_assumptions_ae`.
     - Prove those LLN statements for each Gram/cross term from the design assumptions (iid/clustered assignments, bounded or square‑integrable features, and a noiseless or mean‑zero outcome link `Yobs = gStar ∘ A` or `E[Yobs | A] = gStar A`).
     - Use `paper_ols_attr_moments_of_lln_fullrank_ae` to package the LLN results plus full‑rank/invertibility and identification (`theta0_eq`) into `OLSMomentAssumptionsOfAttr`.
     - Apply `theta_tendsto_of_paper_ols_moments` to obtain `Tendsto (olsThetaHat ...)`, then package as `ThetaTendstoAssumptions` or use the `Tendsto` statement directly.
     - Prove or reuse the continuity bridge from `Tendsto` to moment convergence: `FunctionalContinuityAssumptions` ⇒ continuity of `attrMeanΘ` and `attrM2Θ`, then combine with `ThetaTendstoAssumptions` to yield `GEstimationAssumptions`.
     - Replace paper‑facing theorems that currently assume `GEstimationAssumptions` with the derived bridge path (usually via `GEstimationAssumptions_of_paper_ols_moments_*`).
   - Dependencies on other gaps:
     - Depends on gap (7) “OLS cross‑moment convergence is assumed rather than derived,” because that LLN is a core input to `OLSMomentAssumptionsOfAttr`.
     - Depends on gap (8) “Functional continuity is assumed rather than derived,” because the bridge to `GEstimationAssumptions` uses continuity of the population moment functionals.
     - If the derivation uses boundedness of scores/features to justify integrability for LLN, it is helped by gap (9) (bounded‑score to moment assumptions), but not strictly required if square‑integrability is assumed directly.

11) IID assumptions are more general than the paper’s design-based pipeline
   - Current state: `IIDAssumptions` is a standalone bundle for real‑valued processes and is used as the generic hypothesis in `PredictedSD.lean`, even though most paper-facing uses derive IID from the randomized attribute process via `ScoreAssumptions`/`DesignAttrIID`.
   - Goal: narrow the formal pipeline so IID is derived from the conjoint design (`A` + `g`) rather than assumed for arbitrary `Z`, aligning with the paper’s randomized-attribute logic.
   - Plan (do not implement yet):
     - Audit all uses of `IIDAssumptions` (especially in `ConjointSD/PredictedSD.lean` and any paper-facing wrappers) and classify which can be specialized to `Z := Zcomp A g` without losing needed generality.
     - Promote the existing derivation lemma (`iidAssumptions_Zcomp`) as the canonical entry point, and refactor downstream theorems to take `ScoreAssumptions`/`DesignAttrIID` (plus measurability and L2) rather than `IIDAssumptions`.
     - Keep any generic IID theorems in `ConjointSD/Assumptions.lean`, but make paper-facing results go through the design-derived path.
     - Update documentation (`readable/Assumptions.md`, `readable/PredictedSD.md`, `proven_statements.md`, `project_map.md`, `readable/lean_index.md`, `Scratch.lean`, `dependency_tables.Rmd`/`.md`) to reflect the narrower assumption flow.
     - Run `lake build` from the repo root to verify the refactor.

12) Derivable assumptions from bounded status are not centralized
   - Current state: boundedness of the status score (0–100) is implicitly used across multiple assumption bundles (e.g., `ScoreAssumptions.int_g0_sq`, `AttrMomentAssumptions.int2`, `DecompAssumptions.bound_g`), but the derivations are not recorded in one place.
   - Gap: we still require per-bundle boundedness/integrability assumptions even when the score is just status.
   - Plan (do not implement yet):
     - Add a single bounded-status assumption in `ConjointSD/Assumptions.lean` (e.g., `StatusBounded` or `StatusScoreBounded`) that formalizes `|status| ≤ 100` (or `0 ≤ status ≤ 100`) as a reusable hypothesis.
     - Prove helper lemmas for each *derivable* assumption field, naming targets explicitly:
       - `AttrMomentAssumptions.int2` (and thus `AttrMomentAssumptions.int1`) for `s := status`.
       - `ScoreAssumptions.int_g0_sq` (and thus `ScoreAssumptions.int_g0`) for `g := status` and `g := gHat ...` when `gHat` is status-only.
       - `IIDAssumptions.intZ2` (and thus `IIDAssumptions.intZ`) for `Z n := status (A n)` (or bounded transforms).
       - `DecompAssumptions.bound_g` for block scores that are status-only.
       - `SplitEvalAssumptionsBounded.hBound` for evaluation scores that are status-only.
     - Refactor call sites to use these lemmas and drop redundant boundedness assumptions where the score is status-only.
     - Update documentation (`readable/Assumptions.md`, `proven_statements.md`, `Scratch.lean`, `dependency_tables.Rmd`/`.md`, `gaps.md`) to reflect the new derived-assumption flow.
