Gaps in the formal proof relative to the paper’s causal identification and [consistency](readable/jargon_consistency.md) claims
==========================================================================================

Lean entrypoint: [ConjointSD.lean](ConjointSD.lean)

1) [Block](readable/jargon_block.md)/[term](readable/jargon_term.md) well-specification is assumed, not proved ([ModelBridge.lean](ConjointSD/ModelBridge.lean), [WellSpecifiedFromNoInteractions.lean](ConjointSD/WellSpecifiedFromNoInteractions.lean), [TrueBlockEstimand.lean](ConjointSD/TrueBlockEstimand.lean), [PaperCoreEstimand.lean](ConjointSD/PaperCoreEstimand.lean))
   - Remaining gap: instantiate `β0`, `βMain`, `βInter`, `fMain`, `fInter`, and the paper’s [block](readable/jargon_block.md) map for the status conjoint (and any other arms), and supply concrete bounds (C, δ) or [variance](readable/jargon_variance.md) nonnegativity needed to apply the approximation lemmas.
   - Empirical bound sketch (not formalized): use a sample split to estimate an approximation error ε between the linear-in-terms model and a richer benchmark, then plug ε into the approximate SD targets.

2) [Sequential consistency](readable/jargon_sequential_consistency.md) proofs do not connect to the paper’s sampling/estimation workflow ([SequentialConsistency.lean](ConjointSD/SequentialConsistency.lean), [DecompositionSequentialConsistency.lean](ConjointSD/DecompositionSequentialConsistency.lean), [PaperWrappers.lean](ConjointSD/PaperWrappers.lean))
   - Sequential results require SplitEvalAssumptions ([i.i.d.](readable/jargon_iid.md) eval sample; second-moment conditions with integrability derived under a probability measure), raw parameter convergence, and `FunctionalContinuityAssumptions`, but are never instantiated with the paper’s two-stage estimation (train/eval splits, number of tasks per respondent, weighting).
   - To fix: formalize the training/evaluation split used in the paper, show the assumptions hold for that procedure, and state rates or limits for the specific m,n regimes relevant to the data size.

3) Outcome noise is not modeled in the paper OLS design bundle
   - `PaperOLSDesignAssumptions.yobs_eq` fixes `Yobs = gStar ∘ A`, ruling out measurement error and outcome noise.
   - To fix: replace `yobs_eq` with a weaker observation model (e.g., `E[Yobs n ω | A n ω] = gStar (A n ω)` or `Yobs = gStar ∘ A + ε` with `E[ε | A] = 0` and integrability), and re-derive the cross-moment/normal-equation limits under the weaker assumption.

4) Main [SD](readable/jargon_standard_deviation.md) [estimator](readable/jargon_estimator.md) not instantiated for the status conjoint
   - Remaining gap: specialize the [theorem](readable/jargon_theorem.md) to the status conjoint by instantiating the paper’s [term](readable/jargon_term.md) set, [block](readable/jargon_block.md) map, features, and coefficient map (`blk`, `φ`, `βOf`, `β0`) and by proving the SplitEvalAssumptions / continuity / [convergence](readable/jargon_convergence.md) hypotheses from the design.

5) Missingness and “not sure” responses are not modeled
   - The formalized outcomes are bounded real values on [0,100] and do not model the “not sure” response option or any missingness mechanism.
   - To fix: justify treating “not sure” as ignorable, or add a missingness/selection model and connect it to the [estimands](readable/jargon_estimand.md).
   - Patch plan (MAR/MCAR): (i) introduce a missingness indicator `R` and observed outcome `Yobs := if R=1 then Y else default`, plus a notation that treats “not sure” as `R=0`; (ii) add a bundled assumption in `ConjointSD/Assumptions.lean` for MCAR (`R ⟂ (Y, A, X)` with `P(R=1)>0`) or MAR (`R ⟂ Y | (A, X)` with positivity `P(R=1 | A, X) >= c`); (iii) show the target estimand is identifiable from observed data under MAR by rewriting expectations as `E[Y | A, X] = E[Yobs | A, X, R=1]` and then integrating over `(A, X)`; (iv) update the estimator definitions to either (a) treat missing as ignorable and use complete cases under MCAR, or (b) add inverse-probability weights `1/P(R=1 | A, X)` under MAR; (v) thread the new assumptions into the consistency theorems by replacing outcome integrability with conditional integrability given `R=1`, and adding the positivity bound needed for LLN/variance control; (vi) update docs (`readable/Assumptions.md`, any affected `readable/*.md`, `proven_statements.md`, `gaps.md`) and rerun the dependency tables.

6) Component [SD](readable/jargon_standard_deviation.md) targets require an [additive-projection](readable/jargon_additive_projection.md) definition
   - We want bounds for component SDs even when the oracle includes nonlinear/interactive structure. That requires defining components as the additive [L2](readable/jargon_l2.md) projection of the oracle onto the linear/main-effects span, with a residual capturing non-additive effects.
   - Remaining gap: formalize the projection target, prove the residual is orthogonal (so its [L2](readable/jargon_l2.md) norm equals the “nonlinear component” size), and relate the fitted OLS components to this projection (estimation error vs approximation error). Without this definition, component SDs are not identified by overall [RMSE](readable/jargon_rmse.md).

7) Empirical [RMSE](readable/jargon_rmse.md)s vs target-human-population [L2](readable/jargon_l2.md) bounds are not linked
   - The proof uses target-human-population [L2](readable/jargon_l2.md) distances under `ν`, but the R workflow computes test-set [RMSE](readable/jargon_rmse.md)s. A generalization/[LLN](readable/jargon_lln.md) step is needed to show the sample RMSE converges to the target-human-population `L2(ν)` distance (or to a weighted target-human-population target).
   - To fix: add a sample-to-target-human-population convergence lemma for the [RMSE](readable/jargon_rmse.md) estimator (possibly under the same IID/weighting assumptions as the SD consistency results), and thread it into the [L2](readable/jargon_l2.md)-approximation assumptions used in the bounds.

8) Population moment assumptions are weaker than the paper’s bounded-score intuition
   - `AttrMomentAssumptions` currently assumes only a.e. measurability and square-integrability under the target population attribute distribution `ν`. In the paper, status scores are implicitly bounded (0–100), so square-integrability should follow from boundedness plus measurability.
   - To fix: add a bounded-score assumption for population scores (or reuse existing boundedness bundles), derive `AttrMomentAssumptions.int2` from it, and replace direct `AttrMomentAssumptions` usage in paper-facing statements with the bounded version.

9) Consistency of the OLS estimator is not derived; raw `Tendsto` for `olsThetaHat` and `FunctionalContinuityAssumptions` are still used as premises in paper-facing results
   - Current state: we can prove `Tendsto` for `olsThetaHat` **if** `OLSMomentAssumptionsOfAttr` is given (see `ConjointSD/PaperOLSConsistency.lean`). We have a design-side bundle (`PaperOLSDesignAssumptions`) together with design IID (`DesignAttrIID`) plus lemmas
     `paper_ols_lln_of_design_ae`, `paper_ols_attr_moments_of_design_ae`,
     and `theta_tendsto_of_paper_ols_design_ae`, which derive the LLN and OLS moment assumptions a.e. from design IID, bounded/measurable features, bounded `gStar`, moment transport to `ν`, and well‑specification. Inverse‑Gram stability and identification are now derived from the explicit full‑rank assumption (`PaperOLSFullRankAssumptions`) plus the derived normal equations, but those assumptions themselves are still not derived from the design.
   - New: `paper_ols_normal_eq_of_wellSpecified` derives the normal‑equation identity from well‑specification plus bounded/measurable paper features, so normal equations are no longer assumed as a standalone bundle.
   - Completed refactor: `ThetaTendstoAssumptions` and `GEstimationAssumptions` were removed from paper-facing statements. Those theorems now take raw `Tendsto (olsThetaHat ...)` and `FunctionalContinuityAssumptions` directly, with plug‑in moment convergence derived as needed.
   - Remaining work:
     - Derive `Tendsto (olsThetaHat ...)` from `PaperOLSDesignAssumptions` without assuming `OLSMomentAssumptionsOfAttr` (i.e., close the LLN/Gram/cross‑moment path from the randomized design).
     - Derive inverse‑Gram stability and identification (`hInv`, `hId`) from the design-side assumptions. We now derive `hInv` from `PaperOLSFullRankAssumptions` plus the Gram LLN and derive `hId` from the normal‑equation identity plus full‑rank; new derivations `paper_ols_fullRank_of_orthogonal` and `paper_ols_fullRank_of_posDef` show full‑rank follows from orthogonal/nondegenerate feature moments (`PaperOLSOrthogonalAssumptions`) or a positive‑definite Gram (`PaperOLSPosDefAssumptions`), but linking those conditions to the paper’s randomized design is still open.
     - Derive `FunctionalContinuityAssumptions` from the paper’s linear/additive model and bounded features (ties to gap 8), then remove it as a standalone premise in paper-facing results.
     - Re-run the documentation chain (`readable/*.md`, `proven_statements.md`, `Scratch.lean`) and refresh `dependency_tables.Rmd` / `dependency_tables.md` after those derivations.
   - Dependencies on other gaps:
     - If the derivation uses boundedness of scores/features to justify integrability for LLN, it is helped by gap (7) (bounded‑score to moment assumptions), but not strictly required if square‑integrability is assumed directly.

10) Derivable assumptions from bounded status are not centralized
   - Current state: boundedness of the status score (0–100) is implicitly used across multiple assumption bundles (e.g., `ScoreAssumptions.int_g0_sq`, `AttrMomentAssumptions.int2`, `DecompAssumptions.bound_g`), but the derivations are not recorded in one place.
   - Gap: we still require per-bundle boundedness/integrability assumptions even when the score is just status.
   - Plan (do not implement yet):
     - Add a single bounded-status assumption in `ConjointSD/Assumptions.lean` (e.g., `StatusBounded` or `StatusScoreBounded`) that formalizes `|status| ≤ 100` (or `0 ≤ status ≤ 100`) as a reusable hypothesis.
     - Prove helper lemmas for each *derivable* assumption field, naming targets explicitly:
       - `AttrMomentAssumptions.int2` (and thus `AttrMomentAssumptions.int1`) for `s := status`.
       - `ScoreAssumptions.int_g0_sq` (and thus `ScoreAssumptions.int_g0`) for `g := status` and `g := gHat ...` when `gHat` is status-only.
     - L2-integrability for `Z n := status (A n)` (or bounded transforms).
       - `DecompAssumptions.bound_g` for block scores that are status-only.
       - `SplitEvalAssumptionsBounded.hBound` for evaluation scores that are status-only.
     - Refactor call sites to use these lemmas and drop redundant boundedness assumptions where the score is status-only.
     - Update documentation (`readable/Assumptions.md`, `proven_statements.md`, `Scratch.lean`, `dependency_tables.Rmd`/`.md`, `gaps.md`) to reflect the new derived-assumption flow.
