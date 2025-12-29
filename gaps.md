Gaps in the formal proof relative to the paper’s causal identification and [consistency](readable/jargon_consistency.md) claims
==========================================================================================

Lean entrypoint: [ConjointSD.lean](ConjointSD.lean)

1) Conjoint identification now derived from a design schema and tied to the status survey ([ConjointIdentification.lean](ConjointSD/ConjointIdentification.lean), [StatusConjointDesign.lean](ConjointSD/StatusConjointDesign.lean), [PaperWrappers.lean](ConjointSD/PaperWrappers.lean))  
   - Added `ConjointSingleShotDesign`: gives a law `ν` for `X` with positive singleton mass, bounded/[measurable](readable/jargon_measurable.md) outcomes, [consistency](readable/jargon_consistency.md), and ignorability. Lemmas `integrable_of_bounded`, `ConjointIdRandomized.of_singleShot`, and `rand_from_randomized` derive the factorization and `ConjointIdAssumptions` from these design facts. `paper_identifies_*` now hinges on this derived path.  
   - Instantiated the fielded status conjoint: 8,500-persona uniform assignment over four task slots, [measurability](readable/jargon_measurable.md)/ignorability/boundedness proofs, and `status_id_randomized` producing the concrete `ConjointIdRandomized` assumptions.  
   - **Status:** `ConjointSD/StatusConjointDesign.lean` is currently a leaf in the DAG; its theorems are not threaded into the paper-facing identification wrappers. It should either be wired into the identification chain or pruned if the concrete design instantiation is out of scope.  
   - **Plan to wire it in (and payoff):**
     1) Add a wrapper lemma in `ConjointSD/PaperWrappers.lean` (or `ConjointSD/ConjointIdentification.lean`) that takes the status-conjoint design assumptions (e.g., `status_id_randomized` or `ConjointSingleShotDesign` specialized to status) and produces `ConjointIdAssumptions`.
     2) Use that wrapper to derive `paper_identifies_potMean_from_condMean` and `paper_identifies_amce_from_condMeans` without requiring manual identification assumptions at the top level.
     3) Export a paper-facing theorem that states identification holds for the concrete status survey instance, so downstream statements can depend on the instantiated design rather than an abstract assumption package.
     4) Update `PaperWrappers.lean` or `StatusConjointDesign.lean` documentation to point to the new “status-identification” theorem.
     - **What this buys:** closes the DAG gap by making the concrete design instantiation a usable input to the paper-facing identification results; reduces the assumption surface exposed to downstream users; makes the formalization traceable from the real survey design to the identification claims.
   - Remaining gap: the design treats each rating as depending only on the assigned persona (via `statusY`) and rules out within-set interference between the two personas shown together. The paper would need an explicit “no within-set interference” justification or a model that allows joint dependence across the paired profiles.
   - Remaining gap: the formalized outcomes are bounded real values on [0,100] and do not model the “not sure” response option or any missingness mechanism; the paper should justify treating “not sure” as ignorable or supply a modeled missingness/selection adjustment.
   - Remaining work (if needed for other surveys): replicate this instantiation for any other conjoint designs (e.g., non-status arms) and thread them through the paper-facing wrappers.

2) [Population](readable/jargon_population.md) process for attributes is assumed [i.i.d.](readable/jargon_iid.md) without justification ([SDDecompositionFromConjoint.lean](ConjointSD/SDDecompositionFromConjoint.lean), [SampleSplitting.lean](ConjointSD/SampleSplitting.lean))  
   - PopIID requires pairwise [independence](readable/jargon_independent.md) and [identical distribution](readable/jargon_identically_distributed.md) of the attribute draws A i, but the conjoint has respondent-level clustering and finite attribute pools. No proof that survey design or resampling yields these properties.  
   - To fix: Model respondent/task structure, show exchangeability/[independence](readable/jargon_independent.md) under the actual sampling and randomization, or replace with a dependence-aware [convergence](readable/jargon_convergence.md) result (e.g., triangular arrays, martingale SLLN).

3) Link the paper [estimator](readable/jargon_estimator.md) to θ̂ [convergence](readable/jargon_convergence.md) assumptions ([EstimatedG.lean](ConjointSD/EstimatedG.lean), [RegressionConsistencyBridge.lean](ConjointSD/RegressionConsistencyBridge.lean), [DeriveGEstimationAssumptions.lean](ConjointSD/DeriveGEstimationAssumptions.lean), [RegressionEstimator.lean](ConjointSD/RegressionEstimator.lean), [PaperOLSConsistency.lean](ConjointSD/PaperOLSConsistency.lean))  
   - **Now added:** an [OLS](readable/jargon_ols.md)-style [estimator](readable/jargon_estimator.md) (normal equations) with empirical Gram/cross moments, [population](readable/jargon_population.md) analogs, and a [consistency](readable/jargon_consistency.md) [theorem](readable/jargon_theorem.md) showing `θhat → θ0` from entrywise Gram/cross [convergence](readable/jargon_convergence.md) ([RegressionEstimator.lean](ConjointSD/RegressionEstimator.lean)).  
   - **Now added:** paper-specific wrappers targeting the causal estimand `gStar` using the paper [term](readable/jargon_term.md) set ([PaperOLSConsistency.lean](ConjointSD/PaperOLSConsistency.lean)), including an [a.e.](readable/jargon_almost_everywhere.md) moment package and [a.e.](readable/jargon_almost_everywhere.md) `GEstimationAssumptions` bridge.  
   - Remaining gap: the paper’s main estimates are Bayesian hierarchical regressions; the Lean path only proves consistency for an OLS-style estimator. A bridge is still needed showing that the posterior summaries used in the paper correspond to the OLS-style limits (or that the Bayesian estimator satisfies the same moment/convergence assumptions).
   - **Now added:** a derivation of the LLN piece from existing `ScoreAssumptions` (`paper_ols_lln_of_score_assumptions_ae`), but it assumes the strong noiseless link `Yobs = gStar ∘ A` on sample paths.  
   - Remaining gap: instantiate the LLN/identifiability assumptions (`PaperOLSMomentAssumptions`) from the actual status-conjoint sampling scheme (and any other arms), then supply continuity at `θ0` and thread the resulting `GEstimationAssumptions` into the paper-facing [SD](readable/jargon_standard_deviation.md) [consistency](readable/jargon_consistency.md) results.
   - **Plan to justify inverse-Gram convergence (the strong assumption):**
     1) Prove LLN for the Gram and cross moments under the status-conjoint sampling process (i.i.d. or exchangeable draws of profiles/attributes, plus boundedness or moment conditions on `φPaper`).
     2) Prove full-rank of the population Gram matrix under the target attribute law (show no linear dependence among paper features on the support of ν).
     3) Add a stability lemma: if `Gram_n → Gram` entrywise and `Gram` is invertible with a uniform lower bound on eigenvalues, then `Gram_n` is eventually invertible and `Gram_n⁻¹ → Gram⁻¹` entrywise.
   4) Use (1)–(3) to [discharge](readable/jargon_discharge.md) the inverse-Gram convergence fields in `PaperOLSMomentAssumptions`.

3.25) Paper OLS consistency is not yet wired into the block/total SD target chain  
   - The paper-specific OLS results (in `PaperOLSConsistency.lean`) yield `GEstimationAssumptions` for `gPaper`, but the downstream paper-facing wrappers target block scores (`gBlock`, `gTotal`) and the true estimand `gStar`. There is no bridge from the paper term model to the block/total chain, so the OLS path is a leaf in the Lean DAG.  
   - Plan to fix (option 2 integration):
     1) Add a lemma that specializes `gLin_eq_gTotal_blocks` to the paper term set, producing
        `gPaper θ0 = gTotal (gBlockTerm (blk := blk) (β := θ0) (φ := φPaper ...))`
        for a provided block map `blk : PaperTerm Main Inter → B`.
     2) Add a wrapper that combines `GEstimationAssumptions_of_paper_ols_moments_ae` with the
        sequential consistency theorems to obtain SD convergence for the paper-term total score.
     3) Use `wellSpecified_of_parametricMainInteractions` (or `gStar_eq_sum_blocks_of_parametricMainInteractions`)
        to connect the paper-term total score to `gStar` and reuse the existing “true target” wrappers.
     4) Thread the new bridge into `PaperWrappers.lean`/`PaperCoreEstimand.lean` so the paper-facing
        SD theorems can be instantiated directly from the paper OLS assumptions.

3.5) Assumptions that drive [SD](readable/jargon_standard_deviation.md) [consistency](readable/jargon_consistency.md) (map to Lean statements)  
   - SDDecompositionFromConjoint: `PopIID` ([i.i.d.](readable/jargon_iid.md)-type draws of A i), `ScoreAssumptions` ([measurability](readable/jargon_measurable.md) + [integrability](readable/jargon_integral.md) of g(A0), g(A0)^2).  
   - OracleSDConsistency: requires `ScoreAssumptions` and `Measure.map (A 0) μ = ν` to target `popSDAttr ν g`.  
   - SampleSplitting: `SplitEvalAssumptions` for the fixed-m plug-in score `gHat g θhat m` (reuses `ScoreAssumptions`, adds [measurability](readable/jargon_measurable.md) of A 0).  
   - EstimatedG: `GEstimationAssumptions` ([mean](readable/jargon_mean.md) and [second-moment](readable/jargon_second_moment.md) [convergence](readable/jargon_convergence.md) for `g (θhat n)` under ν).  
   - RegressionConsistencyBridge + FunctionalContinuityAssumptions: a route to discharge `GEstimationAssumptions` via `θhat → θ0` and continuity of `popMeanAttr` / `popM2Attr`.  
   - SequentialConsistency + DecompositionSequentialConsistency: bundles the above into the [sequential consistency](readable/jargon_sequential_consistency.md) [SD](readable/jargon_standard_deviation.md) [consistency](readable/jargon_consistency.md) statement used in `PaperWrappers`.
   - Exact Lean statements (see [Scratch.lean](Scratch.lean)):
     - `PopIID`:
       ```lean
       structure PopIID (A : ℕ → Ω → Attr) : Prop where
         measA : ∀ i, Measurable (A i)
         indepA : Pairwise (fun i j => IndepFun (A i) (A j) μ)
         identA : ∀ i, IdentDistrib (A i) (A 0) μ μ
       ```
     - `ScoreAssumptions`:
       ```lean
       structure ScoreAssumptions (A : ℕ → Ω → Attr) (g : Attr → ℝ) : Prop where
         popiid : PopIID (μ := μ) A
         meas_g : Measurable g
         int_g0 : Integrable (fun ω => g (A 0 ω)) μ
         int_g0_sq : Integrable (fun ω => (g (A 0 ω)) ^ 2) μ
       ```
     - `SplitEvalAssumptions`:
       ```lean
       structure SplitEvalAssumptions
           (μ : Measure Ω) (A : ℕ → Ω → Attr)
           (g : Θ → Attr → ℝ) (θhat : ℕ → Θ)
           (m : ℕ) : Prop where
         hScore : ScoreAssumptions (μ := μ) (A := A) (g := gHat g θhat m)
       ```
     - `GEstimationAssumptions`:
       ```lean
       structure GEstimationAssumptions
           (ν : Measure Attr) [IsProbabilityMeasure ν]
           (g : Θ → Attr → ℝ) (θ0 : Θ) (θhat : ℕ → Θ) : Prop where
         mean_tendsto :
             Tendsto
               (fun n => popMeanAttr ν (gHat g θhat n))
               atTop
               (nhds (popMeanAttr ν (g θ0)))
         m2_tendsto :
             Tendsto
               (fun n => popM2Attr ν (gHat g θhat n))
               atTop
               (nhds (popM2Attr ν (g θ0)))
       ```
     - `FunctionalContinuityAssumptions`:
       ```lean
       structure FunctionalContinuityAssumptions
           {Attr Θ : Type*} [MeasurableSpace Attr] [TopologicalSpace Θ]
           (ν : Measure Attr) (g : Θ → Attr → ℝ) (θ0 : Θ) : Prop where
         cont_mean : ContinuousAt (popMeanΘ (ν := ν) g) θ0
         cont_m2   : ContinuousAt (popM2Θ   (ν := ν) g) θ0
       ```
     - `sequential_consistency_ae` assumptions:
       ```lean
    (hLaw : Measure.map (A 0) μ = ν)
    (hSplit : ∀ m, SplitEvalAssumptions (μ := μ) (A := A) (g := g) (θhat := θhat) m)
    (hG : GEstimationAssumptions (ν := ν) (g := g) (θ0 := θ0) (θhat := θhat))
      ```
   - Boundedness simplifications (new wrappers):
     - `scoreAssumptions_of_bounded` lets you replace integrability hypotheses with measurability + uniform bounds.
     - `SplitEvalAssumptionsBounded` + `splitEvalAssumptions_of_bounded` do the same for the evaluation stage.
     - Paper-facing bounded variants: `paper_sd_blocks_sequential_consistency_ae_of_bounded`,
       `paper_sd_total_sequential_consistency_ae_of_bounded`,
       `paper_sd_blocks_and_total_sequential_consistency_ae_of_bounded`.

4) [Block](readable/jargon_block.md)/[term](readable/jargon_term.md) well-specification is assumed, not proved ([ModelBridge.lean](ConjointSD/ModelBridge.lean), [WellSpecifiedFromNoInteractions.lean](ConjointSD/WellSpecifiedFromNoInteractions.lean), [TrueBlockEstimand.lean](ConjointSD/TrueBlockEstimand.lean), [PaperCoreEstimand.lean](ConjointSD/PaperCoreEstimand.lean))  
   - **Added:** explicit encoding of the paper’s [regression](readable/jargon_regression.md): [term](readable/jargon_term.md) set `PaperTerm` (intercept + main effects + listed interactions), coefficient/feature maps `βPaper`/`φPaper`, and assumptions `ParametricMainInteractions` in ModelBridge. `wellSpecified_of_parametricMainInteractions` and `gStar_eq_sum_blocks_of_parametricMainInteractions` now let us discharge well-specification and bridge to [block](readable/jargon_block.md) sums once we provide the actual [regression](readable/jargon_regression.md) features/coefs and [term](readable/jargon_term.md)→[block](readable/jargon_block.md) map.  
   - **Added:** approximation-bound variant: `ApproxWellSpecified`/`ApproxWellSpecifiedAE` in ModelBridge, plus `ApproxInvarianceAE`/`BoundedAE` and popSD error bounds in TargetEquivalence, with paper-facing wrappers for approximate [block](readable/jargon_block.md)/total [SD](readable/jargon_standard_deviation.md) targets in PaperWrappers.  
   - Remaining gap: instantiate `β0`, `βMain`, `βInter`, `fMain`, `fInter`, and the paper’s [block](readable/jargon_block.md) map for the status conjoint (and any other arms), and supply concrete bounds (C, δ) or [variance](readable/jargon_variance.md) nonnegativity needed to apply the approximation lemmas.

5) [Sequential consistency](readable/jargon_sequential_consistency.md) proofs do not connect to the paper’s sampling/estimation workflow ([SequentialConsistency.lean](ConjointSD/SequentialConsistency.lean), [DecompositionSequentialConsistency.lean](ConjointSD/DecompositionSequentialConsistency.lean), [PaperWrappers.lean](ConjointSD/PaperWrappers.lean))  
   - Sequential results require SplitEvalAssumptions ([i.i.d.](readable/jargon_iid.md) eval sample, [integrability](readable/jargon_integral.md)) and `GEstimationAssumptions` but are never instantiated with the paper’s two-stage estimation (train/eval splits, number of tasks per respondent, weighting).  
   - To fix: Formalize the training/evaluation split used in the paper, show the assumptions hold for that procedure, and state rates or limits for the specific m,n regimes relevant to the data size.

6) Survey weights and finite-[population](readable/jargon_population.md) targets were missing  
   - **Added:** weighted [population](readable/jargon_population.md) estimands (`weightMeanAttr`, `weightM2Attr`, `weightVarAttr`, `weightSDAttr`) plus finite-[population](readable/jargon_population.md) targets (`finitePopMean`/`finitePopSD`) in SurveyWeights. This lets existing [consistency](readable/jargon_consistency.md)/identification results be reused by swapping in the weighted/finite-pop targets.  
   - **Status:** `ConjointSD/SurveyWeights.lean` is currently a leaf in the DAG; none of its definitions are used elsewhere. It should either be pruned (if out of scope) or explicitly wired into the estimand/consistency chain (if the paper needs weighting or finite-population targets).
   - Remaining gap: instantiate the actual survey weights/nonresponse model for the status study and prove the required weighting assumptions (e.g., mass positivity, [integrability](readable/jargon_integral.md)) or link the weighted targets to a specific sampling design.

7) Main [SD](readable/jargon_standard_deviation.md) [estimator](readable/jargon_estimator.md) now defined, but not instantiated for the status conjoint  
   - **Added:** `paperTotalSDEst` (evaluation-stage [SD](readable/jargon_standard_deviation.md) [estimator](readable/jargon_estimator.md) for the [term](readable/jargon_term.md)-induced total score) and an end-to-end [sequential consistency](readable/jargon_sequential_consistency.md) wrapper `paper_total_sd_estimator_consistency_ae_of_gBTerm` in PaperCoreEstimand. This ties the [estimator](readable/jargon_estimator.md) to the paper’s total [SD](readable/jargon_standard_deviation.md) target under coefficient identification and the [sequential consistency](readable/jargon_sequential_consistency.md) assumptions.  
   - Remaining gap: specialize the [theorem](readable/jargon_theorem.md) to the status conjoint by instantiating the paper’s [term](readable/jargon_term.md) set, [block](readable/jargon_block.md) map, features, and coefficient map (`blk`, `φ`, `βOf`, `β0`) and by proving the SplitEvalAssumptions / continuity / [convergence](readable/jargon_convergence.md) hypotheses from the design.
