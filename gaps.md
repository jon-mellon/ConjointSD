Gaps in the formal proof relative to the paper’s causal identification and consistency claims
==========================================================================================

1) Conjoint identification now derived from a design schema and tied to the status survey (ConjointIdentification.lean, StatusConjointDesign.lean, PaperWrappers.lean)  
   - Added `ConjointSingleShotDesign`: gives a law `ν` for `X` with positive singleton mass, bounded/measurable outcomes, consistency, and ignorability. Lemmas `integrable_of_bounded`, `ConjointIdRandomized.of_singleShot`, and `rand_from_randomized` derive the factorization and `ConjointIdAssumptions` from these design facts. `paper_identifies_*` now hinges on this derived path.  
   - Instantiated the fielded status conjoint: 8,500-persona uniform assignment over four task slots, measurability/ignorability/boundedness proofs, and `status_id_randomized` producing the concrete `ConjointIdRandomized` assumptions.  
   - Remaining work (if needed for other surveys): replicate this instantiation for any other conjoint designs (e.g., non-status arms) and thread them through the paper-facing wrappers.

2) Population process for attributes is assumed i.i.d. without justification (SDDecompositionFromConjoint.lean, SampleSplitting.lean)  
   - PopIID requires pairwise independence and identical distribution of the attribute draws A i, but the conjoint has respondent-level clustering and finite attribute pools. No proof that survey design or resampling yields these properties.  
   - To fix: Model respondent/task structure, show exchangeability/independence under the actual sampling and randomization, or replace with a dependence-aware convergence result (e.g., triangular arrays, martingale SLLN).

3) No link from the estimator used in the paper to θ̂ convergence assumptions (EstimatedG.lean, RegressionConsistencyBridge.lean, DeriveGEstimationAssumptions.lean)  
   - GEstimationAssumptions (mean/m2 convergence of g(θ̂n)) are taken as hypotheses; there is no definition of the paper’s estimator θ̂, nor conditions (regularity, rate, sample splitting, concentration) showing θ̂ → θ0.  
   - To fix: Define the actual estimator (e.g., OLS/GLM on the conjoint), prove its consistency and moment convergence under the design, then instantiate GEstimationAssumptions.

4) Block/term well-specification is assumed, not proved (ModelBridge.lean, WellSpecifiedFromNoInteractions.lean, TrueBlockEstimand.lean, PaperCoreEstimand.lean)  
   - **Added:** explicit encoding of the paper’s regression: term set `PaperTerm` (intercept + main effects + listed interactions), coefficient/feature maps `βPaper`/`φPaper`, and assumptions `ParametricMainInteractions` in ModelBridge. `wellSpecified_of_parametricMainInteractions` and `gStar_eq_sum_blocks_of_parametricMainInteractions` now let us discharge well-specification and bridge to block sums once we provide the actual regression features/coefs and term→block map.  
   - **Added:** approximation-bound variant: `ApproxWellSpecified`/`ApproxWellSpecifiedAE` in ModelBridge, plus `ApproxInvarianceAE`/`BoundedAE` and popSD error bounds in TargetEquivalence, with paper-facing wrappers for approximate block/total SD targets in PaperWrappers.  
   - Remaining gap: instantiate `β0`, `βMain`, `βInter`, `fMain`, `fInter`, and the paper’s block map for the status conjoint (and any other arms), and supply concrete bounds (C, δ) or var nonnegativity needed to apply the approximation lemmas.

5) Sequential consistency proofs do not connect to the paper’s sampling/estimation workflow (SequentialConsistency.lean, DecompositionSequentialConsistency.lean, PaperWrappers.lean)  
   - Sequential results require SplitEvalAssumptions (i.i.d. eval sample, integrability) and GEstimationAssumptions but are never instantiated with the paper’s two-stage estimation (train/eval splits, number of tasks per respondent, weighting).  
   - To fix: Formalize the training/evaluation split used in the paper, show the assumptions hold for that procedure, and state rates or limits for the specific m,n regimes relevant to the data size.

6) Survey weights and finite-population targets were missing  
   - **Added:** weighted population estimands (`weightMeanAttr`, `weightM2Attr`, `weightVarAttr`, `weightSDAttr`) plus finite-population targets (`finitePopMean`/`finitePopSD`) in SurveyWeights. This lets existing consistency/identification results be reused by swapping in the weighted/finite-pop targets.  
   - Remaining gap: instantiate the actual survey weights/nonresponse model for the status study and prove the required weighting assumptions (e.g., mass positivity, integrability) or link the weighted targets to a specific sampling design.

7) Main SD estimator now defined, but not instantiated for the status conjoint  
   - **Added:** `paperTotalSDEst` (evaluation-stage SD estimator for the term-induced total score) and an end-to-end sequential-consistency wrapper `paper_total_sd_estimator_consistency_ae_of_gBTerm` in PaperCoreEstimand. This ties the estimator to the paper’s total SD target under coefficient identification and the sequential-consistency assumptions.  
   - Remaining gap: specialize the theorem to the status conjoint by instantiating the paper’s term set, block map, features, and coefficient map (`blk`, `φ`, `βOf`, `β0`) and by proving the SplitEvalAssumptions / continuity / convergence hypotheses from the design.
