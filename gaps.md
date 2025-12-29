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
   - Remaining gap: instantiate `β0`, `βMain`, `βInter`, `fMain`, `fInter`, and the paper’s block map for the status conjoint (and any other arms), or add approximation bounds if exact equality to the regression surface is too strong.

5) Sequential consistency proofs do not connect to the paper’s sampling/estimation workflow (SequentialConsistency.lean, DecompositionSequentialConsistency.lean, PaperWrappers.lean)  
   - Sequential results require SplitEvalAssumptions (i.i.d. eval sample, integrability) and GEstimationAssumptions but are never instantiated with the paper’s two-stage estimation (train/eval splits, number of tasks per respondent, weighting).  
   - To fix: Formalize the training/evaluation split used in the paper, show the assumptions hold for that procedure, and state rates or limits for the specific m,n regimes relevant to the data size.

6) No treatment of survey weights, nonresponse, or finite-population corrections (entire project)  
   - All measures are population probability measures with no link to weighting or finite sampling; the paper’s estimates likely use survey weights and a finite target population.  
   - To fix: Define weighted estimators and show identification/consistency under the survey design and weighting scheme, or add finite-population sampling lemmas.

7) No final theorem tying everything to the reported main SD estimate  
   - Even after adding the randomized-design bridge, the paper-facing wrappers still stop at abstract convergence to `popSDAttr ν (g θ0)`. There is no instantiation with the actual attributes, blocks, or the SD quantity reported in the paper, nor a theorem that “the estimator used in the paper converges to the causal SD estimand.”  
   - To fix: Define the paper’s main SD estimator in Lean, map the paper’s blocks/terms to the abstract `g`/`blk` under the (now formalized) assignment assumptions, and prove the end-to-end consistency/identification statement for that estimator and target.
