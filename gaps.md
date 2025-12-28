Gaps in the formal proof relative to the paper’s causal identification and consistency claims
==========================================================================================

1) Conjoint identification not linked to the actual experiment (ConjointIdentification.lean, PaperWrappers.lean)  
   - The key “rand” assumption simply asserts conditional means equal unconditional means on each `{X = x0}` event. No derivation from the randomized conjoint design (multiple profiles per respondent, blocking, attribute-level randomization, exclusion restrictions, or SUTVA). Positivity is also assumed, not shown from the design or the realized support.  
   - To fix: Formalize the experimental assignment mechanism (per-task attribute randomization, respondent-level clustering, potential outcomes), prove that mechanism implies the “rand” factorization and positivity for all presented profiles, and include SUTVA/no-interference statements.

2) Population process for attributes is assumed i.i.d. without justification (SDDecompositionFromConjoint.lean, SampleSplitting.lean)  
   - PopIID requires pairwise independence and identical distribution of the attribute draws A i, but the conjoint has respondent-level clustering and finite attribute pools. No proof that survey design or resampling yields these properties.  
   - To fix: Model respondent/task structure, show exchangeability/independence under the actual sampling and randomization, or replace with a dependence-aware convergence result (e.g., triangular arrays, martingale SLLN).

3) No link from the estimator used in the paper to θ̂ convergence assumptions (EstimatedG.lean, RegressionConsistencyBridge.lean, DeriveGEstimationAssumptions.lean)  
   - GEstimationAssumptions (mean/m2 convergence of g(θ̂n)) are taken as hypotheses; there is no definition of the paper’s estimator θ̂, nor conditions (regularity, rate, sample splitting, concentration) showing θ̂ → θ0.  
   - To fix: Define the actual estimator (e.g., OLS/GLM on the conjoint), prove its consistency and moment convergence under the design, then instantiate GEstimationAssumptions.

4) Block/term well-specification is assumed, not proved (ModelBridge.lean, WellSpecifiedFromNoInteractions.lean, TrueBlockEstimand.lean, PaperCoreEstimand.lean)  
   - “WellSpecified” and “trueBlockScore” presuppose the causal estimand lies exactly in the linear-in-terms model with the chosen block map. No argument that the paper’s specification or exclusion restrictions imply this.  
   - To fix: Encode the paper’s parametric model (main effects/interactions actually estimated) and prove the causal estimand equals that model under stated assumptions, or relax theorems to approximation bounds.

5) Sequential consistency proofs do not connect to the paper’s sampling/estimation workflow (SequentialConsistency.lean, DecompositionSequentialConsistency.lean, PaperWrappers.lean)  
   - Sequential results require SplitEvalAssumptions (i.i.d. eval sample, integrability) and GEstimationAssumptions but are never instantiated with the paper’s two-stage estimation (train/eval splits, number of tasks per respondent, weighting).  
   - To fix: Formalize the training/evaluation split used in the paper, show the assumptions hold for that procedure, and state rates or limits for the specific m,n regimes relevant to the data size.

6) No treatment of survey weights, nonresponse, or finite-population corrections (entire project)  
   - All measures are population probability measures with no link to weighting or finite sampling; the paper’s estimates likely use survey weights and a finite target population.  
   - To fix: Define weighted estimators and show identification/consistency under the survey design and weighting scheme, or add finite-population sampling lemmas.

7) No final theorem tying everything to the reported main SD estimate  
   - Paper-facing wrappers stop at abstract convergence to popSDAttr ν (g θ0). There is no instantiation with the actual attributes, blocks, or SD quantity reported in the paper, nor a theorem that “the estimator used in the paper converges to the causal SD estimand.”  
   - To fix: Define the paper’s main SD estimator in Lean, map the paper’s blocks/terms to the abstract g/blk, and prove the end-to-end consistency/identification statement under the proved design assumptions.
