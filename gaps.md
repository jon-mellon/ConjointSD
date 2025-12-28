Gaps in the formal proof relative to the paper’s causal identification and consistency claims
==========================================================================================

1) Conjoint identification now has a derived rand lemma but still lacks a design proof (ConjointIdentification.lean, PaperWrappers.lean)  
   - `ConjointIdRandomized` now collects measurability, positivity, integrability, boundedness, and strong ignorability, and `rand_from_randomized` derives the factorization used by `ConjointIdAssumptions`. `paper_identifies_*` consumes the derived factorization via `ConjointIdAssumptions.of_randomized`.  
   - Remaining gap: the randomized/ignorability assumptions are still taken as axioms about the assignment; there is no formal single-shot assignment mechanism or proof that the survey design implies positivity/ignorability/boundedness.  
   - To fix: formalize the assignment mechanism for profiles, prove strong ignorability and positivity from that mechanism (and boundedness/integrability of outcomes), and instantiate `ConjointIdRandomized` from those design facts so the factorization is justified rather than assumed.

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
