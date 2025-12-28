Weaknesses and fudges in the current Lean development
======================================================

1) Assumption-as-axiom for identification (ConjointIdentification.lean)  
   - The “rand” hypothesis asserts exact factorization of conditional expectations; it is neither derived from the conjoint randomization nor justified under the survey design with multiple tasks per respondent. The positivity requirement is also assumed. This is a direct leap from desired identification to an axiom.

2) Unrealistic independence structure (SDDecompositionFromConjoint.lean, SampleSplitting.lean)  
   - PopIID enforces pairwise independence of A i; SplitEvalAssumptions inherit this. Real conjoint data are clustered within respondents and not i.i.d. across tasks. No relaxation (e.g., mixing, martingales) or clustering correction is attempted.

3) Opaque θ̂ requirements (EstimatedG.lean, RegressionConsistencyBridge.lean, DeriveGEstimationAssumptions.lean)  
   - GEstimationAssumptions demands moment convergence of g(θ̂n) without defining θ̂, its objective, or regularity conditions. The “bridge” merely repackages continuity + θ̂ → θ0 as assumptions; no rates, no stochastic equicontinuity, and no tie to the estimator actually used in the paper.

4) Well-specification assumed, not established (ModelBridge.lean, WellSpecifiedFromNoInteractions.lean, TrueBlockEstimand.lean)  
   - The code assumes the causal estimand equals a linear-in-terms model (or “no interactions”) to obtain block decompositions. There is no connection to the paper’s model selection, attribute coding, or exclusion restrictions; the assumptions are simply posited.

5) No connection to the reported estimator or data pipeline (FinalCleanEstimate.lean, PaperWrappers.lean)  
   - The “paper-facing” theorems stop at abstract convergence of sdHatZ under idealized conditions. There is no definition of the estimator actually reported in the paper (including weighting, repeated tasks, finite samples), so the Lean results do not certify the published SD estimate.

6) Missing treatment of survey weights / finite population (project-wide)  
   - All measures are unconditional population measures; weights, nonresponse, and finite-population adjustments used in survey analysis are ignored. Any weighted estimator in the paper is outside the current formalization.

7) Lack of robustness/error bounds  
   - All results are asymptotic “Tendsto” statements with exact well-specification; there are no approximation/error bounds to cover model misspecification or finite-sample behavior, which the paper likely relies on for interpretation.

8) Some files are thin wrappers without substantive proof content  
   - PaperCoreEstimand.lean, PaperWrappers.lean, FinalCleanEstimate.lean mostly re-express earlier assumptions without adding validation. They do not advance the proof beyond restating desired conclusions under unproven premises.
