Acceptable gaps and external citations
======================================

1) Bayesian-to-OLS convergence bridge for the paper estimator
   - The paper’s main estimates are Bayesian hierarchical regressions; the Lean path only proves consistency for an OLS-style estimator. Rather than proving the Bayesian convergence in Lean, we point to standard asymptotic results showing that, under weak conditions, Bayesian posteriors concentrate around the same limit as the MLE/OLS target.
   - Sketch proof idea (Bayes-to-OLS limit under weak priors): assume the likelihood corresponds to the same linear-in-terms model used for OLS (possibly with a working Gaussian error model) and the prior is continuous, positive, and weakly informative in a neighborhood of the pseudo-true parameter. Then (i) show the empirical risk function converges uniformly to its population target by a LLN plus continuity; (ii) show the population target has a unique minimizer (identifiability / full-rank Gram); (iii) use standard posterior concentration results to show the posterior puts mass in shrinking neighborhoods of that minimizer; (iv) conclude that posterior mean/median/mode (the paper’s summaries) converge to the same limit as the OLS estimator, so they satisfy the same theta-hat convergence assumptions.
   - References for the Bayesian-to-MLE/OLS limit:
     - van der Vaart (1998), Asymptotic Statistics, Bernstein-von Mises theorem.
     - Kleijn and van der Vaart (2012), The Bernstein-von Mises theorem under misspecification (posterior concentrates at the KL minimizer).
     - Ghosal, Ghosh, and van der Vaart (2000), Convergence rates of posterior distributions (consistency under weak priors).

We cite these results to justify that the Bayesian summaries used in the paper converge to the same asymptotic target as the OLS estimator under standard regularity conditions, without re-proving the Bayesian convergence for the specific hierarchical design.

2) Status estimand marginalization over paired profiles
   - If outcomes depend on both profiles shown in a task, the estimand should be stated as the expected response to a focal profile, averaged over the randomized partner profile (and respondent conditions), matching standard conjoint AMCE targets.
   - We are not fixing this in Lean; instead we treat it as part of the transport conditions, where marginalizing over other profiles is a reasonable approximation to the true status-assigning process respondents apply when making conjoint judgments.

3) Weighted population moments are assumed
   - For weighted survey targets, we assume weighted moment matching (`WeightMatchesPopMoments`) for the relevant score.
   - For the paper, we endorse the moment-matching/weighted LLN assumptions as axioms for the target population moments.
