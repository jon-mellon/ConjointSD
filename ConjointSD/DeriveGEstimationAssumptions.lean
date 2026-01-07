/-
ConjointSD/DeriveGEstimationAssumptions.lean

Utilities to eliminate direct moment-convergence assumptions in paper-facing theorems,
by deriving them from:
  (1) θhat → θ0
  (2) continuity-at-θ0 of the attribute-distribution functionals

This file compiles independently and is meant to be imported by your paper wrapper file
(previously `FinalTheorems.lean`).
-/

import ConjointSD.RegressionConsistencyBridge

noncomputable section
namespace ConjointSD


/-!
Deprecated: plug-in moment convergence bundles are no longer assumed.
Use `attrMean_tendsto_of_theta_tendsto` and `attrM2_tendsto_of_theta_tendsto` directly.
-/

end ConjointSD
