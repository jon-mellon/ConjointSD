# ApproxTargetEquivalence.lean

Lean file: [ConjointSD/ApproxTargetEquivalence.lean](../ConjointSD/ApproxTargetEquivalence.lean)

This file collects approximate/misspecification bounds for target population moments and SDs.

Key pieces:
- `approxInvarianceAE_triangle`: combines two ν-a.e. approximation bounds by triangle inequality.
- `attrMean_diff_le_of_L2Approx` and `attrSD_diff_le_of_L2Approx`: L2/RMSE-style bounds on mean and SD differences.
- `attrMean_diff_le_of_approx_ae`, `attrM2_diff_le_of_approx_ae`, `attrVar_diff_le_of_approx_ae`, `attrSD_diff_le_of_approx_ae`: ε-approximate bounds under `ApproxInvarianceAE` and `BoundedAE`.

These are not part of the main theorem chain; they support approximate/misspecified variants.
