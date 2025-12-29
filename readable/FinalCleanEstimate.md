# FinalCleanEstimate.lean

This file packages the plug-in [convergence](jargon_convergence.md) statements in clean, named forms.

Key definitions:
- `meanPlugIn`, `m2PlugIn`, `varPlugIn`, `sdPlugIn` are the plug-in population [mean](jargon_mean.md), [second moment](jargon_second_moment.md), [variance](jargon_variance.md), and [standard deviation](jargon_standard_deviation.md) when you use the estimated [parameter](jargon_parameter.md) at step `n`.

Key theorems:
- Each `*_tendsto` theorem says the plug-in quantity [converges](jargon_convergence.md) to the corresponding true population quantity, assuming `GEstimationAssumptions`.
- `sdPlugIn_consistent` is just a convenience alias for the [standard deviation](jargon_standard_deviation.md) [convergence](jargon_convergence.md) statement.

This file does not introduce new ideas; it gives clean names and proofs that directly reuse the assumptions from `EstimatedG.lean`.
