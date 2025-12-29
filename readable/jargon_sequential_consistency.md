# Sequential consistency

Lean entrypoint: [ConjointSD.lean](../ConjointSD.lean)

Sequential [consistency](jargon_consistency.md) here means a two-step limit: first let the evaluation sample size grow (n), then let the training index grow (m). The error gets small for large n after m is large enough.
