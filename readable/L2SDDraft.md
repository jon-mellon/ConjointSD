# L2SDDraft.lean

Lean file: [ConjointSD/L2SDDraft.lean](../ConjointSD/L2SDDraft.lean)

Summary:
- Temporary scratchpad for an [L2](jargon_l2.md)-style [SD](jargon_standard_deviation.md) bound on population scores; not imported by the main development.
- Adds a rigorous lemma expressing `popSDAttr` as the L2 norm of the centered score, plus the underlying `popVarAttr` centering identity.
- Records a proof outline: rewrite SD as a centered L2 norm, apply the L2 triangle inequality, and combine with the existing L2 [mean](jargon_mean.md) bound.
