# PaperWrappers.lean

Lean file: [ConjointSD/PaperWrappers.lean](../ConjointSD/PaperWrappers.lean)

This file provides paper-friendly wrappers around the core technical results. It mostly re-exports theorems with names and hypotheses that match the manuscript. The wrapper statements use the standard probability/convergence bundles and target attribute moments under `ν_pop`, with `EvalAttrLawEqPop` encoding the evaluation-to-population law equality needed for SD targets. Where causal scores (`gStar`) appear, they are tied to the experimental law `μexp`, separating experimental identification from population evaluation.

Identification wrappers now live in `ConjointSD/IdentificationTheorems.lean`.

Section 2: model to [blocks](jargon_block.md)
- Uses the block decomposition bridge from `ConjointSD/ModelBridge.lean` inside the end-to-end wrappers (see [linear model](jargon_linear_model.md) and [block](jargon_block.md)).

Section 3: sequential [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md)
- Provides paper-facing statements that block [standard deviations](jargon_standard_deviation.md) are sequentially [consistent](jargon_consistency.md) (see [sequential consistency](jargon_sequential_consistency.md) and [consistency](jargon_consistency.md)).
- Provides generic wrappers that accept direct mean/second‑moment convergence of the plug‑in score, while the end-to-end OLS wrappers **derive** those convergences from OLS coefficient convergence plus derived continuity of the mean/second-moment functionals under `ν_pop`.
- The main end-to-end chain now assumes boundedness for the evaluation score and derives the needed score-level integrability from those bounds.
- Adds [OLS](jargon_ols.md)-based wrappers that use the paper OLS assumptions to derive `θhat → θ0`, then derive plug‑in moment convergence under `ν_pop` from bounded/measurable paper features.
- Adds end-to-end OLS wrappers that derive well-specification from `NoInteractions` + `FullMainEffectsTerms`, use randomized assignment for identification, and then apply the experiment-subject sampling LLN bridge. In the wrapper hypotheses, the `gPop` LLN is derived from `SubjectSamplingIID` + `SubjectScoreAssumptions`, while the `gStar` LLN is assumed via `SubjectSamplingLLNStar`. The wrapper targets the block decomposition implied by the population-mean score `gPop`, and the equality `gStar = gPop` is obtained via the IID-based derivation lemmas.

Targeting the true [estimand](jargon_estimand.md):
- Uses ν_pop-a.e. equality (derived from experiment-subject sampling) to link model-implied SDs to the population targets.

In short, this file is the narrative layer: it collects the pieces into statements that match the paper's wording and flow.
