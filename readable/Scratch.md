# Scratch.lean

Lean file: [Scratch.lean](../Scratch.lean)

This is a scratchpad file. It imports the full project and prints the types of key assumptions and theorems (including derived integrability lemmas, intermediate consistency results, and paper-facing wrappers) for inspection. The list includes the design-derived OLS moment package (`paper_ols_attr_moments_of_design_ae`), the design-based total sequential-consistency wrapper (`paper_sd_total_sequential_consistency_ae_of_paper_ols_design_total_ae`), and the new moment-convergence bridges from raw parameter convergence (`attrMean_tendsto_of_theta_tendsto`, `attrM2_tendsto_of_theta_tendsto`).

It does not define new logic. It is used to quickly check the shapes of assumptions and results in Lean.
