# SDDecompositionFromConjoint.lean

This file connects a sequence of attribute draws to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) results for any score function, and then extends that to a family of block scores.

Key definitions:
- `PopIID` packages IID assumptions for the attribute process `A` (see [iid](jargon_iid.md)).
- `Zcomp` composes attributes with a score function: `Z i = g (A i)`.
- `ScoreAssumptions` adds measurability and integrability conditions for `g`.

Main results:
- If `g` is bounded, then the integrability assumptions hold automatically.
- `iidAssumptions_Zcomp` shows that the score process `Zcomp` inherits [IID](jargon_iid.md) properties from `A`.
- `sd_component_consistent` proves the empirical [standard deviation](jargon_standard_deviation.md) of `g(A i)` [converges](jargon_convergence.md) to the population SD.
- `sd_component_consistent_of_bounded` is a convenient bounded version.

Block version:
- `DecompAssumptions` bundles boundedness and measurability for all blocks.
- `sd_block_consistent` applies the single-score result to any chosen block.

This file is the bridge from general [IID](jargon_iid.md) assumptions on the data to [standard deviation](jargon_standard_deviation.md) [consistency](jargon_consistency.md) for scores and blocks.
