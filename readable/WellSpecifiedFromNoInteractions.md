# WellSpecifiedFromNoInteractions.lean

This file shows that "no interactions" in the causal target implies the target fits a linear model with an intercept and main effects.

Key ideas:
- A [profile](jargon_profile.md) is a full list of attribute values.
- "No interactions" means the causal target can be written as
  constant + sum of one-at-a-time effects, with no cross-terms.

What is defined:
- `AdditiveGStar` describes the exact additive form of the causal score `gStar`.
- `NoInteractions` says there exist a constant and main-effect functions that give this additive form.
- A term set `Term := Option K` is used: `none` is the intercept term and `some k` is the main effect for attribute `k`.
- `betaMain` and `phiMain` build the coefficients and features for that term set.

Main theorem:
- `wellSpecified_of_noInteractions` constructs a linear model (see [linear model](jargon_linear_model.md)) that exactly equals the causal target whenever `NoInteractions` holds.

So the file bridges an intuitive causal assumption (additivity) to the formal "well-specified" condition used later.
