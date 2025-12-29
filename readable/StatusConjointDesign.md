# StatusConjointDesign.lean

Lean file: [ConjointSD/StatusConjointDesign.lean](../ConjointSD/StatusConjointDesign.lean)

This file instantiates the conjoint design for the specific "status" study used in the paper.

What it sets up:
- The [profile](jargon_profile.md) space is a finite set of 8,500 feasible personas.
- There are 4 task slots per respondent.
- The design distribution over profiles is uniform (see [distribution](jargon_distribution.md)).
- The sample space is respondent x task slot x randomized profile.

Key constructions:
- `nuStatus`: the uniform [distribution](jargon_distribution.md) over the 8,500 [profiles](jargon_profile.md).
- `muTask` and `muRT`: [distributions](jargon_distribution.md) over task slots and respondent-task pairs.
- `muStatus`: the product [distribution](jargon_distribution.md) over respondent-task and profile.
- `statusX`: the assigned profile (projection from the product space).
- `statusY` and `statusYobs`: potential and observed outcomes on this space.

Main theorem:
- `status_singleShot_design` proves that this concrete setup satisfies `ConjointSingleShotDesign`.
  The proof checks [measurability](jargon_measurable.md), the assignment law, positive probability for each profile,
  bounded outcomes (0 to 100), and [independence](jargon_independent.md) between assignment and [potential outcomes](jargon_potential_outcome.md).

The file ends with a corollary `status_id_randomized` that packages this into the randomized identification assumptions.

Recent changes: minor proof refactors; statements unchanged.
