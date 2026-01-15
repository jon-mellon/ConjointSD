# AuditHiddenAssumptions

Lean file: [scripts/audit_hidden_assumptions.lean](../scripts/audit_hidden_assumptions.lean)

This script audits whether the proof term of a theorem mentions any constants declared
in `ConjointSD/Assumptions.lean` that do not appear in the theorem's statement. It is
meant to catch assumptions that are used only in local lemmas or proof steps and are
not visible in the theorem signature, including a transitive scan over ConjointSD
dependencies that appear in the proof term. Transitive hidden assumptions are annotated
when they are implied by structure fields in the theorem statement or derivable via
ConjointSD lemmas whose hypotheses are already assumed. It also checks that every
Prop-valued hypothesis in the theorem type whose head constant lives in `ConjointSD`
is declared in `ConjointSD/Assumptions.lean`, and reports whether the proof term relies
on `sorryAx` or any other axioms (as reported by `#print axioms`), separating `sorryAx`
from other axioms in the output.

Usage:

```bash
lake env lean --run scripts/audit_hidden_assumptions.lean \
  ConjointSD.paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization
```

If no declaration name is supplied, the script defaults to the main theorem above.
