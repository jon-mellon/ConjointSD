# SubjectSamplingLLNFromIID

Lean file: [ConjointSD/SubjectSamplingLLNFromIID.lean](../ConjointSD/SubjectSamplingLLNFromIID.lean)

This file derives the subject-sampling LLN for the population mean from IID subject sampling and
bounded score regularity, and then packages the full LLN structure used in the main transport step.

Key pieces:
- `subject_lln_gPop_of_iid`: uses the strong law of large numbers to show that the subject-average
  score converges a.e. to `gPop` under `SubjectSamplingIID` and bounded `SubjectScoreAssumptions`.
- `subjectSamplingLLN_of_iid_of_lln_gStar`: combines the derived `gPop` LLN with the assumed
  `SubjectSamplingLLNStar` (LLN to `gStar`) to produce `SubjectSamplingLLN`.
- `subject_lln_pointwise_eq_of_iid` and `subject_lln_ae_eq_of_iid`: convert the IID + `gStar` LLN
  assumptions into `gStar = gPop` pointwise and almost-everywhere statements, so downstream
  wrappers no longer need to assume `SubjectSamplingLLN` directly.
