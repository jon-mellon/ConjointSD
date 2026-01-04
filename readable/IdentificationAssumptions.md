# IdentificationAssumptions

Identification-only assumptions used by the conjoint identification results.

## ConjointIdentification

- `ConjointIdRandomized`: a randomized-design variant under a probability
  measure `μexp` (experimental design distribution). It assumes
  [measurable](jargon_measurable.md) assignment,
  uniformly bounded [potential outcomes](jargon_potential_outcome.md), and
  [independence](jargon_independent.md) between `X` and each `Y x`. Integrability
  of outcomes is derived from boundedness. (Hainmueller Assumption 3)
  - `ConjointIdRandomized.measX`: assignment is measurable.
    Intuition: treatment is a well-defined [random variable](jargon_random_variable.md).
    Formal: `Measurable X`.
  - `ConjointIdRandomized.measYobs`: observed outcomes are measurable.
    Intuition: outcomes are observable [random variables](jargon_random_variable.md).
    Formal: `Measurable Yobs`.
  - `ConjointIdRandomized.measY`: potential outcomes are measurable.
    Intuition: counterfactual outcomes are integrable.
    Formal: `∀ x, Measurable (Y x)`.
  - `ConjointIdRandomized.consistency`: observed equals realized potential outcome.
    Intuition: no measurement distortion.
    Formal: `∀ ω, Yobs ω = Y (X ω) ω`.
  - `ConjointIdRandomized.bounded`: uniform boundedness of potential outcomes.
    Intuition: outcomes have finite moments by design.
    Formal: `∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Y x ω| ≤ C`.
  - `ConjointIdRandomized.ignorability`: assignment is independent of each `Y x`.
    Intuition: randomization breaks confounding.
    Formal: `∀ x, (fun ω => X ω) ⟂ᵢ[μexp] (fun ω => Y x ω)`.
