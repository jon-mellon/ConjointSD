# ApproxAssumptions

Approximation-only assumptions used by the misspecification/approximate target
results. These do not feed the main theorem chain in `main_theorem.md`.

## Transport

- `ApproxInvarianceAE`: the approximate transport condition that allows bounded
  deviations on the target [population](jargon_population.md) support.
  Intuition: the experiment score may differ from the target score by at most
  `ε` on a set of probability one under `ν_pop`, so target moments are only
  perturbed by a controlled amount. Formal:
  `∀ᵐ x ∂ν_pop, |s x - t x| ≤ ε`.

## ApproximateOracle

- `L2Approx`: an [L2](jargon_l2.md)/[RMSE](jargon_rmse.md)-style approximation assumption: the model score differs
  from the target by at most `δ` in mean-square (uses the [L2](jargon_l2.md) norm under `ν_pop`).
  Intuition: the average squared error is bounded by `δ^2`.
  Formal:
  `MemLp (fun a => gModel a - gTarget a) (ENNReal.ofReal 2) ν_pop ∧
    Real.sqrt (∫ a, |gModel a - gTarget a| ^ 2 ∂ν_pop) ≤ δ`.

## WellSpecifiedFromNoInteractions

- `ApproxNoInteractions`: approximate additivity of `gStar` within `ε` of a
  main-effects surface.
  Intuition: interactions are small enough that an additive model is uniformly
  close to the causal target.
  Formal:
  `∃ (α0 : ℝ) (main : ∀ k : K, V k → ℝ),
    ∀ x : Profile K V,
      |gStar (μexp := μexp) (Y := Y) x - (α0 + ∑ k : K, main k (x k))| ≤ ε`.
