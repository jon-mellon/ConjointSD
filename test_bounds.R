# Toy simulation: empirical bound check for SD error under approximate well-specification.
# This script simulates multiple cases and reports how often the bound holds on a test set.

set.seed(123)

simulate_case <- function(n = 2000,
                          train_frac = 0.6,
                          valid_frac = 0.2,
                          beta = c(1, 2, -1.5),
                          inter = 2.0,
                          noise_sd = 0.5) {
  # Generate bounded features so a true uniform bound C exists.
  X1 <- runif(n, min = -1, max = 1)
  X2 <- runif(n, min = -1, max = 1)
  # True function (gStar) includes interaction.
  g_star <- beta[1] + beta[2] * X1 + beta[3] * X2 + inter * X1 * X2
  # Observed outcomes with noise (only used for fitting).
  y <- g_star + rnorm(n, sd = noise_sd)

  df <- data.frame(y, X1, X2)

  # Split indices
  idx <- sample(seq_len(n))
  n_train <- floor(train_frac * n)
  n_valid <- floor(valid_frac * n)
  train_idx <- idx[seq_len(n_train)]
  valid_idx <- idx[(n_train + 1):(n_train + n_valid)]
  test_idx  <- idx[(n_train + n_valid + 1):n]

  train <- df[train_idx, ]
  valid <- df[valid_idx, ]
  test  <- df[test_idx, ]

  # Fit linear model (misspecified) and richer model (includes interaction)
  fit_lin  <- lm(y ~ X1 + X2, data = train)
  fit_rich <- lm(y ~ X1 * X2, data = train)

  # Predict on validation and test
  pred_lin_valid  <- predict(fit_lin, newdata = valid)
  pred_rich_valid <- predict(fit_rich, newdata = valid)

  pred_lin_test  <- predict(fit_lin, newdata = test)
  pred_rich_test <- predict(fit_rich, newdata = test)

  # True gStar on test data
  g_star_test <- beta[1] + beta[2] * test$X1 + beta[3] * test$X2 + inter * test$X1 * test$X2
  # True linear (misspecified) target on test data (no interaction term).
  g_lin_true_test <- beta[1] + beta[2] * test$X1 + beta[3] * test$X2

  # Exact (theoretical) uniform bounds implied by the data-generating process.
  # Since |X1|,|X2| <= 1, we have |g_star| <= |beta0|+|beta1|+|beta2|+|inter|.
  # This is a true uniform bound and matches the lemma's assumptions.
  C_true <- abs(beta[1]) + abs(beta[2]) + abs(beta[3]) + abs(inter)

  # Exact uniform approximation error: g_star - g_lin = inter * X1 * X2,
  # so |g_star - g_lin| <= |inter| on the bounded domain.
  delta_true <- abs(inter)

  # SD differences on test:
  # - "total" uses fitted predictions (includes sampling error).
  # - "model" uses true functions (misspecification only).
  sd_lin_fit  <- sd(pred_lin_test)
  sd_star     <- sd(g_star_test)
  sd_lin_true <- sd(g_lin_true_test)
  sd_diff_total <- abs(sd_lin_fit - sd_star)
  sd_diff_model <- abs(sd_lin_true - sd_star)

  # Bound value from the proved lemma (using true C and true delta).
  bound_true <- sqrt(4 * C_true * delta_true)

  list(
    sd_diff_total = sd_diff_total,
    sd_diff_model = sd_diff_model,
    C_true = C_true,
    delta_true = delta_true,
    bound_true = bound_true
  )
}

run_simulation <- function(cases = c(0, 0.5, 1, 2, 3), reps = 50) {
  results <- list()
  for (inter in cases) {
    sd_diff <- numeric(reps)
    sd_diff_model <- numeric(reps)
    b_true <- numeric(reps)

    for (r in seq_len(reps)) {
      out <- simulate_case(inter = inter)
      sd_diff[r] <- out$sd_diff_total
      sd_diff_model[r] <- out$sd_diff_model
      b_true[r] <- out$bound_true
    }

    results[[as.character(inter)]] <- list(
      inter = inter,
      mean_sd_diff_total = mean(sd_diff),
      mean_sd_diff_model = mean(sd_diff_model),
      mean_bound_true = mean(b_true),
      fail_rate_true_total = mean(sd_diff > b_true),
      fail_rate_true_model = mean(sd_diff_model > b_true)
    )
  }
  results
}

results <- run_simulation()

cat("Simulation summary (by interaction strength):\n")
for (k in names(results)) {
  r <- results[[k]]
  cat("\nInteraction:", r$inter, "\n")
  cat("  mean |SD_lin_fit - SD_star|:", round(r$mean_sd_diff_total, 4), "\n")
  cat("  mean |SD_lin_true - SD_star|:", round(r$mean_sd_diff_model, 4), "\n")
  cat("  mean bound (true):", round(r$mean_bound_true, 4),
      "  fail rate (total):", round(r$fail_rate_true_total, 3),
      "  fail rate (model):", round(r$fail_rate_true_model, 3), "\n")
}

cat("\nNotes:\n")
cat("- The bound uses true uniform C and delta implied by the bounded data-generating process.\n")
cat("- Features are uniform on [-1,1], so the uniform bounds are valid.\n")
cat("- 'model' fail rate checks only misspecification (true functions).\n")
cat("- 'total' fail rate includes sampling error from estimating the linear model.\n")
