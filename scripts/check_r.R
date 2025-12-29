# Basic R check for the Lean import DAG script.

source("plot_proof_structure.R")

dag <- build_import_dag()

if (nrow(dag$edges) == 0) {
  stop("No import edges found. Check that the repo contains Lean files with imports.")
}

cat("R check ok:\n")
cat("  nodes:", nrow(dag$nodes), "\n")
cat("  edges:", nrow(dag$edges), "\n")
