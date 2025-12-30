# Simple Lean import DAG plotter.

# install.packages(c("fs", "stringr", "dplyr", "purrr", "tidyr", "DiagrammeR",
#                    "DiagrammeRsvg", "rsvg"))

library(fs)
library(stringr)
library(dplyr)
library(purrr)
library(tidyr)
library(DiagrammeR)

# ---- config ----
project_root <- "."        # repo root
src_dirs <- c(project_root)
lean_glob <- "\\.lean$"
include_external <- FALSE  # FALSE: keep only modules that exist in repo
excluded_modules <- c("ConjointSD", "Scratch")
output_png <- path(project_root, "readable", "lean_import_dag.png")

# ---- helpers ----
read_lines_safe <- function(path) {
  tryCatch(readLines(path, warn = FALSE), error = function(e) character(0))
}

strip_lean_comments <- function(lines) {
  # Drop line comments "-- ...". Block comments "/- ... -/" ignored here.
  str_replace(lines, "--.*$", "")
}

extract_imports <- function(lines) {
  # Supports: import A.B C.D
  lines <- strip_lean_comments(lines)
  imp_lines <- lines[str_detect(lines, "^\\s*import\\s+")]
  if (length(imp_lines) == 0) return(character(0))
  
  imp_lines %>%
    str_replace("^\\s*import\\s+", "") %>%
    str_split("\\s+") %>%
    unlist() %>%
    str_trim() %>%
    discard(~ .x == "")
}

relpath_to_module <- function(relpath) {
  # Foo/Bar.lean -> Foo.Bar
  relpath %>%
    str_replace_all("\\\\", "/") %>%
    str_replace("\\.lean$", "") %>%
    str_replace_all("/", ".")
}

dot_from_edges <- function(nodes, edges, title = "Lean import DAG") {
  node_lines <- nodes %>%
    mutate(label = name) %>%
    transmute(line = sprintf('"%s" [label="%s"];', name, label)) %>%
    pull(line)
  
  edge_lines <- edges %>%
    transmute(line = sprintf('"%s" -> "%s";', from, to)) %>%
    pull(line)
  
  sprintf(
    'digraph G {
      graph [rankdir=LR, labelloc="t", label="%s", fontsize=20];
      node  [shape=box, style="rounded,filled", fillcolor="#F7F7F7", color="#444444", fontname="Helvetica"];
      edge  [color="#666666"];

      %s

      %s
    }',
    title,
    paste(node_lines, collapse = "\n"),
    paste(edge_lines, collapse = "\n")
  )
}

build_import_dag <- function() {
  lean_files <- src_dirs %>%
    map(~ dir_ls(.x, recurse = TRUE, type = "file", regexp = lean_glob)) %>%
    unlist() %>%
    unique()
  
  if (length(lean_files) == 0) stop("No .lean files found. Set project_root/src_dirs correctly.")
  
  lean_files_rel <- path_rel(lean_files, start = project_root)
  file_modules <- tibble(
    file = lean_files,
    rel  = lean_files_rel,
    mod  = relpath_to_module(lean_files_rel)
  )
  
  mods_in_repo <- unique(file_modules$mod)
  
  imports_tbl <- file_modules %>%
    mutate(imports = map(file, ~ extract_imports(read_lines_safe(.x)))) %>%
    select(mod, imports) %>%
    unnest(imports, keep_empty = TRUE) %>%
    rename(imported = imports) %>%
    filter(!is.na(imported), imported != "")
  
  if (!include_external) {
    imports_tbl <- imports_tbl %>% filter(imported %in% mods_in_repo)
  }
  
  edges_current <- imports_tbl %>%
    transmute(from = imported, to = mod) %>%
    distinct()
  
  if (length(excluded_modules) > 0) {
    edges_current <- edges_current %>%
      filter(!(from %in% excluded_modules), !(to %in% excluded_modules))
  }
  edges_current$from <- gsub("ConjointSD\\.", "", edges_current$from)
  edges_current$to <- gsub("ConjointSD\\.", "", edges_current$to)
  
  nodes_current <- tibble(name = sort(unique(c(edges_current$from, edges_current$to)))) %>%
    mutate(group = if_else(str_detect(name, "\\."), str_extract(name, "^[^.]+"), name))
  
  list(nodes = nodes_current, edges = edges_current)
}

plot_import_dag <- function(title = "Lean import DAG") {
  dag <- build_import_dag()
  grViz(dot_from_edges(dag$nodes, dag$edges, title = title))
}

write_import_dag_png <- function(output_path = output_png, title = "Lean import DAG") {
  if (!requireNamespace("DiagrammeRsvg", quietly = TRUE) ||
      !requireNamespace("rsvg", quietly = TRUE)) {
    stop("Missing packages DiagrammeRsvg/rsvg. Install them to export PNG.")
  }
  dir_create(path_dir(output_path))
  graph <- plot_import_dag(title = title)
  plot_import_dag(title = title)
  svg <- DiagrammeRsvg::export_svg(graph)
  rsvg::rsvg_png(charToRaw(svg), file = output_path)
  message("Wrote DAG PNG to: ", output_path)
  invisible(output_path)
}

if (sys.nframe() == 0) {
  write_import_dag_png()
}
