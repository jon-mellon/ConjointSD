# ============================================================
# 2) TARGET DAG: define the “should connect” architecture and plot it
#    + optional: compare current vs target (missing / extra edges)
# ============================================================
# ============================================================
# 1) CURRENT DAG: parse Lean `import` lines and plot dependency DAG
# ============================================================

# install.packages(c("fs", "stringr", "dplyr", "purrr", "DiagrammeR"))

# install.packages(c("dplyr", "tibble", "igraph", "stringr", "purrr"))

library(dplyr)
library(tibble)
library(igraph)
library(stringr)
library(purrr)

# --------------------------
# 1) Cycle detection from an edge list (from,to)
#    Returns SCCs that contain a cycle + one witness cycle per SCC.
# --------------------------

.find_cycle_witness_in_subgraph <- function(g_sub) {
  nodes <- V(g_sub)$name
  # adjacency as named list
  adj <- setNames(vector("list", length(nodes)), nodes)
  for (v in nodes) {
    adj[[v]] <- neighbors(g_sub, v, mode = "out")$name
  }
  
  visited  <- setNames(rep(FALSE, length(nodes)), nodes)
  in_stack <- setNames(rep(FALSE, length(nodes)), nodes)
  parent   <- setNames(rep(NA_character_, length(nodes)), nodes)
  
  cycle <- NULL
  
  dfs <- function(v) {
    visited[[v]] <<- TRUE
    in_stack[[v]] <<- TRUE
    
    for (w in adj[[v]]) {
      if (!is.null(cycle)) break
      
      if (!visited[[w]]) {
        parent[[w]] <<- v
        dfs(w)
      } else if (isTRUE(in_stack[[w]])) {
        # back edge v -> w gives a cycle w ... v -> w
        path <- c(v)
        cur <- v
        while (!is.na(parent[[cur]]) && parent[[cur]] != w) {
          cur <- parent[[cur]]
          path <- c(cur, path)
        }
        if (!is.na(parent[[cur]]) && parent[[cur]] == w) {
          path <- c(w, path, w)
          cycle <<- path
        } else {
          # fallback: still return a minimal witness
          cycle <<- c(w, v, w)
        }
      }
    }
    
    in_stack[[v]] <<- FALSE
  }
  
  for (v in nodes) {
    if (!visited[[v]] && is.null(cycle)) dfs(v)
  }
  
  cycle
}


detect_cycles_from_edges <- function(edges) {
  stopifnot(all(c("from", "to") %in% names(edges)))
  edges <- edges %>% distinct(from, to)
  
  g <- graph_from_data_frame(edges, directed = TRUE)
  
  # self-loops are cycles
  self_loops <- edges %>% filter(from == to)
  
  comp  <- components(g, mode = "strong")
  memb  <- comp$membership
  sizes <- comp$csize
  
  scc_ids_with_cycle <- which(sizes > 1)
  
  scc_nodes <- if (length(scc_ids_with_cycle) == 0) {
    tibble(node = character(), scc = integer(), size = integer())
  } else {
    tibble(
      node = V(g)$name,
      scc  = memb[V(g)],
      size = sizes[memb[V(g)]]
    ) %>%
      filter(scc %in% scc_ids_with_cycle) %>%
      arrange(desc(size), scc, node)
  }
  
  # witness-finder from earlier (assumes you defined .find_cycle_witness_in_subgraph)
  cycle_witnesses <- if (length(scc_ids_with_cycle) == 0) {
    tibble(scc = integer(), size = integer(), cycle = character())
  } else {
    map_dfr(scc_ids_with_cycle, function(cid) {
      nodes <- V(g)$name[memb[V(g)] == cid]
      g_sub <- induced_subgraph(g, vids = nodes)
      cyc <- .find_cycle_witness_in_subgraph(g_sub)
      tibble(
        scc = cid,
        size = length(nodes),
        cycle = if (is.null(cyc)) NA_character_ else paste(cyc, collapse = " -> ")
      )
    }) %>%
      arrange(desc(size), scc)
  }
  
  # add self-loop witnesses as explicit cycles
  if (nrow(self_loops) > 0) {
    loop_witnesses <- self_loops %>%
      transmute(
        scc = NA_integer_,
        size = 1L,
        cycle = paste0(from, " -> ", to)
      )
    cycle_witnesses <- bind_rows(loop_witnesses, cycle_witnesses)
  }
  
  list(
    is_dag = is_dag(g),
    has_cycle = !is_dag(g) || nrow(self_loops) > 0,
    self_loops = self_loops,
    scc_nodes = scc_nodes,
    cycle_witnesses = cycle_witnesses
  )
}

# --------------------------
# 2) Optional: build the edge list from Lean imports by scanning *.lean files
#    edges: FileModule -> ImportedModule
# --------------------------

.strip_lean_comments <- function(lines) {
  # remove line comments
  lines <- str_replace(lines, "--.*$", "")
  
  # crude block comment removal: drop content inside /- ... -/
  out <- character(0)
  in_block <- FALSE
  for (ln in lines) {
    if (!in_block) {
      if (str_detect(ln, "/-")) {
        # keep the part before block comment starts
        before <- str_split_fixed(ln, "/-", 2)[, 1]
        if (nzchar(str_trim(before))) out <- c(out, before)
        in_block <- TRUE
      } else {
        out <- c(out, ln)
      }
    } else {
      if (str_detect(ln, "-/")) {
        after <- str_split_fixed(ln, "-/", 2)[, 2]
        if (nzchar(str_trim(after))) out <- c(out, after)
        in_block <- FALSE
      }
    }
  }
  out
}

.file_to_module <- function(path, root) {
  rel <- sub(paste0("^", gsub("([\\.^$|()\\[\\]{}*+?\\\\-])", "\\\\\\1", normalizePath(root, winslash = "/")), "/?"), "", normalizePath(path, winslash = "/"))
  mod <- sub("\\.lean$", "", rel)
  mod <- gsub("/", ".", mod)
  mod
}

collect_import_edges <- function(root_dir = ".", subdir = NULL) {
  scan_root <- if (is.null(subdir)) root_dir else file.path(root_dir, subdir)
  files <- list.files(scan_root, pattern = "\\.lean$", recursive = TRUE, full.names = TRUE)
  
  edges <- map_dfr(files, function(f) {
    mod_from <- .file_to_module(f, root_dir)
    
    lines <- readLines(f, warn = FALSE)
    lines <- .strip_lean_comments(lines)
    lines <- str_trim(lines)
    lines <- lines[nzchar(lines)]
    
    # Lean: import A B C
    imp_lines <- lines[str_detect(lines, "^import\\s+")]
    if (length(imp_lines) == 0) return(tibble(from = character(0), to = character(0)))
    
    to_mods <- imp_lines %>%
      str_replace("^import\\s+", "") %>%
      str_split("\\s+") %>%
      unlist() %>%
      str_trim() %>%
      (\(x) x[nzchar(x)])()
    
    tibble(from = mod_from, to = to_mods)
  }) %>% distinct()
  
  edges
}

# --------------------------
# Example usage A: you already have an edge list "edges_current"
# result <- detect_cycles_from_edges(edges_current)
# result$is_dag
# result$self_loops
# result$cycle_witnesses
# result$scc_nodes
#
# Example usage B: scan your Lean project on disk
# edges_imports <- collect_import_edges(root_dir = ".", subdir = "ConjointSD")
# result <- detect_cycles_from_edges(edges_imports)
# result$is_dag
# result$cycle_witnesses


library(fs)
library(stringr)
library(dplyr)
library(purrr)
library(DiagrammeR)

# ---- config ----
project_root <- "."                  # <-- set to your repo root
src_dirs <- c(project_root)          # add more dirs if needed
lean_glob <- "\\.lean$"
include_external <- FALSE            # FALSE: only keep modules that exist in repo

# ---- helpers ----
read_lines_safe <- function(path) {
  tryCatch(readLines(path, warn = FALSE), error = function(e) character(0))
}

strip_lean_comments <- function(lines) {
  # Simple: drop line comments "-- ...". Block comments "/- ... -/" are ignored here.
  str_replace(lines, "--.*$", "")
}

extract_imports <- function(lines) {
  # supports: import A.B C.D
  # does not aim to parse every Lean corner case; good for typical project files.
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

module_to_relpath <- function(mod) {
  # Lean module Foo.Bar -> Foo/Bar.lean
  file.path(str_replace_all(mod, "\\.", "/"), paste0("", ".lean")) %>%
    str_replace("/\\.lean$", ".lean") %>% # safety
    str_replace_all("//+", "/")
}

relpath_to_module <- function(relpath) {
  # Foo/Bar.lean -> Foo.Bar
  relpath %>%
    str_replace_all("\\\\", "/") %>%
    str_replace("\\.lean$", "") %>%
    str_replace_all("/", ".")
}

# ---- collect Lean files ----
lean_files <- src_dirs %>%
  map(~ dir_ls(.x, recurse = TRUE, type = "file", regexp = lean_glob)) %>%
  unlist() %>%
  unique()

if (length(lean_files) == 0) stop("No .lean files found. Set project_root/src_dirs correctly.")

# map files to modules (relative to project_root)
lean_files_rel <- path_rel(lean_files, start = project_root)
file_modules <- tibble(
  file = lean_files,
  rel  = lean_files_rel,
  mod  = relpath_to_module(lean_files_rel)
)

mods_in_repo <- file_modules$mod %>% unique()

# ---- build edges from imports ----
imports_tbl <- file_modules %>%
  mutate(imports = map(file, ~ extract_imports(read_lines_safe(.x)))) %>%
  select(mod, imports) %>%
  tidyr::unnest(imports, keep_empty = TRUE) %>%
  rename(imported = imports) %>%
  filter(!is.na(imported), imported != "")

if (!include_external) {
  imports_tbl <- imports_tbl %>% filter(imported %in% mods_in_repo)
}

# Direction: imported -> importer (so arrows go from foundations to dependents)
edges_current <- imports_tbl %>%
  transmute(from = imported, to = mod) %>%
  distinct()

nodes_current <- tibble(name = sort(unique(c(edges_current$from, edges_current$to)))) %>%
  mutate(
    group = if_else(str_detect(name, "\\."), str_extract(name, "^[^.]+"), name)
  )

# ---- plot via DOT (DiagrammeR / Graphviz) ----
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
edges_current <- edges_current[edges_current$to!="ConjointSD", ]
grViz(dot_from_edges(nodes_current, edges_current, title = "Current Lean proof DAG (imports)"))

library(dplyr)
library(DiagrammeR)
 
# ---- define your intended architecture here ----
# Use Lean module names (Foo.Bar) or any labels you want.
# Arrows represent "depends on" in the same direction as the current plot:
#    foundation -> downstream
edges_target <- tibble::tribble(
  ~from, ~to,
  
  # Core definitional base
  "ConjointSD.Defs",                 "ConjointSD.PaperCoreEstimand",
  
  # Assumptions & identification inside the conjoint
  "ConjointSD.Defs",                 "ConjointSD.ConjointIdentification",
  "ConjointSD.ConjointIdentification","ConjointSD.EstimatedG",
  
  # Transport (population distribution / mapping)
  "ConjointSD.Defs",                 "ConjointSD.Transport",
  "ConjointSD.Transport",            "ConjointSD.EstimatedG",
  
  # Decomposition / variance algebra on the target scores
  "ConjointSD.PaperCoreEstimand",    "ConjointSD.VarianceDecompositionFromBlocks",
  "ConjointSD.VarianceDecompositionFromBlocks", "ConjointSD.SDDecompositionFromConjoint",
  
  # Estimation pipeline and final results
  "ConjointSD.EstimatedG",           "ConjointSD.FinalCleanEstimate"
  
) %>% distinct()

nodes_target <- tibble(name = sort(unique(c(edges_target$from, edges_target$to)))) %>%
  mutate(group = if_else(grepl("\\.", name), sub("\\..*$", "", name), name))

# ---- plot target DAG ----
dot_target <- dot_from_edges(nodes_target, edges_target, title = "Target architecture DAG (intended)")

grViz(dot_target)

# ---- OPTIONAL: compare current vs target (requires edges_current from the first script) ----
# Missing edges: in target but not in current
missing_edges <- anti_join(edges_target, edges_current, by = c("from", "to"))
# Extra edges: in current but not in target
extra_edges   <- anti_join(edges_current, edges_target, by = c("from", "to"))

# A combined comparison plot: current edges grey, missing edges red
edges_compare <- bind_rows(
  edges_current %>% mutate(color = "#999999", style = "solid", penwidth = 1),
  missing_edges %>% mutate(color = "#CC0000", style = "bold",  penwidth = 2)
) %>% distinct(from, to, .keep_all = TRUE)

nodes_compare <- tibble(name = sort(unique(c(edges_compare$from, edges_compare$to))))

dot_compare <- sprintf(
  'digraph G {
    graph [rankdir=LR, labelloc="t", label="%s", fontsize=20];
    node  [shape=box, style="rounded,filled", fillcolor="#F7F7F7", color="#444444", fontname="Helvetica"];
    %s
    %s
  }',
  "Current vs Target (red edges are missing in current)",
  paste(sprintf('"%s";', nodes_compare$name), collapse = "\n"),
  paste(sprintf('"%s" -> "%s" [color="%s", penwidth=%s];',
                edges_compare$from, edges_compare$to, edges_compare$color, edges_compare$penwidth),
        collapse = "\n")
)

grViz(dot_compare)

# Inspect differences in tabular form:
list(
  missing_in_current = missing_edges,
)
  extra_in_current   = extra_edges

result <- detect_cycles_from_edges(edges_current)
result$is_dag
result$self_loops
result$cycle_witnesses
result$scc_nodes

all_files <- list.files(recursive = TRUE, include.dirs = TRUE)
lean_files <- all_files[grepl("\\.lean", all_files)]
all_text <- ""
for(ii in lean_files) {
  all_text <- c(all_text, "", paste("File: ", ii, collapse = ""), readLines(ii))
}

writeLines(text = paste(all_text, collapse = '\n'), con = "all_lean.txt")
args(writeLines)
args(list.files)
#