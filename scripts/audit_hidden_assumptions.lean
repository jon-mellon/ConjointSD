import ConjointSD
import Lean

open Lean Core

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.'

private def cleanIdent (s : String) : String :=
  s.takeWhile isIdentChar

private def words (s : String) : List String :=
  s.split (fun c => c.isWhitespace)

private def extractDeclName (line : String) : Option String :=
  let line := line.trimLeft
  if line.startsWith "structure " then
    match words line with
    | "structure" :: name :: _ => some (cleanIdent name)
    | _ => none
  else if line.startsWith "def " then
    match words line with
    | "def" :: name :: _ => some (cleanIdent name)
    | _ => none
  else
    none

private def nameFromString (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part => Name.str acc part) Name.anonymous

private def qualifyName (s : String) : Name :=
  if s.startsWith "ConjointSD." then
    nameFromString s
  else
    nameFromString ("ConjointSD." ++ s)

private def collectConsts (e : Expr) (s : Std.HashSet Name) : Std.HashSet Name :=
  match e with
  | .const n _ => s.insert n
  | .app f a => collectConsts a (collectConsts f s)
  | .lam _ t b _ => collectConsts b (collectConsts t s)
  | .forallE _ t b _ => collectConsts b (collectConsts t s)
  | .letE _ t v b _ => collectConsts b (collectConsts v (collectConsts t s))
  | .mdata _ b => collectConsts b s
  | .proj _ _ b => collectConsts b s
  | _ => s

private def constsInExpr (e : Expr) : Std.HashSet Name :=
  collectConsts e ({} : Std.HashSet Name)

private def constsInDecl (declName : Name) : CoreM (Std.HashSet Name × Std.HashSet Name) := do
  let env <- getEnv
  let some decl := env.find? declName
    | throwError m!"unknown declaration {declName}"
  let typeConsts := constsInExpr decl.type
  let valueConsts :=
    match decl.value? with
    | some v => constsInExpr v
    | none => ({} : Std.HashSet Name)
  return (typeConsts, valueConsts)

private def readAssumptionNames (path : System.FilePath) : IO (Std.HashSet Name) := do
  let text <- IO.FS.readFile path
  let mut set : Std.HashSet Name := {}
  for line in text.splitOn "\n" do
    match extractDeclName line with
    | some nameStr => set := set.insert (qualifyName nameStr)
    | none => pure ()
  return set

private def usage : String :=
  "Usage: lake env lean --run scripts/audit_hidden_assumptions.lean [DeclName]"

def main (args : List String) : IO Unit := do
  let declNameStr :=
    match args with
    | [] =>
        "ConjointSD.paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization"
    | [s] => s
    | _ =>
        IO.eprintln usage
        return ()
  let declName := nameFromString declNameStr
  let env <- importModules #[`ConjointSD] {} (trustLevel := 1024) (loadExts := true)
  let ctx := { fileName := "", fileMap := default }
  let state := { env }
  let (typeConsts, valueConsts) <-
    (Prod.fst <$> (CoreM.toIO (ctx := ctx) (s := state) (constsInDecl declName)))
  let valueOnly := valueConsts.fold (init := ({} : Std.HashSet Name)) fun acc n =>
    if typeConsts.contains n then acc else acc.insert n
  let assumptionNames <- readAssumptionNames "ConjointSD/Assumptions.lean"
  let hidden := valueOnly.fold (init := ({} : Std.HashSet Name)) fun acc n =>
    if assumptionNames.contains n then acc.insert n else acc
  if hidden.isEmpty then
    IO.println "No hidden assumptions from ConjointSD/Assumptions.lean."
  else
    IO.println "Hidden assumptions (appear in proof term only):"
    for n in hidden.toList do
      IO.println n.toString
