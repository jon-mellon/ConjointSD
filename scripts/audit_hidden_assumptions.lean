import ConjointSD
import Lean
import Lean.Util.CollectAxioms

open Lean Core

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.'

private def cleanIdent (s : String) : String :=
  s.takeWhile isIdentChar

private def words (s : String) : List String :=
  s.splitToList (fun c => c.isWhitespace)

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

private def stripForall (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => stripForall b
  | .letE _ _ _ b _ => stripForall b
  | .mdata _ b => stripForall b
  | _ => e

private def headConst? (e : Expr) : Option Name :=
  match e with
  | .const n _ => some n
  | .app f _ => headConst? f
  | .lam _ _ b _ => headConst? b
  | .letE _ _ _ b _ => headConst? b
  | .mdata _ b => headConst? b
  | .proj _ _ b => headConst? b
  | _ => none

private def headConstAfterForalls (e : Expr) : Option Name :=
  headConst? (stripForall e)

private def propHypothesisHeadConsts (declName : Name) :
    Lean.Meta.MetaM (Std.HashSet Name) := do
  let declInfo <- getConstInfo declName
  let declType := declInfo.type
  Lean.Meta.forallTelescopeReducing declType fun fvars _ => do
    let mut set : Std.HashSet Name := {}
    for fvar in fvars do
      let fvarType <- Lean.Meta.inferType fvar
      if (← Lean.Meta.isProp fvarType) then
        match headConstAfterForalls fvarType with
        | some n => set := set.insert n
        | none => pure ()
    return set

private def readAssumptionNames (path : System.FilePath) : IO (Std.HashSet Name) := do
  let text <- IO.FS.readFile path
  let mut set : Std.HashSet Name := {}
  for line in text.splitOn "\n" do
    match extractDeclName line with
    | some nameStr => set := set.insert (qualifyName nameStr)
    | none => pure ()
  return set

private def isConjointName (n : Name) : Bool :=
  (`ConjointSD).isPrefixOf n

private def sortedNames (s : Std.HashSet Name) : List Name :=
  s.toList.mergeSort (fun a b => a.toString < b.toString)

private def usage : String :=
  "Usage: lake env lean --run scripts/audit_hidden_assumptions.lean [DeclName]"

def main (args : List String) : IO Unit := do
  let declNameStr? :=
    match args with
    | [] =>
        some
          "ConjointSD.paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization"
    | [s] => some s
    | _ => none
  match declNameStr? with
  | none =>
      IO.eprintln usage
      return ()
  | some declNameStr =>
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
        for n in sortedNames hidden do
          IO.println n.toString
      let (propHeadConsts, _, _) <-
        Lean.Meta.MetaM.toIO
          (ctxCore := ctx)
          (sCore := state)
          (x := propHypothesisHeadConsts declName)
      let conjointPropHeads := propHeadConsts.fold (init := ({} : Std.HashSet Name)) fun acc n =>
        if isConjointName n then acc.insert n else acc
      let unaccounted := conjointPropHeads.fold (init := ({} : Std.HashSet Name)) fun acc n =>
        if assumptionNames.contains n then acc else acc.insert n
      if conjointPropHeads.isEmpty then
        IO.println "No ConjointSD Prop hypotheses in theorem type."
      else
        IO.println "ConjointSD Prop hypotheses in theorem type:"
        for n in sortedNames conjointPropHeads do
          IO.println n.toString
      if unaccounted.isEmpty then
        IO.println "All ConjointSD Prop hypotheses are declared in Assumptions.lean."
      else
        IO.println "Unaccounted ConjointSD Prop hypotheses (not in Assumptions.lean):"
        for n in sortedNames unaccounted do
          IO.println n.toString
      let axioms <-
        (Prod.fst <$> (CoreM.toIO (ctx := ctx) (s := state) (Lean.collectAxioms declName)))
      let hasSorry := axioms.contains ``sorryAx
      if hasSorry then
        IO.eprintln "Found sorryAx in proof term."
      let mut otherAxioms : List Name := []
      for ax in axioms do
        if ax != ``sorryAx then
          otherAxioms := ax :: otherAxioms
      if otherAxioms.isEmpty then
        if hasSorry then
          IO.println "No axioms used besides sorryAx."
        else
          IO.println "No axioms used."
      else
        if hasSorry then
          IO.println "Other axioms used:"
        else
          IO.println "Axioms used:"
        for ax in otherAxioms.reverse do
          IO.println ax.toString
