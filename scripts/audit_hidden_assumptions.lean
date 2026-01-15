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

private def hiddenAssumptionsForDecl (declName : Name) (assumptionNames : Std.HashSet Name) :
    CoreM (Std.HashSet Name) := do
  let (typeConsts, valueConsts) <- constsInDecl declName
  let valueOnly := valueConsts.fold (init := ({} : Std.HashSet Name)) fun acc n =>
    if typeConsts.contains n then acc else acc.insert n
  let hidden := valueOnly.fold (init := ({} : Std.HashSet Name)) fun acc n =>
    if assumptionNames.contains n then acc.insert n else acc
  return hidden

private def isConjointName (n : Name) : Bool :=
  (`ConjointSD).isPrefixOf n

partial def collectConjointValueDeps (declName : Name) : CoreM (Std.HashSet Name) := do
  let rec go (pending : List Name) (visited : Std.HashSet Name) : CoreM (Std.HashSet Name) := do
    match pending with
    | [] => return visited
    | n :: rest =>
        if visited.contains n then
          go rest visited
        else
          let visited := visited.insert n
          let (_, valueConsts) <- constsInDecl n
          let next := valueConsts.toList.foldl (fun acc c =>
            if isConjointName c && !visited.contains c then c :: acc else acc) rest
          go next visited
  go [declName] {}

private def hiddenAssumptionsByDecl (decls : List Name) (assumptionNames : Std.HashSet Name) :
    CoreM (List (Name × Std.HashSet Name)) := do
  let mut acc : List (Name × Std.HashSet Name) := []
  for decl in decls do
    if assumptionNames.contains decl then
      continue
    let hidden <- hiddenAssumptionsForDecl decl assumptionNames
    if !hidden.isEmpty then
      acc := (decl, hidden) :: acc
  return acc.reverse

private def containsPair (pairs : List (Name × Name)) (p : Name × Name) : Bool :=
  pairs.any (fun q => q.1 == p.1 && q.2 == p.2)

private def addPair (pairs : List (Name × Name)) (p : Name × Name) : List (Name × Name) :=
  if containsPair pairs p then pairs else p :: pairs

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

private def structureFieldAssumptionPairs
    (structName : Name) (assumptionNames : Std.HashSet Name) :
    CoreM (List (Name × Name)) := do
  let env <- getEnv
  let some info := Lean.getStructureInfo? env structName
    | return []
  let mut pairs : List (Name × Name) := []
  for i in List.range info.fieldNames.size do
    let some proj := info.getProjFn? i
      | continue
    let some projInfo := env.find? proj
      | continue
    match headConstAfterForalls projInfo.type with
    | some head =>
        if assumptionNames.contains head then
          pairs := addPair pairs (head, structName)
    | none => pure ()
  return pairs

private partial def impliedAssumptionsFromFieldsGo
    (pending : List Name) (closure : Std.HashSet Name) (pairs : List (Name × Name))
    (assumptionNames : Std.HashSet Name) :
    CoreM (Std.HashSet Name × List (Name × Name)) := do
  match pending with
  | [] => return (closure, pairs)
  | n :: rest =>
      let newPairs <- structureFieldAssumptionPairs n assumptionNames
      let mut closure := closure
      let mut rest := rest
      let mut pairs := pairs
      for (assump, src) in newPairs do
        pairs := addPair pairs (assump, src)
        if !closure.contains assump then
          closure := closure.insert assump
          rest := assump :: rest
      impliedAssumptionsFromFieldsGo rest closure pairs assumptionNames

private def impliedAssumptionsFromFields
    (roots : Std.HashSet Name) (assumptionNames : Std.HashSet Name) :
    CoreM (Std.HashSet Name × List (Name × Name)) :=
  impliedAssumptionsFromFieldsGo roots.toList roots [] assumptionNames

private def subsetOf (a b : Std.HashSet Name) : Bool :=
  a.fold (init := true) fun ok n => ok && b.contains n

private def insertDerivation
    (pairs : List (Name × List Name)) (key val : Name) :
    List (Name × List Name) :=
  match pairs with
  | [] => [(key, [val])]
  | (k, vs) :: rest =>
      if k == key then
        let vs := if vs.contains val then vs else val :: vs
        (k, vs) :: rest
      else
        (k, vs) :: insertDerivation rest key val

private def lookupDerivations (pairs : List (Name × List Name)) (key : Name) : List Name :=
  match pairs with
  | [] => []
  | (k, vs) :: rest =>
      if k == key then vs else lookupDerivations rest key

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

private def sortedNames (s : Std.HashSet Name) : List Name :=
  s.toList.mergeSort (fun a b => a.toString < b.toString)

private def dedupNames (names : List Name) : List Name :=
  let set := names.foldl (init := ({} : Std.HashSet Name)) fun acc n => acc.insert n
  sortedNames set

private def joinNames (names : List Name) : String :=
  String.intercalate ", " (names.map Name.toString)

private def sourcesForAssumption (pairs : List (Name × Name)) (assumption : Name) : List Name :=
  pairs.foldl (init := []) fun acc p => if p.1 == assumption then p.2 :: acc else acc

private def noteForAssumption
    (fieldPairs : List (Name × Name)) (derivations : List (Name × List Name)) (assumption : Name) :
    String :=
  let sources := dedupNames (sourcesForAssumption fieldPairs assumption)
  let derivs := dedupNames (lookupDerivations derivations assumption)
  let parts :=
    (if !sources.isEmpty then [s!"implied by {joinNames sources}"] else []) ++
    (if !derivs.isEmpty then [s!"derivable via {joinNames derivs}"] else [])
  if parts.isEmpty then
    ""
  else
    " (" ++ String.intercalate "; " parts ++ ")"

private def derivationsByAssumption
    (decls : List Name) (assumptionNames : Std.HashSet Name) (allowed : Std.HashSet Name)
    (env : Environment) (ctx : Core.Context) (state : Core.State) :
    IO (List (Name × List Name)) := do
  let mut acc : List (Name × List Name) := []
  for decl in decls do
    if env.isConstructor decl || env.isProjectionFn decl then
      continue
    let some info := env.find? decl
      | continue
    let some head := headConstAfterForalls info.type
      | continue
    if !assumptionNames.contains head then
      continue
    let (propHeads, _, _) <-
      Lean.Meta.MetaM.toIO
        (ctxCore := ctx)
        (sCore := state)
        (x := propHypothesisHeadConsts decl)
    let conjPropHeads := propHeads.fold (init := ({} : Std.HashSet Name)) fun acc n =>
      if isConjointName n then acc.insert n else acc
    if subsetOf conjPropHeads allowed then
      acc := insertDerivation acc head decl
  return acc

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
      let (propHeadConsts, _, _) <-
        Lean.Meta.MetaM.toIO
          (ctxCore := ctx)
          (sCore := state)
          (x := propHypothesisHeadConsts declName)
      let conjointPropHeads := propHeadConsts.fold (init := ({} : Std.HashSet Name)) fun acc n =>
        if isConjointName n then acc.insert n else acc
      let assumptionNames <- readAssumptionNames "ConjointSD/Assumptions.lean"
      let (impliedAssumptions, fieldPairs) <-
        (Prod.fst <$>
          (CoreM.toIO (ctx := ctx) (s := state)
            (impliedAssumptionsFromFields conjointPropHeads assumptionNames)))
      let hidden <-
        (Prod.fst <$>
          (CoreM.toIO (ctx := ctx) (s := state)
            (hiddenAssumptionsForDecl declName assumptionNames)))
      if hidden.isEmpty then
        IO.println "No hidden assumptions from ConjointSD/Assumptions.lean."
      else
        IO.println "Hidden assumptions (appear in proof term only):"
        for n in sortedNames hidden do
          IO.println n.toString
      let transitiveDeps <-
        (Prod.fst <$>
          (CoreM.toIO (ctx := ctx) (s := state)
            (collectConjointValueDeps declName)))
      let transitiveDeps := transitiveDeps.erase declName
      let hiddenDeps <-
        (Prod.fst <$>
          (CoreM.toIO (ctx := ctx) (s := state)
            (hiddenAssumptionsByDecl (sortedNames transitiveDeps) assumptionNames)))
      let derivations <-
        derivationsByAssumption
          (sortedNames transitiveDeps)
          assumptionNames
          impliedAssumptions
          env ctx state
      if hiddenDeps.isEmpty then
        IO.println "No transitive hidden assumptions from ConjointSD/Assumptions.lean."
      else
        IO.println "Transitive hidden assumptions by declaration:"
        for (decl, deps) in hiddenDeps do
          IO.println decl.toString
          for n in sortedNames deps do
            let note := noteForAssumption fieldPairs derivations n
            IO.println s!"  {n.toString}{note}"
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
