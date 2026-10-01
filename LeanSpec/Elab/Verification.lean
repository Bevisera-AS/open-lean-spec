module

public import Lean.Elab.Command
public import Lean.Elab.Term
public import Lean.Meta.Eval
public import Lean.PrettyPrinter
public import Lean.Util.CollectAxioms
public import Lean.OriginalConstKind
public import LeanSpec.Verification
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.Meta.Eval
public meta import Lean.PrettyPrinter
public meta import Lean.Util.CollectAxioms
public meta import Lean.OriginalConstKind
public meta import LeanSpec.Verification

open Lean Elab Command Term Meta

namespace LeanSpec

public meta section

/-!
`verification_statement <name> for <snapshot>` elaborates a `VerificationStatement`.

Theorems named by each `DesignUnit` are resolved in this environment. Their axioms
are `collectAxioms`, the same walk as `#print axioms`. The resulting definition
is the build artefact; the `lean-spec-verified` mark covers its proved rows only.
-/

private def nameOfCited (cited : String) : Name :=
  (cited.splitOn ".").foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.mkStr acc part

private def hasHiddenComponent : Name → Bool
  | .anonymous => false
  | .num parent _ => hasHiddenComponent parent
  | .str parent part => part.startsWith "_" || hasHiddenComponent parent

/-- Declarations whose last component is `cited`, skipping `_private` / `_native` names. -/
private def suffixHits (env : Environment) (cited : String) : Array Name :=
  if cited.isEmpty || cited.any (· == '.') then #[]
  else
    let env := env.setExporting false
    env.constants.fold (init := #[]) fun acc name _ =>
      if hasHiddenComponent name then acc
      else
        match name with
        | .str _ part => if part == cited then acc.push name else acc
        | _ => acc

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun a b => compare a.toString b.toString == Ordering.lt

private def constKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def constIsTheorem : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

private def oneLine (s : String) : String :=
  String.ofList <| s.toList.map fun c =>
    if c == '\n' || c == '\r' || c == '\t' then ' ' else c

/-- Imported `public theorem`s are axioms in this module. `wasOriginallyTheorem` recovers the
declaration kind from the defining module, where the kernel checked the proof. -/
private def describe (info : ConstantInfo) (name : Name) : CommandElabM TheoremFact := do
  let env ← getEnv
  let originallyTheorem := wasOriginallyTheorem env name
  let kind :=
    if originallyTheorem then "theorem"
    else if wasOriginallyDefn env name then "definition"
    else constKind info
  let axioms ← collectAxioms name
  let statement ← liftTermElabM do
    withOptions (fun o => pp.fullNames.set (pp.unicode.set o false) true) do
      let fmt ← PrettyPrinter.ppExpr info.toConstantVal.type
      pure <| oneLine (fmt.pretty 100000)
  return .resolved name.toString kind (originallyTheorem || constIsTheorem info) statement
    (axioms.map (·.toString))

private def resolveTheorem (cited : String) : CommandElabM TheoremFact := do
  let env := (← getEnv).setExporting false
  let exact := nameOfCited cited
  match env.find? exact with
  | some info => describe info exact
  | none =>
    if cited.isEmpty || cited.any (· == '.') then
      return .missing
    else
      match (sortNames (suffixHits env cited)).toList with
      | [] => return .missing
      | [name] =>
        match env.find? name with
        | some info => describe info name
        | none => return .missing
      | names => return .ambiguous (names.toArray.map (·.toString))

private def collectFacts (snap : SpecSnapshot) : CommandElabM (Array NamedTheoremFact) := do
  let mut facts : Array NamedTheoremFact := #[]
  for design in snap.designs do
    for thm in design.theorems do
      let fact ← resolveTheorem thm.value
      facts := facts.push {
        requirementId := design.id.value
        citedAs := thm.value
        fact
      }
  return facts

private def termStr (s : String) : Term :=
  ⟨Syntax.mkStrLit s⟩

private def termStrArray (xs : Array String) : CommandElabM Term := do
  let elems : Array Term := xs.map termStr
  `(#[$elems,*])

private def termFact (fact : TheoremFact) : CommandElabM Term := do
  match fact with
  | .missing => `(LeanSpec.TheoremFact.missing)
  | .ambiguous candidates =>
    let arr ← termStrArray candidates
    `(LeanSpec.TheoremFact.ambiguous $arr)
  | .resolved name kind isTheorem statement axioms =>
    let nameTerm := termStr name
    let kindTerm := termStr kind
    let statementTerm := termStr statement
    let arr ← termStrArray axioms
    let flag ← if isTheorem then `(true) else `(false)
    `(LeanSpec.TheoremFact.resolved $nameTerm $kindTerm $flag $statementTerm $arr)

private def termNamed (fact : NamedTheoremFact) : CommandElabM Term := do
  let body ← termFact fact.fact
  let requirementId := termStr fact.requirementId
  let citedAs := termStr fact.citedAs
  `({ requirementId := $requirementId, citedAs := $citedAs, fact := $body })

private def termFacts (facts : Array NamedTheoremFact) : CommandElabM Term := do
  let elems ← facts.mapM termNamed
  `(#[$elems,*])

/-- Elaborate `name` as the verification statement for `snap`.
Axioms come from `#print axioms` (`collectAxioms`) in this environment. -/
elab "verification_statement " name:ident " for " snap:term : command => unsafe do
  let snapshot ← liftTermElabM do
    let expr ← elabTerm snap (some (mkConst ``LeanSpec.SpecSnapshot))
    synthesizeSyntheticMVarsNoPostponing
    let expr ← instantiateMVars expr
    evalExpr' (α := SpecSnapshot) ``LeanSpec.SpecSnapshot expr
  let facts ← collectFacts snapshot
  let statement := assembleStatement snapshot facts
  let baked ← termFacts facts
  elabCommand <| ← `(command|
    public def $name : LeanSpec.VerificationStatement :=
      LeanSpec.assembleStatement $snap $baked)
  if !statement.disjoint || !statement.checkable then
    throwError "verification statement `{name.getId}` is not a checkable mark"

end

end LeanSpec
