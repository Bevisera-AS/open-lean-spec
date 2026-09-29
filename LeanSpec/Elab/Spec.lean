module

public import Lean.Elab.Command
public import Lean.Elab.Term
public import Lean.Environment
public import Lean.Meta.Eval
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.Meta.Eval
public import LeanSpec.Types
public meta import LeanSpec.Types

open Lean Elab Command Term Meta

namespace LeanSpec

public section

/-- True when a `Requirement.id` is already in the list. Used by the `spec` command. -/
public def requirementIdTaken (requirements : Array Requirement) (id : String) : Bool :=
  requirements.any (fun r => r.id.value == id)

#guard !requirementIdTaken #[] "demo.requirement"
#guard
  requirementIdTaken #[{
    id := ⟨"demo.requirement", by native_decide⟩
    shall := ⟨"x", by native_decide⟩
    scenarios := ⟨#[{
      name := ⟨"n", by native_decide⟩
      whenText := ⟨"w", by native_decide⟩
      thenText := ⟨"t", by native_decide⟩
      check := .executable
    }], by native_decide⟩
  }] "demo.requirement"

end

public meta section

initialize specExt :
    SimplePersistentEnvExtension (Name × Requirement) (Array (Name × Requirement)) ←
  registerSimplePersistentEnvExtension {
    name          := `LeanSpec.specExt
    addImportedFn := fun arrs => arrs.foldl (init := #[]) (· ++ ·)
    addEntryFn    := fun arr e => arr.push e
    asyncMode     := .local
  }

def specEntries (env : Environment) : Array (Name × Requirement) :=
  specExt.getState env

end

/-- Snapshot of requirements registered by the `spec` command in this environment. -/
elab "registeredSpecs%" : term => unsafe do
  let env ← getEnv
  let entries := specEntries env
  let nameTy := Lean.mkConst ``Name
  let valTy := Lean.mkConst ``LeanSpec.Requirement
  let pairTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) nameTy valTy
  entries.foldlM
    (init := mkApp (Lean.mkConst ``Array.mkArray0 [0]) pairTy)
    fun (acc : Expr) (p : Name × Requirement) => do
      let nameExpr := toExpr p.1
      let valExpr := Lean.mkConst p.1
      let pairExpr :=
        mkApp2 (mkApp2 (Lean.mkConst ``Prod.mk [0, 0]) nameTy valTy) nameExpr valExpr
      return mkApp2 (mkApp (Lean.mkConst ``Array.push [0]) pairTy) acc pairExpr

/-- Expand `spec name := { ... }` to a `Requirement` def and register it.

Duplicate Lean names and duplicate `Requirement.id` values fail at elaboration.
Snapshot membership stays explicit; this command does not write the store. -/
elab "spec " name:ident " := " body:term : command => unsafe do
  elabCommand (← `(command| public def $name : Requirement := $body))
  let declName := (← getCurrNamespace) ++ name.getId
  let env ← getEnv
  if (specEntries env).any (fun (n, _) => n == declName) then
    throwError "duplicate spec `{declName}` (already registered)"
  let value ← liftTermElabM do
    evalExpr' (α := Requirement) ``LeanSpec.Requirement (mkConst declName)
  if (specEntries env).any (fun (_, r) => r.id == value.id) then
    throwError "duplicate requirement id `{value.id.value}` (already registered)"
  if !value.wellFormed then
    throwError "spec `{value.id.value}` is ill-formed"
  modifyEnv fun env => specExt.addEntry env (declName, value)

end LeanSpec
