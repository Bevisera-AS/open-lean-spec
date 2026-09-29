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

/-- True when a `ProcessSkill.id` is already in the list. Used by the `skill` command. -/
public def skillIdTaken (skills : Array ProcessSkill) (id : String) : Bool :=
  skills.any (fun s => s.id.value == id)

#guard !skillIdTaken #[] "demo.ping"
#guard
  skillIdTaken #[{
    id := ⟨"demo.ping", by native_decide⟩
    oneLiner := ⟨"x", by native_decide⟩
    purpose := ⟨"y", by native_decide⟩
    rules := ⟨#[⟨"z", by native_decide⟩], by native_decide⟩
  }] "demo.ping"

end

public meta section

initialize skillExt :
    SimplePersistentEnvExtension (Name × ProcessSkill) (Array (Name × ProcessSkill)) ←
  registerSimplePersistentEnvExtension {
    name          := `LeanSpec.skillExt
    addImportedFn := fun arrs => arrs.foldl (init := #[]) (· ++ ·)
    addEntryFn    := fun arr e => arr.push e
    asyncMode     := .local
  }

def skillEntries (env : Environment) : Array (Name × ProcessSkill) :=
  skillExt.getState env

end

/-- Snapshot of skills registered by the `skill` command in this environment. -/
elab "registeredSkills%" : term => unsafe do
  let env ← getEnv
  let entries := skillEntries env
  let nameTy := Lean.mkConst ``Name
  let valTy := Lean.mkConst ``LeanSpec.ProcessSkill
  let pairTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) nameTy valTy
  entries.foldlM
    (init := mkApp (Lean.mkConst ``Array.mkArray0 [0]) pairTy)
    fun (acc : Expr) (p : Name × ProcessSkill) => do
      let nameExpr := toExpr p.1
      let valExpr := Lean.mkConst p.1
      let pairExpr :=
        mkApp2 (mkApp2 (Lean.mkConst ``Prod.mk [0, 0]) nameTy valTy) nameExpr valExpr
      return mkApp2 (mkApp (Lean.mkConst ``Array.push [0]) pairTy) acc pairExpr

/-- Expand `skill name := { ... }` to a `ProcessSkill` def and register it.

Duplicate Lean names and duplicate `ProcessSkill.id` values fail at elaboration.
Catalog membership stays explicit; this is not company-pack content. -/
elab "skill " name:ident " := " body:term : command => unsafe do
  elabCommand (← `(command| public def $name : ProcessSkill := $body))
  let declName := (← getCurrNamespace) ++ name.getId
  let env ← getEnv
  if (skillEntries env).any (fun (n, _) => n == declName) then
    throwError "duplicate skill `{declName}` (already registered)"
  let value ← liftTermElabM do
    evalExpr' (α := ProcessSkill) ``LeanSpec.ProcessSkill (mkConst declName)
  if (skillEntries env).any (fun (_, s) => s.id == value.id) then
    throwError "duplicate skill id `{value.id.value}` (already registered)"
  if !value.wellFormed then
    throwError "skill `{value.id.value}` is ill-formed"
  modifyEnv fun env => skillExt.addEntry env (declName, value)

end LeanSpec
