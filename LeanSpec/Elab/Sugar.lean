module

public import Lean.Elab.Command
public import Lean.Elab.Term
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public import LeanSpec.Types
public import LeanSpec.Elab.Spec
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Spec

/-!
# Spec syntax sugar

Human-friendly surface syntax for `Requirement` definitions.
Desugars to the same proof-carrying structures; the `spec` command
still does registration and duplicate checking.

## Example

```
requirement overviewDashboard where
  id       "page.overview"
  shall    "Display a summary dashboard with national averages"
  strength must

  scenario "latest year on load"
    given "the user navigates to the overview page"
    when  "the page finishes loading"
    then_ "national averages for the latest year are shown"
    check deferred "dashboard UI not yet built"

  scenario "filter by county"
    when  "the user selects a county filter"
    then_ "only that county's data is displayed"
    check executable
```

Each string literal is wrapped into the proof-carrying `⟨"...", by native_decide⟩`
form, so a blank field is a compile error just as with the raw literals.

## Token reservation strategy

Field words fall into two groups:

* **Non-reserved** (`&"..."`): `id`, `shall`, `strength`. These words are also
  `Requirement`/`DesignUnit`/`Skillset` structure fields, so making them global
  keywords would break ordinary `{ id := ... }` literals in any file importing
  this module (observed in practice). They appear only in committed positions
  after the reserved `requirement` head, so they parse fine non-reserved.

* **Reserved**: `requirement`, `scenario`, `given`, `when`, `then_`, `check`.
  None of these are structure field names in this library, so reserving them is
  safe. They must be reserved because each leads an optional or repeated group,
  and a non-reserved token cannot make the parser commit to entering such a
  group.

The enumerated values (`must`/`should`, `executable`/`deferred`) are read as a
plain `ident` and interpreted in the macro.

Because `id`/`shall`/`strength` are non-reserved, the command cannot be matched
with a command quotation pattern; the handler destructures the parsed node by
`getArgs` index and is attached with `@[macro requirementCmd]`.
-/

open Lean Elab Command Term

namespace LeanSpec

/-- A single scenario block. `scenario`, `given`, `when`, `then_`, `check`
are reserved (safe: not structure fields). The check kind is a plain `ident`.

Layout (by `getArgs` index):
  0 "scenario "  1 name:str  2 (given)?  3 "when "  4 when:str
  5 "then_ "     6 then:str  7 "check "  8 kind:ident  9 (reason:str)? -/
declare_syntax_cat specScenario
syntax (name := specScenarioBlock) "scenario " str
    ("given " str)?
    "when " str
    "then_ " str
    "check " ident (str)? : specScenario

/-- The `requirement` command.

Layout (by `getArgs` index):
  0 "requirement "  1 name:ident  2 " where "  3 &"id "  4 id:str
  5 &"shall "       6 shall:str   7 (strength grp)?  8 scenarios+ -/
syntax (name := requirementCmd) "requirement " ident " where "
    &"id " str
    &"shall " str
    (&"strength " ident)?
    specScenario+ : command

/-- Wrap a string-literal syntax into `⟨"...", by native_decide⟩`. -/
private meta def proofStr (s : TSyntax `str) : MacroM (TSyntax `term) :=
  `(⟨$s, by native_decide⟩)

/-- Read a string literal out of a syntax node, or fail. -/
private meta def asStr (stx : Syntax) : MacroM (TSyntax `str) :=
  match stx.isStrLit? with
  | some _ => pure ⟨stx⟩
  | none => Macro.throwUnsupported

/-- Interpret the optional `(&"strength " ident)?` group. Absent ⇒ `shall`. -/
private meta def strengthTerm (grp : Syntax) : MacroM (TSyntax `term) :=
  let args := grp.getArgs
  if args.isEmpty then `(Strength.shall)
  else
    match (args.back!.getId).toString with
    | "must" => `(Strength.must)
    | "should" => `(Strength.should)
    | _ => `(Strength.shall)

/-- Build a `CheckStatus` term from the scenario `check` clause.
`kindIdent` is `executable` or `deferred`; `reasonGrp` is the optional reason. -/
private meta def checkTerm (kindIdent : Syntax) (reasonGrp : Syntax) :
    MacroM (TSyntax `term) := do
  match kindIdent.getId.toString with
  | "executable" => `(CheckStatus.executable)
  | "deferred" => do
    let reasonArgs := reasonGrp.getArgs
    if reasonArgs.isEmpty then
      Macro.throwUnsupported  -- deferred requires a reason string
    else
      let ps ← proofStr (← asStr reasonArgs.back!)
      `(CheckStatus.deferred $ps)
  | _ => Macro.throwUnsupported

/-- Build a `Scenario.mk` term from a `specScenario` node. -/
private meta def scenarioTerm (node : Syntax) : MacroM (TSyntax `term) := do
  let args := node.getArgs
  let namePs ← proofStr (← asStr args[1]!)
  let givenGrp := args[2]!
  let givenStx : TSyntax `term ←
    if givenGrp.getArgs.isEmpty then
      `(none)
    else
      -- given group args: [ "given ", str ]
      let ps ← proofStr (← asStr givenGrp.getArgs.back!)
      `(some $ps)
  let whenPs ← proofStr (← asStr args[4]!)
  let thenPs ← proofStr (← asStr args[6]!)
  let checkStx ← checkTerm args[8]! args[9]!
  `(Scenario.mk $namePs $givenStx $whenPs $thenPs $checkStx)

/- Macro for `requirementCmd`, attached by kind so we never need a quotation
pattern over the non-reserved `id`/`shall`/`strength` tokens. -/
@[macro requirementCmd]
public meta def expandRequirement : Macro := fun stx => do
  let args := stx.getArgs
  let name : TSyntax `ident := ⟨args[1]!⟩
  let idPs ← proofStr (← asStr args[4]!)
  let shallPs ← proofStr (← asStr args[6]!)
  let strengthStx ← strengthTerm args[7]!
  let scenarioNodes := args[8]!.getArgs
  let mut scenarioStxs : Array (TSyntax `term) := #[]
  for sc in scenarioNodes do
    scenarioStxs := scenarioStxs.push (← scenarioTerm sc)
  `(spec $name :=
      Requirement.mk $idPs $shallPs $strengthStx
        ⟨#[$scenarioStxs,*], by native_decide⟩)

end LeanSpec
