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

Each string literal is wrapped into the proof-carrying `⟨"...", by decide +kernel⟩`
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

The enumerated values (`must`/`shall`/`should`, `executable`/`deferred`) are read
as a plain `ident` and interpreted in the elaborator; any other word is an error.

Because `id`/`shall`/`strength` are non-reserved, the command cannot be matched
with a command quotation pattern; the handler reads the parsed node by index
(`stx[i]`, which yields `missing` rather than panicking) and is attached with
`@[command_elab requirementCmd]`.
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

/-- Wrap a string-literal syntax into `⟨"...", by decide +kernel⟩`. -/
private meta def proofStr (s : TSyntax `str) : CommandElabM (TSyntax `term) :=
  `(⟨$s, by decide +kernel⟩)

/-- Read a string literal out of a syntax node, or fail at that node. -/
private meta def asStr (what : String) (stx : Syntax) : CommandElabM (TSyntax `str) :=
  match stx.isStrLit? with
  | some _ => pure ⟨stx⟩
  | none => throwErrorAt stx "expected a string literal for {what}"

/-- Interpret the optional `(&"strength " ident)?` group. Absent ⇒ `shall`.
An unknown word is an error, as it is on the JSON wire. -/
private meta def strengthTerm (grp : Syntax) : CommandElabM (TSyntax `term) := do
  if grp.getNumArgs == 0 then return ← `(Strength.shall)
  let word := grp[1]
  match word.getId.toString with
  | "must" => `(Strength.must)
  | "shall" => `(Strength.shall)
  | "should" => `(Strength.should)
  | other => throwErrorAt word "unknown strength `{other}`; expected `must`, `shall` or `should`"

/-- Build a `CheckStatus` term from the scenario `check` clause.
`kindIdent` is `executable` or `deferred`; `reasonGrp` is the optional reason,
required for `deferred` and refused for `executable`. -/
private meta def checkTerm (kindIdent : Syntax) (reasonGrp : Syntax) :
    CommandElabM (TSyntax `term) := do
  let hasReason := reasonGrp.getNumArgs > 0
  match kindIdent.getId.toString with
  | "executable" =>
    if hasReason then
      throwErrorAt reasonGrp "`check executable` takes no reason; remove the string or use `check deferred`"
    `(CheckStatus.executable)
  | "deferred" =>
    if !hasReason then
      throwErrorAt kindIdent "`check deferred` needs a reason string, e.g. `check deferred \"no fixture yet\"`"
    let ps ← proofStr (← asStr "the deferred reason" reasonGrp[0])
    `(CheckStatus.deferred $ps)
  | other =>
    throwErrorAt kindIdent "unknown check kind `{other}`; expected `executable` or `deferred`"

/-- Build a `Scenario.mk` term from a `specScenario` node. -/
private meta def scenarioTerm (node : Syntax) : CommandElabM (TSyntax `term) := do
  let namePs ← proofStr (← asStr "the scenario name" node[1])
  let givenGrp := node[2]
  let givenStx : TSyntax `term ←
    if givenGrp.getNumArgs == 0 then
      `(none)
    else
      -- given group args: [ "given ", str ]
      let ps ← proofStr (← asStr "`given`" givenGrp[1])
      `(some $ps)
  let whenPs ← proofStr (← asStr "`when`" node[4])
  let thenPs ← proofStr (← asStr "`then_`" node[6])
  let checkStx ← checkTerm node[8] node[9]
  `(Scenario.mk $namePs $givenStx $whenPs $thenPs $checkStx)

/- Elaborator for `requirementCmd`, attached by kind so we never need a quotation
pattern over the non-reserved `id`/`shall`/`strength` tokens. Every failure is an
error at the offending token; nothing falls back to a default. -/
@[command_elab requirementCmd]
public meta def elabRequirement : CommandElab := fun stx => do
  -- The parser has already reported a syntax error on a partial node; elaborating
  -- it would only add noise.
  if stx.hasMissing then throwAbortCommand
  let name : TSyntax `ident := ⟨stx[1]⟩
  let idPs ← proofStr (← asStr "`id`" stx[4])
  let shallPs ← proofStr (← asStr "`shall`" stx[6])
  let strengthStx ← strengthTerm stx[7]
  let mut scenarioStxs : Array (TSyntax `term) := #[]
  for sc in stx[8].getArgs do
    scenarioStxs := scenarioStxs.push (← scenarioTerm sc)
  elabCommand (← `(command| spec $name :=
      Requirement.mk $idPs $shallPs $strengthStx
        ⟨#[$scenarioStxs,*], by decide +kernel⟩))

end LeanSpec
