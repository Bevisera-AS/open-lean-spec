import LeanSpecProcess

open LeanSpec
open LeanSpec.Workflow

/-! The `lean-spec` CLI reads the skill catalog. Requirements are Lean `Prop`s in
`LeanSpec.Logic`; `lake build` checks them, so there is nothing to query here. -/

def usage : String :=
  "usage: lean-spec (list-skillsets | boot-plan <token> | show-skillset <token>)"

def fail (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list-skillsets"] =>
      for ss in catalog.skillsets do
        IO.println s!"{ss.id.value} token={ss.pasteToken.value} role={ss.roleSkill.value}"
      return 0
  | ["boot-plan", token] =>
      match catalog.findSkillset? token with
      | some ss =>
          for id in ss.boot.toArray do
            IO.println id.value
          return 0
      | none => fail s!"skillset not found: {token}"
  | ["show-skillset", token] =>
      match catalog.findSkillset? token with
      | some ss =>
          IO.println s!"# {ss.id.value}"
          IO.println s!"paste-token: {ss.pasteToken.value}"
          IO.println s!"mission: {ss.mission.value}"
          IO.println s!"role-skill: {ss.roleSkill.value}"
          IO.println "boot:"
          for id in ss.boot.toArray do
            IO.println s!"  - {id.value}"
          return 0
      | none => fail s!"skillset not found: {token}"
  | _ => fail usage
