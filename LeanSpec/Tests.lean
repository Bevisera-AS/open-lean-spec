import LeanSpecProcess
import LeanSpecKb
import LeanSpec.Workflow.Catalog
import LeanSpec.Demo.SkillSyntax
import LeanSpec.Logic.Tests
import LeanSpec.Tests.ImportFirewall
import LeanSpec.Tests.Validated
import LeanSpec.Tests.ProcessSkill
import LeanSpec.Tests.Skillset
import LeanSpec.Tests.Catalog
import LeanSpec.Tests.KernelPredicates

/-! `LeanSpec.Logic.Tests` is all `#guard`s: importing it here makes `lake test`
fail when any of them does. -/

open LeanSpec
open LeanSpec.Workflow
open LeanSpec.Demo.SkillSyntax

def assertTrue (label : String) (condition : Bool) : IO Unit := do
  if !condition then
    throw <| IO.userError s!"test failed: {label}"

def main : IO UInt32 := do
  ImportFirewall.check
  for (label, condition) in LeanSpec.Tests.Validated.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.ProcessSkill.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Skillset.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Catalog.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.KernelPredicates.checks do
    assertTrue label condition
  assertTrue "proposeChange skill well-formed" proposeChange.wellFormed
  assertTrue "spec-change catalog well-formed" catalog.wellFormed
  assertTrue "spec-change token resolves" (catalog.findSkillset? "spec-change").isSome
  assertTrue "company-pack skillsets are not in this library"
    (catalog.findSkillset? "company-pack.role").isNone
  let missingRoleSet : Skillset := {
    id := ⟨"skillset.broken", by decide +kernel⟩
    pasteToken := ⟨"broken", by decide +kernel⟩
    mission := ⟨"broken", by decide +kernel⟩
    roleSkill := roleSpecifier.id
    boot := ⟨#[proposeChange.id, roleSpecifier.id], by decide +kernel⟩
    roleInBoot := by decide +kernel
  }
  assertTrue "missing roleSkill fails"
    (match Catalog.of "catalog" #[proposeChange] #[missingRoleSet] with
     | .error error => error.path == "catalog.skillsets" && error.issue == .unregisteredSkill
     | .ok _ => false)
  let roleNotInBootRaw : Raw.Skillset := {
    id := specChange.id.value
    pasteToken := specChange.pasteToken.value
    mission := specChange.mission.value
    roleSkill := specChange.roleSkill.value
    boot := (specChange.boot.toArray.filter (fun id => id != specChange.roleSkill)).map (·.value)
  }
  assertTrue "roleSkill must be in boot"
    (!(roleNotInBootRaw.validate "skillset").isOk)
  assertTrue "skill command elaborates a ProcessSkill" ping.wellFormed
  assertTrue "skill command registers the ProcessSkill id"
    ((registeredSkills%.map (fun p => p.2.id.value)).contains "demo.ping")
  assertTrue "catalog omits demo.ping" (!catalog.hasSkill "demo.ping")
  assertTrue "catalog skills are in the registry"
    (catalog.skills.all fun s =>
      (registeredSkills%.map (fun p => p.2.id.value)).contains s.id.value)
  assertTrue "catalog omits company roles"
    (catalog.skills.all fun s => !s.id.value.contains "chief")
  let escaped : Raw.ProcessSkill := {
    id := "/tmp/escaped"
    oneLiner := "escape"
    purpose := "should not export"
    rules := #["no"]
  }
  assertTrue "absolute skill id is ill-formed" (!(escaped.validate "skill").isOk)
  assertTrue "sameIdSet is not one-directional"
    (!sameIdSet #["a", "a"] #["a", "b"])
  IO.println "lean-spec tests passed"
  return 0
