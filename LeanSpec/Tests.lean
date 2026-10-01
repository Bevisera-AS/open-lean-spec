import LeanSpec
import LeanSpec.Demo.Theme
import LeanSpec.Demo.Archive
import LeanSpec.Demo.HumanAccept
import LeanSpec.Demo.StorePath
import LeanSpec.Workflow.Catalog
import LeanSpec.Demo.SkillSyntax
import LeanSpec.Demo.SpecSyntax
import LeanSpec.Tests.ImportFirewall
import LeanSpec.Tests.Validated
import LeanSpec.Tests.Scenario
import LeanSpec.Tests.Requirement
import LeanSpec.Tests.Change
import LeanSpec.Tests.Applicable
import LeanSpec.Tests.Emit
import LeanSpec.Tests.ProcessSkill
import LeanSpec.Tests.Snapshot
import LeanSpec.Tests.Skillset
import LeanSpec.Tests.Catalog
import LeanSpec.Tests.Design
import LeanSpec.Tests.Verification

open LeanSpec
open LeanSpec.Demo.Theme
open LeanSpec.Demo.Archive
open LeanSpec.Demo.HumanAccept
open LeanSpec.Demo.StorePath
open LeanSpec.Workflow
open LeanSpec.Demo.SkillSyntax
open LeanSpec.Demo.SpecSyntax

def assertTrue (label : String) (condition : Bool) : IO Unit := do
  if !condition then
    throw <| IO.userError s!"test failed: {label}"

def main : IO UInt32 := do
  ImportFirewall.check
  for (label, condition) in LeanSpec.Tests.Validated.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Scenario.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Requirement.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Change.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Applicable.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Emit.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.ProcessSkill.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Snapshot.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Skillset.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Catalog.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Design.checks do
    assertTrue label condition
  for (label, condition) in LeanSpec.Tests.Verification.checks do
    assertTrue label condition
  assertTrue "theme requirement well-formed" themeSelection.wellFormed
  assertTrue "theme design well-formed" themeSelectionDesign.wellFormed
  assertTrue "theme design shares the requirement id"
    (themeSelectionDesign.id == themeSelection.id)
  assertTrue "theme scenario is executable" (!themeSelection.hasDeferredChecks)
  let before : AppState := { theme := .light, persisted := false }
  let after := toggleDark before
  assertTrue "toggle dark check" (toggleDarkCheck before after)
  let emptyRaw : Raw.Requirement := {
    id := "empty"
    shall := "x"
    scenarios := #[]
  }
  assertTrue "empty scenarios fail well-formed" (!(emptyRaw.validate "requirement").isOk)
  assertTrue "proposeChange skill well-formed" proposeChange.wellFormed
  let addTheme : Change := {
    id := ⟨"add-dark-mode", by native_decide⟩
    why := ⟨"Users need a persisted dark theme.", by native_decide⟩
    deltas := ⟨#[.added themeSelection], by native_decide⟩
  }
  assertTrue "added change well-formed" addTheme.wellFormed
  let partialRaw : Raw.Requirement := {
    id := "theme.selection"
    shall := "changed"
    scenarios := #[]
  }
  assertTrue "partial modified is ill-formed" (!(partialRaw.validate "requirement").isOk)
  let okMod : Delta := .modified themeSelection
  assertTrue "validated modified is not partial" (!okMod.isPartialModified)
  let removedOk : Delta := .removed
    ⟨"theme.legacy", by native_decide⟩
    ⟨"replaced", by native_decide⟩
    ⟨"use theme.selection", by native_decide⟩
  assertTrue "removed with reason and migration" removedOk.wellFormed
  assertTrue "spec-change catalog well-formed" catalog.wellFormed
  assertTrue "spec-change token resolves" (catalog.findSkillset? "spec-change").isSome
  assertTrue "company-pack skillsets are not in this library"
    (catalog.findSkillset? "company-pack.role").isNone
  let missingRoleSet : Skillset := {
    id := ⟨"skillset.broken", by native_decide⟩
    pasteToken := ⟨"broken", by native_decide⟩
    mission := ⟨"broken", by native_decide⟩
    roleSkill := roleSpecifier.id
    boot := ⟨#[proposeChange.id, roleSpecifier.id], by native_decide⟩
    roleInBoot := by native_decide
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
  assertTrue "dark-mode change well-formed" darkModeChange.wellFormed
  assertTrue "archive without human accept fails"
    (match initialSnapshot.archive darkModeChange .declined with
     | .error .noHumanAccept => true
     | _ => false)
  let archived := initialSnapshot.archive darkModeChange .accepted
  assertTrue "ADDED+MODIFIED archive succeeds"
    (match archived with
     | .ok snap =>
         snap.has "theme.selection" &&
           snap.has "theme.contrast" &&
           (match snap.find? "theme.selection" with
            | some r => r.scenarios.size == 2
            | none => false)
     | .error _ => false)
  let addDup : Change := {
    id := ⟨"dup", by native_decide⟩
    why := ⟨"already present", by native_decide⟩
    deltas := ⟨#[.added themeSelection], by native_decide⟩
  }
  assertTrue "archive rejects duplicate add"
    (match initialSnapshot.archive addDup .accepted with
     | .error (.duplicateId "theme.selection") => true
     | _ => false)
  let missMod : Change := {
    id := ⟨"miss", by native_decide⟩
    why := ⟨"no such requirement", by native_decide⟩
    deltas := ⟨#[.modified {
      id := ⟨"theme.missing", by native_decide⟩
      shall := ⟨"gone", by native_decide⟩
      scenarios := themeSelection.scenarios
    }], by native_decide⟩
  }
  assertTrue "archive rejects missing modified id"
    (match initialSnapshot.archive missMod .accepted with
     | .error (.missingId "theme.missing") => true
     | _ => false)
  let renamed : Change := {
    id := ⟨"rename-theme", by native_decide⟩
    why := ⟨"stable id", by native_decide⟩
    deltas := ⟨#[.renamed {
      frm := ⟨"theme.selection", by native_decide⟩
      to := ⟨"theme.mode", by native_decide⟩
      property := by native_decide
    }], by native_decide⟩
  }
  assertTrue "rename archive succeeds"
    (match initialSnapshot.archive renamed .accepted with
     | .ok snap =>
         snap.has "theme.mode" && !snap.has "theme.selection" &&
           (snap.findDesign? "theme.mode").isSome &&
           (snap.findDesign? "theme.selection").isNone
     | .error _ => false)
  let removed : Change := {
    id := ⟨"drop-theme", by native_decide⟩
    why := ⟨"retired", by native_decide⟩
    deltas := ⟨#[.removed
      ⟨"theme.selection", by native_decide⟩
      ⟨"retired", by native_decide⟩
      ⟨"no replacement", by native_decide⟩], by native_decide⟩
  }
  assertTrue "remove archive succeeds"
    (match initialSnapshot.archive removed .accepted with
     | .ok snap =>
         !snap.has "theme.selection" && snap.requirements.isEmpty && snap.designs.isEmpty
     | .error _ => false)
  assertTrue "theme requirement roundtrips through JSON"
    (match acceptRequirement (encodeRequirement themeSelection) with
     | .ok r => r == themeSelection
     | .error _ => false)
  assertTrue "requirement extra key fails closed"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}],\"oops\":1}" with
     | .error (.unknownFields "requirement" ["oops"]) => true
     | _ => false)
  assertTrue "missing strength has no silent default"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}]}" with
     | .error (.missingField "requirement" "strength") => true
     | _ => false)
  assertTrue "empty scenarios fail accept"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[]}" with
     | .error (.illFormed "requirement.scenarios" _) => true
     | _ => false)
  assertTrue "invalid requirement id retains validation path"
    (match acceptRequirementString
        "{\"id\":\"inventory..x\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}]}" with
     | .error (.illFormed "requirement.id" _) => true
     | _ => false)
  assertTrue "blank shall retains validation path"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\" \",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}]}" with
     | .error (.illFormed "requirement.shall" _) => true
     | _ => false)
  assertTrue "blank JSON scenario name retains validation path"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\" \",\"given\":\"g\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"deferred\",\"reason\":\"later\"}}]}" with
     | .error (.illFormed "requirement.scenarios[0].name" _) => true
     | _ => false)
  assertTrue "blank JSON present given retains validation path"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"given\":\" \",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"deferred\",\"reason\":\"later\"}}]}" with
     | .error (.illFormed "requirement.scenarios[0].given" _) => true
     | _ => false)
  assertTrue "blank JSON when retains validation path"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"given\":\"g\",\"when\":\" \",\"then\":\"t\",\"check\":{\"tag\":\"deferred\",\"reason\":\"later\"}}]}" with
     | .error (.illFormed "requirement.scenarios[0].when" _) => true
     | _ => false)
  assertTrue "blank JSON then retains validation path"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"given\":\"g\",\"when\":\"w\",\"then\":\" \",\"check\":{\"tag\":\"deferred\",\"reason\":\"later\"}}]}" with
     | .error (.illFormed "requirement.scenarios[0].then" _) => true
     | _ => false)
  assertTrue "blank JSON deferred reason retains validation path"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"given\":\"g\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"deferred\",\"reason\":\" \"}}]}" with
     | .error (.illFormed "requirement.scenarios[0].check.reason" _) => true
     | _ => false)
  assertTrue "unknown strength fails"
    (match acceptRequirementString
        "{\"id\":\"x\",\"shall\":\"y\",\"strength\":\"maybe\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}]}" with
     | .error (.invalidTag "requirement" "strength" "maybe") => true
     | _ => false)
  assertTrue "change roundtrips through JSON"
    (match acceptChange (encodeChange darkModeChange) with
     | .ok c => c == darkModeChange
     | .error _ => false)
  assertTrue "snapshot roundtrips through JSON"
    (match acceptSnapshot (encodeSnapshot initialSnapshot) with
     | .ok s => s == initialSnapshot
     | .error _ => false)
  assertTrue "duplicate snapshot ids keep their path"
    (match acceptSnapshotString
        "{\"requirements\":[{\"id\":\"r\",\"shall\":\"s\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}]},{\"id\":\"r\",\"shall\":\"s2\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}]}]}" with
     | .error (.illFormed "snapshot.requirements" _) => true
     | _ => false)
  assertTrue "snapshot scenario validation retains its full nested path"
    (match acceptSnapshotString
        "{\"requirements\":[{\"id\":\"r\",\"shall\":\"s\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\" \",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}]}]}" with
     | .error (.illFormed "snapshot.requirements[0].scenarios[0].name" _) => true
     | _ => false)
  assertTrue "change scenario validation retains its full nested path"
    (match acceptChangeString
        "{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"added\",\"requirement\":{\"id\":\"r\",\"shall\":\"s\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"deferred\",\"reason\":\" \"}}]}}]}" with
     | .error (.illFormed
         "change.deltas[0].requirement.scenarios[0].check.reason" _) => true
     | _ => false)
  assertTrue "change extra key fails closed"
    (match acceptChangeString
        "{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"renamed\",\"from\":\"a\",\"to\":\"b\"}],\"extra\":1}" with
     | .error (.unknownFields "change" ["extra"]) => true
     | _ => false)
  assertTrue "unknown delta tag fails"
    (match acceptChangeString
        "{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"patch\"}]}" with
     | .error (.invalidTag "change.deltas[0]" "tag" "patch") => true
     | _ => false)
  assertTrue "empty deltas fail accept"
    (match acceptChangeString "{\"id\":\"c\",\"why\":\"w\",\"deltas\":[]}" with
     | .error (.illFormed "change.deltas" _) => true
     | _ => false)
  assertTrue "modified id mismatch retains its path"
    (match acceptChangeString
        "{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"modified\",\"id\":\"theme.selection\",\"requirement\":{\"id\":\"theme.other\",\"shall\":\"y\",\"strength\":\"shall\",\"scenarios\":[{\"name\":\"n\",\"when\":\"w\",\"then\":\"t\",\"check\":{\"tag\":\"executable\"}}]}}]}" with
     | .error (.illFormed "change.deltas[0].id" _) => true
     | _ => false)
  assertTrue "same rename retains its path"
    (match acceptChangeString
        "{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"renamed\",\"from\":\"theme.a\",\"to\":\"theme.a\"}]}" with
     | .error (.illFormed "change.deltas[0]" _) => true
     | _ => false)
  IO.FS.withTempDir fun dir => do
    let path := dir / "Snapshot.lean"
    writeSnapshot path initialSnapshot
    match ← readSnapshot path with
    | .error _ => assertTrue "store roundtrip" false
    | .ok s =>
        assertTrue "store roundtrip" (s == initialSnapshot)
        assertTrue "store is not a git path" (!(path.toString.contains ".git"))
        assertTrue "canonical store is Lean source"
          ((← IO.FS.readFile path).startsWith "-- Generated by lean-spec")
  assertTrue "default store is local Lean working state"
    (defaultSnapshotPath.toString == ".lean-spec/Snapshot.lean")
  IO.FS.withTempDir fun dir => do
    let path := dir / "snapshot.json"
    writeSnapshot path initialSnapshot
    match ← readSnapshot path with
    | .ok s => assertTrue "legacy JSON snapshot still reads" (s == initialSnapshot)
    | .error _ => assertTrue "legacy JSON snapshot still reads" false
  assertTrue "dark-mode change is valid against theme snapshot"
    (match initialSnapshot.checkChange darkModeChange with
     | .ok () => true
     | .error _ => false)
  assertTrue "validate refuses adding a duplicate id"
    (match initialSnapshot.checkChange addDup with
     | .error (.apply (.duplicateId "theme.selection")) => true
     | _ => false)
  IO.FS.withTempDir fun dir => do
    let snapPath := dir / "Snapshot.lean"
    let changePath := dir / "change.json"
    writeSnapshot snapPath initialSnapshot
    writeChange changePath darkModeChange
    match ← readChange changePath with
    | .error _ => assertTrue "change store roundtrip" false
    | .ok c =>
        assertTrue "change store roundtrip" (c == darkModeChange)
        assertTrue "format snapshot lists theme"
          ((formatSnapshot initialSnapshot).contains "theme.selection")
        assertTrue "format snapshot lists design interfaces"
          ((formatSnapshot initialSnapshot).contains "interfaces: Theme, AppState")
        assertTrue "validate file against snapshot"
          (match initialSnapshot.checkChange c with
           | .ok () => true
           | .error _ => false)
  IO.FS.withTempDir fun dir => do
    let snapPath := dir / "Snapshot.lean"
    writeSnapshot snapPath initialSnapshot
    match ← archiveChangeFile snapPath darkModeChange .declined with
    | .error d =>
        assertTrue "declined archive is noHumanAccept" (d == "noHumanAccept")
    | .ok _ =>
        assertTrue "declined archive must not succeed" false
    match ← readSnapshot snapPath with
    | .ok s =>
        assertTrue "declined path leaves snapshot unchanged" (s == initialSnapshot)
    | .error _ =>
        assertTrue "declined path left snapshot readable" false
    match ← archiveChangeFile snapPath darkModeChange .accepted with
    | .error _ =>
        assertTrue "accepted archive writes" false
    | .ok s =>
        assertTrue "accepted archive adds contrast" (s.has "theme.contrast")
    match ← readSnapshot snapPath with
    | .ok s =>
        assertTrue "accepted path persists contrast" (s.has "theme.contrast")
    | .error _ =>
        assertTrue "accepted path left snapshot readable" false
  assertTrue "human-accept change well-formed" humanAcceptChange.wellFormed
  assertTrue "human-accept requirement is not theme"
    (archiveRequiresHuman.id.value != "theme.selection")
  assertTrue "empty snapshot accepts the human-accept add"
    (match emptySnapshot.checkChange humanAcceptChange with
     | .ok () => true
     | .error _ => false)
  assertTrue "store-path change well-formed" storePathChange.wellFormed
  assertTrue "store-path requirement is not theme"
    (workingSnapshotPath.id.value != "theme.selection")
  assertTrue "empty snapshot accepts the store-path add"
    (match emptySnapshot.checkChange storePathChange with
     | .ok () => true
     | .error _ => false)
  assertTrue "skill command elaborates a ProcessSkill" ping.wellFormed
  assertTrue "skill command registers the ProcessSkill id"
    ((registeredSkills%.map (fun p => p.2.id.value)).contains "demo.ping")
  assertTrue "spec command elaborates a Requirement" demoRequirement.wellFormed
  assertTrue "spec command registers the Requirement id"
    ((registeredSpecs%.map (fun p => p.2.id.value)).contains "demo.requirement")
  assertTrue "snapshot omits demo.requirement"
    (!initialSnapshot.has "demo.requirement")
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
