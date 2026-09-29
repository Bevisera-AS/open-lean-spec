module

public import LeanSpec.Snapshot
public import LeanSpec.Demo.Theme
public meta import LeanSpec.Snapshot
public meta import LeanSpec.Demo.Theme

namespace LeanSpec.Demo.Archive

open LeanSpec
open LeanSpec.Demo.Theme

public section

public def themeContrast : Requirement := {
  id := ⟨"theme.contrast", by native_decide⟩
  shall := ⟨"Dark theme documents a minimum contrast target.", by native_decide⟩
  strength := .should
  scenarios := ⟨#[{
    name := ⟨"contrast stated", by native_decide⟩
    whenText := ⟨"dark theme is active", by native_decide⟩
    thenText := ⟨"contrast is recorded as a requirement", by native_decide⟩
    check := .deferred ⟨"no pixel checker yet", by native_decide⟩
  }], by native_decide⟩
}

public def themeSelectionV2 : Requirement := {
  id := themeSelection.id
  shall := ⟨themeSelection.shall.value ++ " The choice persists across restart.", by native_decide⟩
  strength := themeSelection.strength
  scenarios := themeSelection.scenarios.push {
    name := ⟨"persist across restart", by native_decide⟩
    given? := some ⟨"the user already chose dark", by native_decide⟩
    whenText := ⟨"the user restarts the app", by native_decide⟩
    thenText := ⟨"the app opens in dark mode", by native_decide⟩
    check := .deferred ⟨"no persistence fixture yet", by native_decide⟩
  }
}

public def initialSnapshot : SpecSnapshot := {
  requirements := #[themeSelection]
  uniqueIds := by native_decide
  designs := #[themeSelectionDesign]
  uniqueDesignIds := by native_decide
  designsLinked := by native_decide
}

public def darkModeChange : Change := {
  id := ⟨"dark-mode-v2", by native_decide⟩
  why := ⟨"Persist theme choice and record contrast.", by native_decide⟩
  deltas := ⟨#[
    .modified themeSelectionV2,
    .added themeContrast
  ], by native_decide⟩
}

public def archived? : Except ArchiveError SpecSnapshot :=
  initialSnapshot.archive darkModeChange .accepted

#guard themeContrast.wellFormed
#guard themeSelectionV2.wellFormed
#guard initialSnapshot.wellFormed
#guard darkModeChange.wellFormed
#guard
  match archived? with
  | .ok snap =>
      snap.has "theme.selection" &&
        snap.has "theme.contrast" &&
        (match snap.find? "theme.selection" with
         | some r => r.shall == themeSelectionV2.shall && r.scenarios.size == 2
         | none => false)
  | .error _ => false
#guard
  match ApplicableChange.of initialSnapshot darkModeChange with
  | .ok ac =>
    ac.result.has "theme.selection" && ac.result.has "theme.contrast" &&
      (match ac.archive .accepted with
       | .ok snap => snap == ac.result
       | .error _ => false)
  | .error _ => false
#guard
  match ApplicableChange.of initialSnapshot darkModeChange with
  | .ok ac =>
    match ac.archive .declined with
    | .error .noHumanAccept => true
    | _ => false
  | .error _ => false

end

end LeanSpec.Demo.Archive
