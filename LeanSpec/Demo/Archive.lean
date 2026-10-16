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
  id := ⟨"theme.contrast", by decide +kernel⟩
  shall := ⟨"Dark theme documents a minimum contrast target.", by decide +kernel⟩
  strength := .should
  scenarios := ⟨#[{
    name := ⟨"contrast stated", by decide +kernel⟩
    whenText := ⟨"dark theme is active", by decide +kernel⟩
    thenText := ⟨"contrast is recorded as a requirement", by decide +kernel⟩
    check := .deferred ⟨"no pixel checker yet", by decide +kernel⟩
  }], by decide +kernel⟩
}

public def themeSelectionV2 : Requirement := {
  id := themeSelection.id
  shall := ⟨themeSelection.shall.value ++ " The choice persists across restart.", by decide +kernel⟩
  strength := themeSelection.strength
  scenarios := themeSelection.scenarios.push {
    name := ⟨"persist across restart", by decide +kernel⟩
    given? := some ⟨"the user already chose dark", by decide +kernel⟩
    whenText := ⟨"the user restarts the app", by decide +kernel⟩
    thenText := ⟨"the app opens in dark mode", by decide +kernel⟩
    check := .deferred ⟨"no persistence fixture yet", by decide +kernel⟩
  }
}

public def initialSnapshot : SpecSnapshot := {
  requirements := #[themeSelection]
  uniqueIds := by decide +kernel
  designs := #[themeSelectionDesign]
  uniqueDesignIds := by decide +kernel
  designsLinked := by decide +kernel
}

public def darkModeChange : Change := {
  id := ⟨"dark-mode-v2", by decide +kernel⟩
  why := ⟨"Persist theme choice and record contrast.", by decide +kernel⟩
  deltas := ⟨#[
    .modified themeSelectionV2,
    .added themeContrast
  ], by decide +kernel⟩
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
