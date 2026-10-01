module

public import LeanSpec.Types
public import LeanSpec.Design
public meta import LeanSpec.Types
public meta import LeanSpec.Design

namespace LeanSpec.Demo.Theme

open LeanSpec

public section

public inductive Theme where
  | light
  | dark
  deriving Repr, BEq, DecidableEq

public structure AppState where
  theme : Theme
  persisted : Bool
  deriving Repr, BEq

public def toggleDark (_before : AppState) : AppState :=
  { theme := .dark, persisted := true }

public def toggleDarkCheck (before after : AppState) : Bool :=
  after.theme == Theme.dark && after.persisted && before.theme != after.theme

/-- The named theme checker holds after `toggleDark` from light. `.executable` on
`themeSelection` remains a claim that this checker exists; it is not a kernel
derivation of the `#guard`. -/
public theorem toggleDarkCheck_of_light (before : AppState) (h : before.theme = .light) :
    toggleDarkCheck before (toggleDark before) = true := by
  simp [toggleDarkCheck, toggleDark, h]
  decide

public def themeSelection : Requirement := {
  id := ⟨"theme.selection", by native_decide⟩
  shall := ⟨"The app lets users switch between light and dark themes, defaulting to system preference.", by native_decide⟩
  strength := .shall
  scenarios := ⟨#[{
    name := ⟨"toggle dark", by native_decide⟩
    given? := some ⟨"the app is in light mode", by native_decide⟩
    whenText := ⟨"the user clicks the theme toggle", by native_decide⟩
    thenText := ⟨"the app switches to dark mode and persists the choice", by native_decide⟩
    check := .executable
  }], by native_decide⟩
}

#guard themeSelection.wellFormed
#guard !themeSelection.hasDeferredChecks
#guard
  let before : AppState := { theme := .light, persisted := false }
  let after := toggleDark before
  toggleDarkCheck before after

public def themeSelectionDesign : DesignUnit := {
  id := themeSelection.id
  interfaces := ⟨#[
    ⟨"Theme", by native_decide⟩,
    ⟨"AppState", by native_decide⟩
  ], by native_decide⟩
  functions := #[
    ⟨"toggleDark", by native_decide⟩,
    ⟨"toggleDarkCheck", by native_decide⟩
  ]
  tests := ⟨#[⟨"toggleDarkCheck", by native_decide⟩], by native_decide⟩
  theorems := #[⟨"toggleDarkCheck_of_light", by native_decide⟩]
}

#guard themeSelectionDesign.wellFormed
#guard themeSelectionDesign.id == themeSelection.id

end

end LeanSpec.Demo.Theme
