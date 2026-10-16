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

@[expose] public def themeSelection : Requirement := {
  id := ⟨"theme.selection", by decide +kernel⟩
  shall := ⟨"The app lets users switch between light and dark themes, defaulting to system preference.", by decide +kernel⟩
  strength := .shall
  scenarios := ⟨#[{
    name := ⟨"toggle dark", by decide +kernel⟩
    given? := some ⟨"the app is in light mode", by decide +kernel⟩
    whenText := ⟨"the user clicks the theme toggle", by decide +kernel⟩
    thenText := ⟨"the app switches to dark mode and persists the choice", by decide +kernel⟩
    check := .executable
  }], by decide +kernel⟩
}

#guard themeSelection.wellFormed
#guard !themeSelection.hasDeferredChecks
#guard
  let before : AppState := { theme := .light, persisted := false }
  let after := toggleDark before
  toggleDarkCheck before after

@[expose] public def themeSelectionDesign : DesignUnit := {
  id := themeSelection.id
  interfaces := ⟨#[
    ⟨"Theme", by decide +kernel⟩,
    ⟨"AppState", by decide +kernel⟩
  ], by decide +kernel⟩
  functions := #[
    ⟨"toggleDark", by decide +kernel⟩,
    ⟨"toggleDarkCheck", by decide +kernel⟩
  ]
  tests := ⟨#[⟨"toggleDarkCheck", by decide +kernel⟩], by decide +kernel⟩
  theorems := #[⟨"toggleDarkCheck_of_light", by decide +kernel⟩]
}

#guard themeSelectionDesign.wellFormed
#guard themeSelectionDesign.id == themeSelection.id

end

end LeanSpec.Demo.Theme
