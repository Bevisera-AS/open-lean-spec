module

public import LeanSpec.Elab.Sugar
public import LeanSpec.Trace
public import LeanSpec.Reflection
public meta import LeanSpec.Elab.Sugar
public meta import LeanSpec.Trace
public meta import LeanSpec.Reflection

/-!
# Sugar syntax demo

Shows the human-friendly `requirement ... where` surface syntax
alongside the `AgentTrace` / `Reflection` types.

Compare with `LeanSpec/Demo/SpecSyntax.lean` which uses the raw structure literals.
-/

namespace LeanSpec.Demo.SugarSyntax

open LeanSpec

-- ─── Requirement via sugar ───────────────────────────────────────────────────

requirement overviewDashboard where
  id    "page.overview-dashboard"
  shall "Display a summary dashboard with national averages per grade"
  strength must

  scenario "latest year shown on load"
    given "the user navigates to the overview page"
    when  "the page finishes loading"
    then_ "national averages for the latest available year are displayed"
    check deferred "dashboard UI not yet built"

  scenario "grade selector filters data"
    given "the dashboard is loaded with all grades visible"
    when  "the user selects a single grade from the filter"
    then_ "only that grade's data remains on screen"
    check deferred "filter component not yet built"

-- The sugar produces the same proof-carrying Requirement as hand-written literals:
#guard overviewDashboard.wellFormed
#guard overviewDashboard.id.value == "page.overview-dashboard"
#guard overviewDashboard.strength == .must
#guard overviewDashboard.scenarios.size == 2
#guard overviewDashboard.hasDeferredChecks

-- It registers via the underlying `spec` command:
#guard (registeredSpecs%.map (fun p => p.2.id.value)).toList.contains "page.overview-dashboard"

-- ─── A second requirement with executable checks ────────────────────────────

requirement themeToggle where
  id    "ui.theme-toggle"
  shall "Allow the user to switch between light and dark themes"

  scenario "toggle from light to dark"
    when  "the user clicks the theme toggle while in light mode"
    then_ "the interface switches to dark mode"
    check executable

  scenario "toggle from dark to light"
    when  "the user clicks the theme toggle while in dark mode"
    then_ "the interface switches to light mode"
    check executable

#guard themeToggle.wellFormed
#guard !themeToggle.hasDeferredChecks
#guard themeToggle.strength == .shall  -- default

-- ─── Agent trace example ─────────────────────────────────────────────────────

/-- Example trace: an agent implementing the theme toggle requirement. -/
def themeToggleTrace : AgentTrace := {
  runId := ⟨"run-20250115-theme", by native_decide⟩
  changeId := some ⟨"ui.theme-toggle", by native_decide⟩
  model := ⟨"claude-sonnet-4-20250514", by native_decide⟩
  steps := ⟨#[
    { timestamp := ⟨"2025-01-15T10:00:00Z", by native_decide⟩
      kind := .observation
      content := ⟨"Read existing Theme type and toggleDark function", by native_decide⟩
      cites := #[⟨"ui.theme-toggle", by native_decide⟩] },
    { timestamp := ⟨"2025-01-15T10:01:00Z", by native_decide⟩
      kind := .decision
      content := ⟨"Will add a #guard for the round-trip property", by native_decide⟩
      cites := #[⟨"ui.theme-toggle", by native_decide⟩] },
    { timestamp := ⟨"2025-01-15T10:02:00Z", by native_decide⟩
      kind := .toolCall
      content := ⟨"Wrote toggleDarkCheck_of_light theorem", by native_decide⟩
      cites := #[⟨"ui.theme-toggle", by native_decide⟩] }
  ], by native_decide⟩
  outcome := .completed #[⟨"LeanSpec/Demo/Theme.lean", by native_decide⟩]
}

#guard themeToggleTrace.wellFormed
#guard themeToggleTrace.steps.size == 3
-- Every step cites the requirement it implements:
#guard themeToggleTrace.steps.toArray.all (fun s => s.cites.size > 0)

/-- Reflection consolidated from the theme toggle trace (one run here; the type
takes many). Agent-axis knowledge — see `LeanSpec/Reflection.lean`. -/
def themeToggleReflection : Reflection := {
  id := ⟨"wiki.enum-toggle-canary", by native_decide⟩
  kind := .pattern
  learning := ⟨"Round-trip properties on enum toggles are trivial but good canaries", by native_decide⟩
  derivedFrom := ⟨#[⟨"run-20250115-theme", by native_decide⟩], by decide⟩
  promoted := .noAction
}

-- Provenance is coherent against the run it was derived from.
#guard themeToggleReflection.coherentIn #[themeToggleTrace.runId.value]

end LeanSpec.Demo.SugarSyntax
