import LeanSpec.Design
import LeanSpec.Demo.Theme

namespace LeanSpec.Tests.Design

open LeanSpec
open LeanSpec.Demo.Theme

def validRaw : Raw.DesignUnit := {
  id := "theme.selection"
  interfaces := #["Theme", "AppState"]
  functions := #["toggleDark", "toggleDarkCheck"]
  tests := #["toggleDarkCheck"]
  theorems := #["toggleDarkCheck_of_light"]
}

private def rejectsAt
    (expectedPath : String) (issue : ValidationIssue)
    (result : Except ValidationError LeanSpec.DesignUnit) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == issue
  | .ok _ => false

theorem validationProjectsRaw
    {raw : Raw.DesignUnit} {design : LeanSpec.DesignUnit}
    (h : raw.validate "design" = .ok design) : design.toRaw = raw :=
  Raw.DesignUnit.validate_sound h

theorem validationCompletes (design : LeanSpec.DesignUnit) :
    design.toRaw.validate "design" = .ok design :=
  Raw.DesignUnit.validate_complete design "design"

def checks : Array (String × Bool) := #[
  ("valid raw design is accepted", (validRaw.validate "design").isOk),
  ("valid raw design roundtrips",
    match validRaw.validate "design" with
    | .ok design => design.toRaw == validRaw
    | .error _ => false),
  ("theme design matches theme requirement id",
    themeSelectionDesign.id == themeSelection.id && themeSelectionDesign.wellFormed),
  ("empty interfaces keep their path",
    rejectsAt "design.interfaces" .emptyArray
      ({ validRaw with interfaces := #[] }.validate "design")),
  ("empty tests keep their path",
    rejectsAt "design.tests" .emptyArray
      ({ validRaw with tests := #[] }.validate "design")),
  ("blank interface keeps its path",
    rejectsAt "design.interfaces[0]" .blank
      ({ validRaw with interfaces := #["  "] }.validate "design")),
  ("invalid id keeps its path",
    rejectsAt "design.id" .invalidRequirementId
      ({ validRaw with id := "theme..x" }.validate "design")),
  ("web + typescript is accepted",
    ({ validRaw with surface := "web", target := "typescript" }.validate "design").isOk),
  ("web + rust is refused as disallowed target",
    rejectsAt "design.target" .disallowedTarget
      ({ validRaw with surface := "web", target := "rust" }.validate "design")),
  ("native + typescript is refused as disallowed target",
    rejectsAt "design.target" .disallowedTarget
      ({ validRaw with surface := "native", target := "typescript" }.validate "design")),
  ("unknown target token is refused",
    rejectsAt "design.target" .disallowedTarget
      ({ validRaw with target := "python" }.validate "design")),
  ("unknown surface token is refused",
    rejectsAt "design.surface" .disallowedTarget
      ({ validRaw with surface := "desktop" }.validate "design")),
  ("java is allowed on native via strata token",
    ({ validRaw with surface := "native", target := "java-via-strata" }.validate "design").isOk)
]

end LeanSpec.Tests.Design
