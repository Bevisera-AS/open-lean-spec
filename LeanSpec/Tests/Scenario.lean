import LeanSpec.Types

namespace LeanSpec.Tests.Scenario

open LeanSpec

def validRaw : Raw.Scenario := {
  name := "reserve stock"
  given? := some "stock is available"
  whenText := "an order is confirmed"
  thenText := "stock is reserved"
  check := .deferred "integration fixture pending"
}

private def rejectsBlankAt
    (expectedPath : String) (result : Except ValidationError LeanSpec.Scenario) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == .blank
  | .ok _ => false

theorem validationProjectsRaw
    {raw : Raw.Scenario} {scenario : LeanSpec.Scenario}
    (h : raw.validate "scenario" = .ok scenario) : scenario.toRaw = raw :=
  Raw.Scenario.validate_sound h

theorem validationCompletes (scenario : LeanSpec.Scenario) :
    scenario.toRaw.validate "scenario" = .ok scenario :=
  Raw.Scenario.validate_complete scenario "scenario"

def checks : Array (String × Bool) := #[
  ("valid raw scenario is accepted", (validRaw.validate "scenario").isOk),
  ("valid raw scenario roundtrips",
    match validRaw.validate "scenario" with
    | .ok scenario => scenario.toRaw == validRaw
    | .error _ => false),
  ("blank scenario name keeps its path",
    rejectsBlankAt "requirement.scenarios[0].name"
      ({ validRaw with name := " \t" }.validate "requirement.scenarios[0]")),
  ("blank present given keeps its path",
    rejectsBlankAt "requirement.scenarios[0].given"
      ({ validRaw with given? := some " " }.validate "requirement.scenarios[0]")),
  ("blank scenario when keeps its path",
    rejectsBlankAt "requirement.scenarios[0].when"
      ({ validRaw with whenText := "\n" }.validate "requirement.scenarios[0]")),
  ("blank scenario then keeps its path",
    rejectsBlankAt "requirement.scenarios[0].then"
      ({ validRaw with thenText := "" }.validate "requirement.scenarios[0]")),
  ("blank deferred reason keeps its path",
    rejectsBlankAt "requirement.scenarios[0].check.reason"
      ({ validRaw with check := .deferred " " }.validate "requirement.scenarios[0]"))
]

end LeanSpec.Tests.Scenario
