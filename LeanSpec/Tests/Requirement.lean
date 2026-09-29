import LeanSpec.Types

namespace LeanSpec.Tests.Requirement

open LeanSpec

def validScenario : Raw.Scenario := {
  name := "reserve stock"
  given? := some "stock is available"
  whenText := "an order is confirmed"
  thenText := "stock is reserved"
  check := .deferred "integration fixture pending"
}

def validRaw : Raw.Requirement := {
  id := "inventory.reserve"
  shall := "The system reserves stock when an order is confirmed."
  scenarios := #[validScenario]
}

private def rejectsAt
    (expectedPath : String) (issue : ValidationIssue)
    (result : Except ValidationError LeanSpec.Requirement) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == issue
  | .ok _ => false

theorem validationProjectsRaw
    {raw : Raw.Requirement} {requirement : LeanSpec.Requirement}
    (h : raw.validate "requirement" = .ok requirement) : requirement.toRaw = raw :=
  Raw.Requirement.validate_sound h

theorem validationCompletes (requirement : LeanSpec.Requirement) :
    requirement.toRaw.validate "requirement" = .ok requirement :=
  Raw.Requirement.validate_complete requirement "requirement"

def checks : Array (String × Bool) := #[
  ("valid raw requirement is accepted", (validRaw.validate "requirement").isOk),
  ("valid raw requirement roundtrips",
    match validRaw.validate "requirement" with
    | .ok requirement => requirement.toRaw == validRaw
    | .error _ => false),
  ("blank shall keeps its path",
    rejectsAt "requirement.shall" .blank
      ({ validRaw with shall := " \t" }.validate "requirement")),
  ("invalid id empty segment keeps its path",
    rejectsAt "requirement.id" .invalidRequirementId
      ({ validRaw with id := "inventory..x" }.validate "requirement")),
  ("digit-starting id segment keeps its path",
    rejectsAt "requirement.id" .invalidRequirementId
      ({ validRaw with id := "inventory.2reserve" }.validate "requirement")),
  ("empty scenarios keep their path",
    rejectsAt "requirement.scenarios" .emptyArray
      ({ validRaw with scenarios := #[] }.validate "requirement"))
]

end LeanSpec.Tests.Requirement
