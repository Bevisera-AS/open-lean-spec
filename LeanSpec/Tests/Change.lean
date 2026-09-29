import LeanSpec.Change

namespace LeanSpec.Tests.Change

open LeanSpec

def validReq : Raw.Requirement := {
  id := "inventory.reserve"
  shall := "The system reserves stock when an order is confirmed."
  scenarios := #[{
    name := "reserve stock"
    whenText := "an order is confirmed"
    thenText := "stock is reserved"
    check := .deferred "integration fixture pending"
  }]
}

def validRaw : Raw.Change := {
  id := "add-reserve"
  why := "Need inventory reservation."
  deltas := #[.added validReq]
}

private def rejectsAt
    (expectedPath : String) (issue : ValidationIssue)
    (result : Except ValidationError LeanSpec.Change) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == issue
  | .ok _ => false

private def rejectsDeltaAt
    (expectedPath : String) (issue : ValidationIssue)
    (result : Except ValidationError LeanSpec.Delta) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == issue
  | .ok _ => false

theorem validationProjectsRaw
    {raw : Raw.Change} {change : LeanSpec.Change}
    (h : raw.validate "change" = .ok change) : change.toRaw = raw :=
  Raw.Change.validate_sound h

theorem validationCompletes (change : LeanSpec.Change) :
    change.toRaw.validate "change" = .ok change :=
  Raw.Change.validate_complete change "change"

theorem modifiedIsNeverPartial (delta : LeanSpec.Delta) :
    delta.isPartialModified = false :=
  Delta.isPartialModified_eq_false delta

def checks : Array (String × Bool) := #[
  ("valid raw change is accepted", (validRaw.validate "change").isOk),
  ("valid raw change roundtrips",
    match validRaw.validate "change" with
    | .ok change => change.toRaw == validRaw
    | .error _ => false),
  ("blank change id keeps its path",
    rejectsAt "change.id" .blank
      ({ validRaw with id := " \t" }.validate "change")),
  ("blank change why keeps its path",
    rejectsAt "change.why" .blank
      ({ validRaw with why := " " }.validate "change")),
  ("empty deltas keep their path",
    rejectsAt "change.deltas" .emptyArray
      ({ validRaw with deltas := #[] }.validate "change")),
  ("modified id mismatch keeps its path",
    rejectsDeltaAt "delta.id" .idMismatch
      ((Raw.Delta.modified "theme.selection" { validReq with id := "theme.other" }).validate "delta")),
  ("same rename keeps its path",
    rejectsDeltaAt "delta" .sameRename
      ((Raw.Delta.renamed "theme.a" "theme.a").validate "delta")),
  ("invalid rename target keeps its path",
    rejectsDeltaAt "delta.to" .invalidRequirementId
      ((Raw.Delta.renamed "theme.a" "theme..b").validate "delta")),
  ("blank removed reason keeps its path",
    rejectsDeltaAt "delta.reason" .blank
      ((Raw.Delta.removed "theme.legacy" " " "use theme.selection").validate "delta"))
]

end LeanSpec.Tests.Change
