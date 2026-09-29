import LeanSpec.Validated

namespace LeanSpec.Tests.Validated

open LeanSpec

theorem parsedNonBlankIsSound :
    NonBlank.parse "shall" "reserve stock" = .ok result →
      result.value = "reserve stock" ∧ LeanUtil.nonemptyText "reserve stock" = true :=
  NonBlank.parse_sound

theorem parsedNonBlankIsComplete (result : NonBlank) :
    NonBlank.parse "shall" result.value = .ok result :=
  NonBlank.parse_complete result

theorem parsedRequirementIdIsSound :
    RequirementId.parse "id" "inventory.reserve_2" = .ok result →
      result.value = "inventory.reserve_2" ∧ ValidRequirementId "inventory.reserve_2" :=
  RequirementId.parse_sound

theorem parsedRequirementIdIsComplete (result : RequirementId) :
    RequirementId.parse "id" result.value = .ok result :=
  RequirementId.parse_complete result

theorem parsedNonEmptyArrayIsSound :
    NonEmptyArray.ofArray "scenarios" #["one"] = .ok result →
      result.items = #["one"] ∧ 0 < (#["one"] : Array String).size :=
  NonEmptyArray.ofArray_sound

theorem parsedNonEmptyArrayIsComplete (result : NonEmptyArray String) :
    NonEmptyArray.ofArray "scenarios" result.items = .ok result :=
  NonEmptyArray.ofArray_complete result

theorem parsedProcessSkillIdIsSound :
    ProcessSkillId.parse "id" "meta.humanGates" = .ok result →
      result.value = "meta.humanGates" ∧ ValidProcessSkillId "meta.humanGates" :=
  ProcessSkillId.parse_sound

theorem parsedProcessSkillIdIsComplete (result : ProcessSkillId) :
    ProcessSkillId.parse "id" result.value = .ok result :=
  ProcessSkillId.parse_complete result

def checks : Array (String × Bool) := #[
  ("NonBlank accepts visible text",
    (NonBlank.parse "shall" "reserve stock").isOk),
  ("NonBlank rejects whitespace",
    match NonBlank.parse "shall" " \n\t" with
    | .error error =>
        error == { path := "shall", issue := .blank, rejected := some " \n\t" }
    | .ok _ => false),
  ("RequirementId accepts dotted segments",
    (RequirementId.parse "id" "inventory.reserve_2").isOk),
  ("RequirementId rejects an empty segment",
    match RequirementId.parse "id" "inventory..reserve" with
    | .error error =>
        error == {
          path := "id"
          issue := .invalidRequirementId
          rejected := some "inventory..reserve"
        }
    | .ok _ => false),
  ("RequirementId rejects a digit-starting segment",
    match RequirementId.parse "id" "inventory.2reserve" with
    | .error _ => true
    | .ok _ => false),
  ("RequirementId rejects path separators",
    match RequirementId.parse "id" "inventory/reserve" with
    | .error _ => true
    | .ok _ => false),
  ("NonEmptyArray accepts one element",
    (NonEmptyArray.ofArray "scenarios" #["one"]).isOk),
  ("NonEmptyArray rejects no elements",
    match NonEmptyArray.ofArray "scenarios" (#[] : Array String) with
    | .error error => error == { path := "scenarios", issue := .emptyArray }
    | .ok _ => false),
  ("ProcessSkillId accepts dotted ids",
    (ProcessSkillId.parse "id" "meta.humanGates").isOk),
  ("ProcessSkillId rejects an absolute path",
    match ProcessSkillId.parse "id" "/tmp/escaped" with
    | .error error =>
        error == {
          path := "id"
          issue := .invalidProcessSkillId
          rejected := some "/tmp/escaped"
        }
    | .ok _ => false),
  ("ProcessSkillId rejects a leading dash",
    match ProcessSkillId.parse "id" "-hidden" with
    | .error _ => true
    | .ok _ => false)
]

end LeanSpec.Tests.Validated
