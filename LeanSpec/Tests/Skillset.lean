import LeanSpec.Skillset
import LeanSpec.Workflow.Catalog

namespace LeanSpec.Tests.Skillset

open LeanSpec
open LeanSpec.Workflow

def validRaw : Raw.Skillset := {
  id := "skillset.specChange"
  pasteToken := "spec-change"
  mission := "Specify and change behaviour as Lean requirements."
  roleSkill := "orchestration.roleSpecifier"
  boot := #["orchestration.roleSpecifier", "process.proposeChange"]
  reads := #["README.md"]
}

private def rejectsAt
    (expectedPath : String) (issue : ValidationIssue)
    (result : Except ValidationError LeanSpec.Skillset) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == issue
  | .ok _ => false

theorem validationProjectsRaw
    {raw : Raw.Skillset} {skillset : LeanSpec.Skillset}
    (h : raw.validate "skillset" = .ok skillset) : skillset.toRaw = raw :=
  Raw.Skillset.validate_sound h

theorem validationCompletes (skillset : LeanSpec.Skillset) :
    skillset.toRaw.validate "skillset" = .ok skillset :=
  Raw.Skillset.validate_complete skillset "skillset"

def checks : Array (String × Bool) := #[
  ("valid raw skillset is accepted", (validRaw.validate "skillset").isOk),
  ("valid raw skillset roundtrips",
    match validRaw.validate "skillset" with
    | .ok skillset => skillset.toRaw == validRaw
    | .error _ => false),
  ("blank mission keeps its path",
    rejectsAt "skillset.mission" .blank
      ({ validRaw with mission := " \t" }.validate "skillset")),
  ("empty boot keeps its path",
    rejectsAt "skillset.boot" .emptyArray
      ({ validRaw with boot := #[] }.validate "skillset")),
  ("unsafe skillset id is refused",
    rejectsAt "skillset.id" .invalidProcessSkillId
      ({ validRaw with id := "/tmp/escaped" }.validate "skillset")),
  ("roleSkill missing from boot keeps its path",
    rejectsAt "skillset.roleSkill" .roleNotInBoot
      ({ validRaw with boot := #["process.proposeChange"] }.validate "skillset")),
  ("spec-change skillset is well-formed", specChange.wellFormed)
]

end LeanSpec.Tests.Skillset
