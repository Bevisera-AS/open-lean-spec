import LeanSpec.Types

namespace LeanSpec.Tests.ProcessSkill

open LeanSpec

def validRaw : Raw.ProcessSkill := {
  id := "process.proposeChange"
  oneLiner := "Propose a typed change."
  purpose := "Keep Markdown out of the source of truth."
  rules := #["Write Lean requirements.", "Stop for human review."]
  antipatterns := #["Emitting spec.md as source."]
}

private def rejectsAt
    (expectedPath : String) (issue : ValidationIssue)
    (result : Except ValidationError LeanSpec.ProcessSkill) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == issue
  | .ok _ => false

theorem validationProjectsRaw
    {raw : Raw.ProcessSkill} {skill : LeanSpec.ProcessSkill}
    (h : raw.validate "skill" = .ok skill) : skill.toRaw = raw :=
  Raw.ProcessSkill.validate_sound h

theorem validationCompletes (skill : LeanSpec.ProcessSkill) :
    skill.toRaw.validate "skill" = .ok skill :=
  Raw.ProcessSkill.validate_complete skill "skill"

def checks : Array (String × Bool) := #[
  ("valid raw process skill is accepted", (validRaw.validate "skill").isOk),
  ("valid raw process skill roundtrips",
    match validRaw.validate "skill" with
    | .ok skill => skill.toRaw == validRaw
    | .error _ => false),
  ("blank oneLiner keeps its path",
    rejectsAt "skill.oneLiner" .blank
      ({ validRaw with oneLiner := " \t" }.validate "skill")),
  ("blank purpose keeps its path",
    rejectsAt "skill.purpose" .blank
      ({ validRaw with purpose := "" }.validate "skill")),
  ("empty rules keep their path",
    rejectsAt "skill.rules" .emptyArray
      ({ validRaw with rules := #[] }.validate "skill")),
  ("blank rule keeps its path",
    rejectsAt "skill.rules[0]" .blank
      ({ validRaw with rules := #["  "] }.validate "skill")),
  ("absolute skill id is refused",
    rejectsAt "skill.id" .invalidProcessSkillId
      ({ validRaw with id := "/tmp/escaped" }.validate "skill")),
  ("leading-dot skill id is refused",
    rejectsAt "skill.id" .invalidProcessSkillId
      ({ validRaw with id := ".hidden" }.validate "skill")),
  ("blank antipattern keeps its path",
    rejectsAt "skill.antipatterns[0]" .blank
      ({ validRaw with antipatterns := #[" "] }.validate "skill")),
  ("requires edges roundtrip",
    match ({ validRaw with requires := #["meta.skillexec", "meta.humanGates"] }.validate "skill") with
    | .ok skill => skill.toRaw.requires == #["meta.skillexec", "meta.humanGates"]
    | .error _ => false),
  ("invalid required id keeps its path",
    rejectsAt "skill.requires[0]" .invalidProcessSkillId
      ({ validRaw with requires := #["/tmp/escaped"] }.validate "skill"))
]

end LeanSpec.Tests.ProcessSkill
