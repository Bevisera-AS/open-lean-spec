module

public import LeanSpec.Elab.Skill
public import LeanSpec.Types
public meta import LeanSpec.Elab.Skill
public meta import LeanSpec.Types

namespace LeanSpec.Demo.SkillSyntax

open LeanSpec

skill ping := {
  id := ⟨"demo.ping", by native_decide⟩
  oneLiner := ⟨"Demo skill declared with the skill command.", by native_decide⟩
  purpose := ⟨"Show that `skill` expands to a ProcessSkill.", by native_decide⟩
  rules := ⟨#[⟨"Lean ProcessSkill values are the instructions.", by native_decide⟩], by native_decide⟩
  antipatterns := #[⟨"Treating Markdown as the skill source.", by native_decide⟩]
}

#guard ping.wellFormed
#guard ping.id.value == "demo.ping"
#guard (registeredSkills%.map (fun p => p.2.id.value)).toList.contains "demo.ping"
#guard !skillIdTaken (registeredSkills%.map (·.2)) "demo.missing"

end LeanSpec.Demo.SkillSyntax
