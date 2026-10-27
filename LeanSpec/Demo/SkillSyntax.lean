module

public import LeanSpec.Elab.Skill
public import LeanSpec.ProcessSkill
public meta import LeanSpec.Elab.Skill
public meta import LeanSpec.ProcessSkill

namespace LeanSpec.Demo.SkillSyntax

open LeanSpec

skill ping := {
  id := ⟨"demo.ping", by decide +kernel⟩
  oneLiner := ⟨"Demo skill declared with the skill command.", by decide +kernel⟩
  purpose := ⟨"Show that `skill` expands to a ProcessSkill.", by decide +kernel⟩
  rules := ⟨#[⟨"Lean ProcessSkill values are the instructions.", by decide +kernel⟩], by decide +kernel⟩
  antipatterns := #[⟨"Treating Markdown as the skill source.", by decide +kernel⟩]
}

#guard ping.wellFormed
#guard ping.id.value == "demo.ping"
#guard (registeredSkills%.map (fun p => p.2.id.value)).toList.contains "demo.ping"
#guard !skillIdTaken (registeredSkills%.map (·.2)) "demo.missing"

end LeanSpec.Demo.SkillSyntax
