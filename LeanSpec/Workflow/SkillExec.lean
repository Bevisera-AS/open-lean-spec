module

public import LeanSpec.Types
public import LeanSpec.Elab.Skill
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

skill skillExec := {
  id := ⟨"meta.skillexec", by decide +kernel⟩
  oneLiner := ⟨"Load the boot-plan skills; treat them as tracked memory, not chat memory.", by decide +kernel⟩
  purpose := ⟨"Agents follow Lean skills listed by boot-plan, not a generated SKILL.md tree as source.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Load the skills listed by `lake exe lean-spec boot-plan <token>`.", by decide +kernel⟩,
    ⟨"Read those skills; do not load the whole catalog by default.", by decide +kernel⟩,
    ⟨"Use archived Markdown only as a host projection, never as instructions or source. This library does not emit SKILL.md and does not compile markdown into Lean.", by decide +kernel⟩,
    ⟨"Do not weaken a spec, gate, or skill to satisfy a tool.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Following OpenSpec or Cursor SKILL.md when it disagrees with Lean.", by decide +kernel⟩
  ]
}

#guard skillExec.wellFormed

end

end LeanSpec.Workflow
