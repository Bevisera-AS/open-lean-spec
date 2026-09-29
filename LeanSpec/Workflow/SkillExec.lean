module

public import LeanSpec.Types
public import LeanSpec.Elab.Skill
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

skill skillExec := {
  id := ⟨"meta.skillexec", by native_decide⟩
  oneLiner := ⟨"Load the boot-plan skills; treat them as tracked memory, not chat memory.", by native_decide⟩
  purpose := ⟨"Agents follow Lean skills listed by boot-plan, not a generated SKILL.md tree as source.", by native_decide⟩
  rules := ⟨#[
    ⟨"Load the skills listed by `lake exe lean-spec boot-plan <token>`.", by native_decide⟩,
    ⟨"Read those skills; do not load the whole catalog by default.", by native_decide⟩,
    ⟨"Use archived Markdown only as a host projection, never as instructions or source. This library does not emit SKILL.md and does not compile markdown into Lean.", by native_decide⟩,
    ⟨"Do not weaken a spec, gate, or skill to satisfy a tool.", by native_decide⟩
  ], by native_decide⟩
  antipatterns := #[
    ⟨"Following OpenSpec or Cursor SKILL.md when it disagrees with Lean.", by native_decide⟩
  ]
}

#guard skillExec.wellFormed

end

end LeanSpec.Workflow
