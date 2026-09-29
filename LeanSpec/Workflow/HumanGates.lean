module

public import LeanSpec.Types
public import LeanSpec.Elab.Skill
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

skill humanGates := {
  id := ⟨"meta.humanGates", by native_decide⟩
  oneLiner := ⟨"Human authority gates: commits, deploys, scope, and public claims.", by native_decide⟩
  purpose := ⟨"Keep machine work inside a human commission.", by native_decide⟩
  rules := ⟨#[
    ⟨"Commit to git only when the human already asked for a commit in the current task.", by native_decide⟩,
    ⟨"Do not deploy, publish, or send stakeholder material without approval.", by native_decide⟩,
    ⟨"Do not expand scope beyond the current commission.", by native_decide⟩,
    ⟨"Stop and ask when a decision would change the external promise, provider posture, or authority hierarchy.", by native_decide⟩
  ], by native_decide⟩
  antipatterns := #[
    ⟨"Treating a successful check as permission to accept or release knowledge.", by native_decide⟩
  ]
}

#guard humanGates.wellFormed

end

end LeanSpec.Workflow
