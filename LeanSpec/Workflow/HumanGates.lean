module

public import LeanSpec.ProcessSkill
public import LeanSpec.Elab.Skill
public meta import LeanSpec.ProcessSkill
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

skill humanGates := {
  id := ⟨"meta.humanGates", by decide +kernel⟩
  oneLiner := ⟨"Human authority gates: commits, deploys, scope, and public claims.", by decide +kernel⟩
  purpose := ⟨"Keep machine work inside a human commission.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Commit to git only when the human already asked for a commit in the current task.", by decide +kernel⟩,
    ⟨"Do not deploy, publish, or send stakeholder material without approval.", by decide +kernel⟩,
    ⟨"Do not expand scope beyond the current commission.", by decide +kernel⟩,
    ⟨"Stop and ask when a decision would change the external promise, provider posture, or authority hierarchy.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Treating a successful check as permission to accept or release knowledge.", by decide +kernel⟩
  ]
}

#guard humanGates.wellFormed

end

end LeanSpec.Workflow
