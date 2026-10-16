module

public import LeanSpec.Types
public import LeanSpec.Elab.Skill
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

skill applyChange := {
  id := ⟨"process.applyChange", by decide +kernel⟩
  oneLiner := ⟨"Apply an accepted change's tasks; do not archive or accept knowledge.", by decide +kernel⟩
  purpose := ⟨"Implement against a reviewed Lean change without merging it into the spec snapshot.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Work only the tasks implied by the current DesignUnit and change.", by decide +kernel⟩,
    ⟨"Keep `lake build` and `lake test` green on the slice.", by decide +kernel⟩,
    ⟨"Do not archive deltas or treat implementation as spec acceptance.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Editing the spec snapshot during apply instead of the change module.", by decide +kernel⟩
  ]
}

#guard applyChange.wellFormed

skill archiveChange := {
  id := ⟨"process.archiveChange", by decide +kernel⟩
  oneLiner := ⟨"Merge a reviewed change into the spec snapshot after a human accept.", by decide +kernel⟩
  purpose := ⟨"Archive is governed merge, not Markdown concat.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Call `SpecSnapshot.archive` with `ArchiveDecision.accepted`; a passing check is not accept.", by decide +kernel⟩,
    ⟨"Without that decision the snapshot file must not change (`noHumanAccept`).", by decide +kernel⟩,
    ⟨"`--human` is a caller flag, not a verified identity or `lake build` receipt.", by decide +kernel⟩,
    ⟨"Modified deltas must be full replacements; sequential deltas are the merge order.", by decide +kernel⟩,
    ⟨"Only a human accept may merge into the current spec snapshot.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Archiving because the model or the implementer is done.", by decide +kernel⟩,
    ⟨"Concatenating Markdown spec.md files instead of applying typed deltas.", by decide +kernel⟩
  ]
}

#guard archiveChange.wellFormed

end

end LeanSpec.Workflow
