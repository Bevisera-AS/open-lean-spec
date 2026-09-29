module

public import LeanSpec.Types
public import LeanSpec.Elab.Skill
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

skill applyChange := {
  id := ⟨"process.applyChange", by native_decide⟩
  oneLiner := ⟨"Apply an accepted change's tasks; do not archive or accept knowledge.", by native_decide⟩
  purpose := ⟨"Implement against a reviewed Lean change without merging it into the spec snapshot.", by native_decide⟩
  rules := ⟨#[
    ⟨"Work only the tasks implied by the current DesignUnit and change.", by native_decide⟩,
    ⟨"Keep `lake build` and `lake test` green on the slice.", by native_decide⟩,
    ⟨"Do not archive deltas or treat implementation as spec acceptance.", by native_decide⟩
  ], by native_decide⟩
  antipatterns := #[
    ⟨"Editing the spec snapshot during apply instead of the change module.", by native_decide⟩
  ]
}

#guard applyChange.wellFormed

skill archiveChange := {
  id := ⟨"process.archiveChange", by native_decide⟩
  oneLiner := ⟨"Merge a reviewed change into the spec snapshot after a human accept.", by native_decide⟩
  purpose := ⟨"Archive is governed merge, not Markdown concat.", by native_decide⟩
  rules := ⟨#[
    ⟨"Call `SpecSnapshot.archive` with `ArchiveDecision.accepted`; a passing check is not accept.", by native_decide⟩,
    ⟨"Without that decision the snapshot file must not change (`noHumanAccept`).", by native_decide⟩,
    ⟨"`--human` is a caller flag, not a verified identity or `lake build` receipt.", by native_decide⟩,
    ⟨"Modified deltas must be full replacements; sequential deltas are the merge order.", by native_decide⟩,
    ⟨"Only a human accept may merge into the current spec snapshot.", by native_decide⟩
  ], by native_decide⟩
  antipatterns := #[
    ⟨"Archiving because the model or the implementer is done.", by native_decide⟩,
    ⟨"Concatenating Markdown spec.md files instead of applying typed deltas.", by native_decide⟩
  ]
}

#guard archiveChange.wellFormed

end

end LeanSpec.Workflow
