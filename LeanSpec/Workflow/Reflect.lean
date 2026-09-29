module

public import LeanSpec.Types
public import LeanSpec.Elab.Skill
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

skill reflect := {
  id := ⟨"process.reflect", by native_decide⟩
  oneLiner := ⟨"End-of-task reflection: record durable learning in the Wiki store.", by native_decide⟩
  purpose := ⟨"Consolidate agent experience into the Wiki store, not chat scrollback or prose files.", by native_decide⟩
  rules := ⟨#[
    ⟨"Ask whether the task revealed durable agent-experience knowledge.", by native_decide⟩,
    ⟨"Capture it as a `Reflection` (kind: pattern / failureMode / strategy) and `Wiki.record` it — consolidating with an existing same-learning entry, never duplicating.", by native_decide⟩,
    ⟨"A `Reflection` must cite the runs it was distilled from (`derivedFrom`); the store refuses fabricated provenance.", by native_decide⟩,
    ⟨"If the learning should change a human artifact, set `promoted` (skill / requirement / steering); promotion crosses the valve into the human gate, it is not automatic.", by native_decide⟩,
    ⟨"If nothing durable was learned, say so in the handoff.", by native_decide⟩
  ], by native_decide⟩
  antipatterns := #[
    ⟨"Relying on prior chat to remember current spec or gate state.", by native_decide⟩,
    ⟨"Logging durable learning as prose in a discovery file instead of consolidating it in the Wiki store.", by native_decide⟩
  ]
}

#guard reflect.wellFormed

end

end LeanSpec.Workflow
