module

public import LeanSpec.ProcessSkill
public import LeanSpec.Elab.Skill
public meta import LeanSpec.ProcessSkill
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

/- The reflect phase: durable learning, with provenance, in the Wiki store. -/
skill reflect := {
  id := ⟨"process.reflect", by decide +kernel⟩
  oneLiner := ⟨"End-of-task reflection: record durable learning and reviewer findings in the Wiki store.", by decide +kernel⟩
  purpose := ⟨"Consolidate agent experience into the Wiki store, not chat scrollback or prose files.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Ask whether the task revealed durable agent-experience knowledge.", by decide +kernel⟩,
    ⟨"Capture it as a `Reflection` (kind: pattern / failureMode / strategy) and `Wiki.record` it, consolidating with an existing same-learning entry, never duplicating.", by decide +kernel⟩,
    ⟨"A reviewer's `Finding` (spec drift, representation drift, bug, test gap, flaw) becomes a `Reflection` through `Finding.toReflection`: drift, bugs and gaps are failure modes, flaws are patterns, and the run id is the provenance.", by decide +kernel⟩,
    ⟨"A `Reflection` must cite the runs it was distilled from (`derivedFrom`); the store refuses fabricated provenance.", by decide +kernel⟩,
    ⟨"If the learning should change a human artifact, set `promoted` (skill / requirement / steering); promotion crosses the valve into the human gate, it is not automatic.", by decide +kernel⟩,
    ⟨"If nothing durable was learned, say so in the handoff.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Relying on prior chat to remember current spec or gate state.", by decide +kernel⟩,
    ⟨"Logging durable learning as prose in a discovery file instead of consolidating it in the Wiki store.", by decide +kernel⟩
  ]
}

#guard reflect.wellFormed

end

end LeanSpec.Workflow
