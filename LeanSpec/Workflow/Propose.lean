module

public import LeanSpec.Types
public import LeanSpec.Elab.Skill
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

/- Lean stand-in for OpenSpec's `openspec-propose` SKILL.md. -/
skill proposeChange := {
  id := ⟨"process.proposeChange", by native_decide⟩
  oneLiner := ⟨"Propose a DesignUnit plus a short Requirement label, not Markdown spec.md.", by native_decide⟩
  purpose := ⟨"Create a typed design (interfaces, functions, tests, theorems) with a short SHALL a stakeholder can read.", by native_decide⟩
  rules := ⟨#[
    ⟨"Author a `DesignUnit` first: named interfaces, expected functions, at least one test, and theorems when a proof exists.", by native_decide⟩,
    ⟨"Keep the `Requirement` SHALL a short stakeholder label; scenarios name those artifacts instead of restating the design.", by native_decide⟩,
    ⟨"Modified deltas replace the whole requirement; never paste a partial scenario list.", by native_decide⟩,
    ⟨"Ship the change as a Lean module with `#guard`s; `lake build` of that module is not snapshot archive.", by native_decide⟩,
    ⟨"Do not call the OpenSpec npm CLI, emit SKILL.md, or treat markdown as source.", by native_decide⟩,
    ⟨"Do not restate shall/when/then in module comments; comments are not the spec.", by native_decide⟩,
    ⟨"Do not add a Strata dependency or emit Java/Python from this library; Strata is a later emit/verify backend.", by native_decide⟩,
    ⟨"If agent experience motivated this change, cite the Wiki reflection(s) in the change's `motivations`; the archive gate refuses a citation to a reflection the Wiki does not hold. Pure human-authored changes cite nothing.", by native_decide⟩,
    ⟨"Stop before apply/archive until a human has reviewed the change.", by native_decide⟩
  ], by native_decide⟩
  antipatterns := #[
    ⟨"Emitting openspec/changes/**/spec.md as the source of truth.", by native_decide⟩,
    ⟨"Padding Lean with comments that duplicate the SHALL.", by native_decide⟩,
    ⟨"Writing long product-copy scenarios instead of naming a test or theorem.", by native_decide⟩,
    ⟨"Hand-porting checks into Java/Python/JS instead of keeping DesignUnit as source.", by native_decide⟩,
    ⟨"Compiling markdown into Lean as a source dialect.", by native_decide⟩,
    ⟨"Marking a scenario `.executable` without a `#guard` or test.", by native_decide⟩,
    ⟨"Wrapping @fission-ai/openspec or a Python agent SDK.", by native_decide⟩
  ]
}

#guard proposeChange.wellFormed

end

end LeanSpec.Workflow
