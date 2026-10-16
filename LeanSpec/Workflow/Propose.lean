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
  id := ⟨"process.proposeChange", by decide +kernel⟩
  oneLiner := ⟨"Propose a DesignUnit plus a short Requirement label, not Markdown spec.md.", by decide +kernel⟩
  purpose := ⟨"Create a typed design (interfaces, functions, tests, theorems) with a short SHALL a stakeholder can read.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Author a `DesignUnit` first: named interfaces, expected functions, at least one test, and theorems when a proof exists.", by decide +kernel⟩,
    ⟨"Keep the `Requirement` SHALL a short stakeholder label; scenarios name those artifacts instead of restating the design.", by decide +kernel⟩,
    ⟨"Modified deltas replace the whole requirement; never paste a partial scenario list.", by decide +kernel⟩,
    ⟨"Ship the change as a Lean module with `#guard`s; `lake build` of that module is not snapshot archive.", by decide +kernel⟩,
    ⟨"Do not call the OpenSpec npm CLI, emit SKILL.md, or treat markdown as source.", by decide +kernel⟩,
    ⟨"Do not restate shall/when/then in module comments; comments are not the spec.", by decide +kernel⟩,
    ⟨"Do not add a Strata dependency or emit Java/Python from this library; Strata is a later emit/verify backend.", by decide +kernel⟩,
    ⟨"If agent experience motivated this change, cite the Wiki reflection(s) in the change's `motivations`; the archive gate refuses a citation to a reflection the Wiki does not hold. Pure human-authored changes cite nothing.", by decide +kernel⟩,
    ⟨"Stop before apply/archive until a human has reviewed the change.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Emitting openspec/changes/**/spec.md as the source of truth.", by decide +kernel⟩,
    ⟨"Padding Lean with comments that duplicate the SHALL.", by decide +kernel⟩,
    ⟨"Writing long product-copy scenarios instead of naming a test or theorem.", by decide +kernel⟩,
    ⟨"Hand-porting checks into Java/Python/JS instead of keeping DesignUnit as source.", by decide +kernel⟩,
    ⟨"Compiling markdown into Lean as a source dialect.", by decide +kernel⟩,
    ⟨"Marking a scenario `.executable` without a `#guard` or test.", by decide +kernel⟩,
    ⟨"Wrapping @fission-ai/openspec or a Python agent SDK.", by decide +kernel⟩
  ]
}

#guard proposeChange.wellFormed

end

end LeanSpec.Workflow
