module

public import LeanSpec.ProcessSkill
public import LeanSpec.Elab.Skill
public meta import LeanSpec.ProcessSkill
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

/- The propose phase: the spec change, reviewed before any code. -/
skill proposeChange := {
  id := ⟨"process.proposeChange", by decide +kernel⟩
  oneLiner := ⟨"Propose requirements as Lean declarations with examples or Props, reviewed before apply.", by decide +kernel⟩
  purpose := ⟨"State what must hold as `@[requirement]` declarations that `lake exe spec check` accepts, and stop for review before building.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Run `lake exe spec help` first; it is the manual.", by decide +kernel⟩,
    ⟨"A requirement is `@[requirement must]` (or `should`) on a def of type `Sig -> Prop`; its docstring is the label. For a black-box program the signature is `IOSig` and the body is `Req.holds [examples]` or `IOReq pre post`.", by decide +kernel⟩,
    ⟨"Examples are the tests: write them as `ex` values in the body or as `@[example R]` defs, a normal and an edge case per requirement, and no other tests.", by decide +kernel⟩,
    ⟨"A stakeholder-level requirement is `@[requirement must user]` and needs a `@[refines]` theorem from the system requirements that imply it, or a proof of its own.", by decide +kernel⟩,
    ⟨"A docstring is a label only; never put the claim in prose, comments or strings.", by decide +kernel⟩,
    ⟨"`lake exe spec check` must pass before review; the `git diff` of Spec.lean and the digests in `lake exe spec report` show the reviewer what changed.", by decide +kernel⟩,
    ⟨"Do not invent behaviour the task does not define; an undefined input is left undefined, not turned into an error case.", by decide +kernel⟩,
    ⟨"If agent experience motivated this change, cite the Wiki reflection(s) in a `PromotionProposal`; a citation to a reflection the Wiki does not hold is refused.", by decide +kernel⟩,
    ⟨"Stop before apply until the reviewer has accepted the change.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Writing shall/given/when/then text or Markdown instead of a `@[requirement]` declaration.", by decide +kernel⟩,
    ⟨"A requirement whose only evidence is that its text is non-empty.", by decide +kernel⟩,
    ⟨"Error behaviour for inputs the task never defines.", by decide +kernel⟩,
    ⟨"Hand-written test scripts beside the examples.", by decide +kernel⟩,
    ⟨"Starting the program before the spec change is reviewed.", by decide +kernel⟩
  ]
}

#guard proposeChange.wellFormed

end

end LeanSpec.Workflow
