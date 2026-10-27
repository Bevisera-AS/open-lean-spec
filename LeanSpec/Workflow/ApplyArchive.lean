module

public import LeanSpec.ProcessSkill
public import LeanSpec.Elab.Skill
public meta import LeanSpec.ProcessSkill
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

/- The apply phase: build until the referee passes, without touching a requirement. -/
skill applyChange := {
  id := ⟨"process.applyChange", by decide +kernel⟩
  oneLiner := ⟨"Implement against reviewed requirements until check, test and report pass; do not sign off.", by decide +kernel⟩
  purpose := ⟨"Make the program satisfy the reviewed `@[requirement]` declarations without changing them.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Work only toward the open rows of `lake exe spec report ./run`: an example that fails, a `must` row that is open.", by decide +kernel⟩,
    ⟨"Keep `lake exe spec check` and `./test.sh` green; `./next` releases the next change request only when `test` passes.", by decide +kernel⟩,
    ⟨"Never edit a requirement, an example or a Prop to make the program or a proof go through; that is a new proposal.", by decide +kernel⟩,
    ⟨"For a Lean product, add `@[satisfies]` theorems `R impl` where a requirement can be proved; add `@[evidence R]` theorems about the functions where it cannot. No sorry. Only `@[satisfies]` closes a row.", by decide +kernel⟩,
    ⟨"Do not write `@[sign_off]` axioms; implementation is not acceptance.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Weakening a requirement or deleting an example during apply instead of proposing a change.", by decide +kernel⟩,
    ⟨"Tagging a theorem `@[evidence]` for a requirement it does not bear on.", by decide +kernel⟩
  ]
}

#guard applyChange.wellFormed

/- The archive phase: acceptance is a person's judgement, recorded in Lean. -/
skill archiveChange := {
  id := ⟨"process.archiveChange", by decide +kernel⟩
  oneLiner := ⟨"Accept a change by a named human sign-off over the requirement digests and commit the report.", by decide +kernel⟩
  purpose := ⟨"Acceptance is a human judgement recorded in Lean, not a merge of text.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"A person accepts with `@[sign_off who \"digest\"] axiom a : SignOff R impl`, quoting `#requirement_digest R`; what code proves needs no sign-off.", by decide +kernel⟩,
    ⟨"Commit `lake exe spec report ./run` next to the spec; the commit binds the report, and its digests are what the next proposal is compared against.", by decide +kernel⟩,
    ⟨"A passing build, a closed statement or a passing report is not acceptance.", by decide +kernel⟩,
    ⟨"When the requirement changes, its digest changes and the old sign-off goes stale; it must be signed again.", by decide +kernel⟩,
    ⟨"Only a human may add or renew a sign-off; the commit is signed by that person.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Signing off because the model or the implementer is done.", by decide +kernel⟩,
    ⟨"Copying an old digest into a new sign-off without reading the changed requirement.", by decide +kernel⟩
  ]
}

#guard archiveChange.wellFormed

end

end LeanSpec.Workflow
