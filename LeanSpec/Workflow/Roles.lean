module

public import LeanSpec.ProcessSkill
public import LeanSpec.Elab.Skill
public meta import LeanSpec.ProcessSkill
public meta import LeanSpec.Elab.Skill

/-!
The loop the bench runs (`bench/`), as skills: the **builder** writes the spec and
the program; the **referee** is `lake exe spec check`, `test`, `report` and the
`./next` gate; the **reviewer** audits the result into typed findings. The referee
is a program, so it is stated here as gates, not as a role.
-/

namespace LeanSpec.Workflow

open LeanSpec

public section

/- Machine gates between the phases. Beside `humanGates`, which bounds what an
agent may do; these bound when the loop may move on. -/
skill refereeGates := {
  id := ⟨"meta.refereeGates", by decide +kernel⟩
  oneLiner := ⟨"The referee's gates: check before review, test before the next change request, report before acceptance.", by decide +kernel⟩
  purpose := ⟨"Keep the loop honest with checks a program runs, not judgements an agent makes.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"`lake exe spec check` must exit 0 before a proposal goes to review; every problem it lists is fixed, none is argued with.", by decide +kernel⟩,
    ⟨"Apply begins only after a reviewed proposal; the builder does not review its own spec.", by decide +kernel⟩,
    ⟨"`./next` releases the next change request only when `./test.sh` passes; a change request is applied to spec, program and examples together.", by decide +kernel⟩,
    ⟨"`lake exe spec report ./run` must exit 0 before archive: every `must` row proved, model, signed, refined or tested.", by decide +kernel⟩,
    ⟨"Only a person signs off; a green report is evidence for the reviewer, never acceptance.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Editing the spec so that `check` passes instead of fixing what it names.", by decide +kernel⟩,
    ⟨"Calling `./next` before the tests pass, or skipping a change request.", by decide +kernel⟩,
    ⟨"Treating a passing report as sign-off.", by decide +kernel⟩
  ]
}

#guard refereeGates.wellFormed

/- The builder: one agent, one workspace, spec and program kept consistent. -/
skill roleBuilder := {
  id := ⟨"orchestration.roleBuilder", by decide +kernel⟩
  oneLiner := ⟨"Builder: write the spec as Lean declarations with examples, then the program, until the referee passes.", by decide +kernel⟩
  purpose := ⟨"Deliver Spec.lean and the program in one workspace, with examples as the only tests and theorems where properties can be stated.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Work only in the workspace; read nothing outside it, and read the library through `lake exe spec help`, not its sources.", by decide +kernel⟩,
    ⟨"Write Spec.lean first (propose), then the program (apply); keep them consistent when a change request arrives.", by decide +kernel⟩,
    ⟨"Define a requirement before a theorem names it in `@[evidence]`; an unknown name is a compile error and a wasted build.", by decide +kernel⟩,
    ⟨"Prog.lean imports Spec, so a spec edit rebuilds the program; batch spec edits rather than alternating them with builds.", by decide +kernel⟩,
    ⟨"Be economical: no explanations, no summaries, no scratch files outside the workspace; reply DONE when `./next` says there are no more change requests.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Reading the benchmark's reference solution or hidden cases.", by decide +kernel⟩,
    ⟨"Killing processes outside the workspace to recover from a slow build.", by decide +kernel⟩,
    ⟨"Naming program functions `get` or `put` at top level; they clash with Lean's.", by decide +kernel⟩
  ]
}

#guard roleBuilder.wellFormed

/- The reviewer: audits a finished workspace against the ground truth, writes typed findings. -/
skill roleReviewer := {
  id := ⟨"orchestration.roleReviewer", by decide +kernel⟩
  oneLiner := ⟨"Reviewer: accept or return a proposal, audit a finished run against ground truth, write typed findings.", by decide +kernel⟩
  purpose := ⟨"Judge the spec against the task and the program against the spec, and record every defect as a `Finding` the next round can be gated on.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Before apply: read the `git diff` of Spec.lean and `lake exe spec check`; accept the proposal, or return it naming the requirement and what is wrong. Do not edit the workspace.", by decide +kernel⟩,
    ⟨"After the run: read `lake exe spec report ./run` and `statement`; compare the spec with the task text and the program with the spec.", by decide +kernel⟩,
    ⟨"Record each defect as a `Finding`: run id, ground-truth requirement or `-`, kind (specDrift, reprDrift, bug, testGap, flaw), severity 1 to 3, evidence location, one-sentence note.", by decide +kernel⟩,
    ⟨"Invented behaviour the task never defines is spec drift, not a bug; a correct program with a fragile test or a quadratic hot path is a flaw.", by decide +kernel⟩,
    ⟨"Hand findings to the reflect phase: `Finding.toReflection` records them in the Wiki with the run as provenance.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Fixing the workspace instead of recording the finding.", by decide +kernel⟩,
    ⟨"A finding with no evidence location.", by decide +kernel⟩,
    ⟨"Grading the prose of a requirement instead of its examples and theorems.", by decide +kernel⟩
  ]
}

#guard roleReviewer.wellFormed

end

end LeanSpec.Workflow
