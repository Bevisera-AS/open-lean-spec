module

public import LeanSpec.ProcessSkill
public import LeanSpec.Elab.Skill
public meta import LeanSpec.ProcessSkill
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

/- Portable default human interface for spec work.

A company pack may ship its own role skill that boots domain skills. This library
ships the same *job* without company-specific content. -/
skill roleSpecifier := {
  id := ⟨"orchestration.roleSpecifier", by decide +kernel⟩
  oneLiner := ⟨"Default human interface: route work, preserve Lean authority, and triage discoveries.", by decide +kernel⟩
  purpose := ⟨"Default human interface for a lean-spec install.", by decide +kernel⟩
  rules := ⟨#[
    ⟨"Answer routing questions from loaded boot skills.", by decide +kernel⟩,
    ⟨"Keep Lean `@[requirement]` Props as authority before product work.", by decide +kernel⟩,
    ⟨"People read `lake exe spec report` (open, tested, proved, model, refined, signed) and sign off; agents author requirements, examples and proofs.", by decide +kernel⟩,
    ⟨"Commission bounded implementation tasks only after boot and gates are clear.", by decide +kernel⟩,
    ⟨"Triage discoveries into skill updates or a discovery log.", by decide +kernel⟩
  ], by decide +kernel⟩
  antipatterns := #[
    ⟨"Loading archived prompts as instructions.", by decide +kernel⟩,
    ⟨"Treating a checker or an LLM as more authoritative than Lean-owned specs.", by decide +kernel⟩,
    ⟨"Restating the spec in comments so the model follows prose instead of types.", by decide +kernel⟩,
    ⟨"Importing a company-specific role skillset into this library.", by decide +kernel⟩
  ]
}

#guard roleSpecifier.wellFormed

end

end LeanSpec.Workflow
