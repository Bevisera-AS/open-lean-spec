module

public import LeanSpec.Types
public import LeanSpec.Elab.Skill
public meta import LeanSpec.Types
public meta import LeanSpec.Elab.Skill

namespace LeanSpec.Workflow

open LeanSpec

public section

/- Portable default human interface for spec work.

A company pack may ship its own role skill that boots domain skills. This library
ships the same *job* without company-specific content. -/
skill roleSpecifier := {
  id := ⟨"orchestration.roleSpecifier", by native_decide⟩
  oneLiner := ⟨"Default human interface: route work, preserve Lean authority, and triage discoveries.", by native_decide⟩
  purpose := ⟨"Default human interface for a lean-spec install.", by native_decide⟩
  rules := ⟨#[
    ⟨"Answer routing questions from loaded boot skills.", by native_decide⟩,
    ⟨"Keep Lean-owned DesignUnits and Requirement labels as authority before product work.", by native_decide⟩,
    ⟨"Founders read `Requirement.shall` and `show-snapshot`; agents author `DesignUnit` fields.", by native_decide⟩,
    ⟨"Commission bounded implementation tasks only after boot and gates are clear.", by native_decide⟩,
    ⟨"Triage discoveries into skill updates or a discovery log.", by native_decide⟩
  ], by native_decide⟩
  antipatterns := #[
    ⟨"Loading archived prompts as instructions.", by native_decide⟩,
    ⟨"Treating a checker or an LLM as more authoritative than Lean-owned specs.", by native_decide⟩,
    ⟨"Restating the spec in comments so the model follows prose instead of types.", by native_decide⟩,
    ⟨"Importing a company-specific role skillset into this library.", by native_decide⟩
  ]
}

#guard roleSpecifier.wellFormed

end

end LeanSpec.Workflow
