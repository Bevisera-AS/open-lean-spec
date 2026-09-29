module

public import LeanSpec.Skillset
public import LeanSpec.Elab.Skill
public import LeanSpec.Workflow.HumanGates
public import LeanSpec.Workflow.SkillExec
public import LeanSpec.Workflow.Reflect
public import LeanSpec.Workflow.Propose
public import LeanSpec.Workflow.ApplyArchive
public import LeanSpec.Workflow.RoleSpecifier
public meta import LeanSpec.Skillset
public meta import LeanSpec.Elab.Skill
public meta import LeanSpec.Workflow.HumanGates
public meta import LeanSpec.Workflow.SkillExec
public meta import LeanSpec.Workflow.Reflect
public meta import LeanSpec.Workflow.Propose
public meta import LeanSpec.Workflow.ApplyArchive
public meta import LeanSpec.Workflow.RoleSpecifier

namespace LeanSpec.Workflow

open LeanSpec

public section

/-- Portable skillset. Company-specific role skillsets stay in a downstream pack. -/
public def specChange : Skillset := {
  id := ⟨"skillset.specChange", by native_decide⟩
  pasteToken := ⟨"spec-change", by native_decide⟩
  mission := ⟨"Specify and change behaviour as Lean DesignUnits with short Requirement labels, then apply and archive under human gates.", by native_decide⟩
  roleSkill := roleSpecifier.id
  boot := ⟨#[
    humanGates.id,
    skillExec.id,
    reflect.id,
    proposeChange.id,
    applyChange.id,
    archiveChange.id,
    roleSpecifier.id
  ], by native_decide⟩
  reads := #[⟨"README.md", by native_decide⟩]
  roleInBoot := by native_decide
}

public def catalog : Catalog := {
  skills := #[
    humanGates,
    skillExec,
    reflect,
    proposeChange,
    applyChange,
    archiveChange,
    roleSpecifier
  ]
  skillsets := #[specChange]
  uniqueSkills := by native_decide
  uniqueSkillsets := by native_decide
  uniqueTokens := by native_decide
  registered := by native_decide
  requiresRegistered := by native_decide
  requiresAcyclic := by native_decide
}

#guard catalog.wellFormed
#guard (catalog.findSkillset? "spec-change").isSome
#guard (catalog.findSkillset? "company-pack.role").isNone
#guard
  sameIdSet (catalog.skills.map (·.id.value)) (registeredSkills%.map (·.2.id.value))
#guard !(catalog.skills.map (·.id.value)).contains "demo.ping"

end

end LeanSpec.Workflow
