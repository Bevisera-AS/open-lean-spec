module

public import LeanSpec.Skillset
public import LeanSpec.Elab.Skill
public import LeanSpec.Workflow.HumanGates
public import LeanSpec.Workflow.SkillExec
public import LeanSpec.Workflow.Reflect
public import LeanSpec.Workflow.Propose
public import LeanSpec.Workflow.ApplyArchive
public import LeanSpec.Workflow.RoleSpecifier
public import LeanSpec.Workflow.Roles
public meta import LeanSpec.Skillset
public meta import LeanSpec.Elab.Skill
public meta import LeanSpec.Workflow.HumanGates
public meta import LeanSpec.Workflow.SkillExec
public meta import LeanSpec.Workflow.Reflect
public meta import LeanSpec.Workflow.Propose
public meta import LeanSpec.Workflow.ApplyArchive
public meta import LeanSpec.Workflow.RoleSpecifier
public meta import LeanSpec.Workflow.Roles

namespace LeanSpec.Workflow

open LeanSpec

public section

/-- Portable skillset: the whole spec-change loop for a person steering it.
Company-specific role skillsets stay in a downstream pack. -/
public def specChange : Skillset := {
  id := ⟨"skillset.specChange", by decide +kernel⟩
  pasteToken := ⟨"spec-change", by decide +kernel⟩
  mission := ⟨"Specify behaviour as Lean requirements with examples and Props, build and review under referee and human gates, then sign off.", by decide +kernel⟩
  roleSkill := roleSpecifier.id
  boot := ⟨#[
    humanGates.id,
    refereeGates.id,
    skillExec.id,
    reflect.id,
    proposeChange.id,
    applyChange.id,
    archiveChange.id,
    roleSpecifier.id
  ], by decide +kernel⟩
  reads := #[⟨"README.md", by decide +kernel⟩]
  roleInBoot := by decide +kernel
}

/-- The builder's skillset: what the agent in a bench workspace boots. -/
public def specBuilder : Skillset := {
  id := ⟨"skillset.specBuilder", by decide +kernel⟩
  pasteToken := ⟨"spec-builder", by decide +kernel⟩
  mission := ⟨"Write Spec.lean and the program in one workspace until check, test and report pass.", by decide +kernel⟩
  roleSkill := roleBuilder.id
  boot := ⟨#[
    humanGates.id,
    refereeGates.id,
    proposeChange.id,
    applyChange.id,
    roleBuilder.id
  ], by decide +kernel⟩
  roleInBoot := by decide +kernel
}

/-- The reviewer's skillset: accept proposals, audit runs, write findings. -/
public def specReviewer : Skillset := {
  id := ⟨"skillset.specReviewer", by decide +kernel⟩
  pasteToken := ⟨"spec-reviewer", by decide +kernel⟩
  mission := ⟨"Judge the spec against the task and the program against the spec; record typed findings.", by decide +kernel⟩
  roleSkill := roleReviewer.id
  boot := ⟨#[
    humanGates.id,
    refereeGates.id,
    reflect.id,
    archiveChange.id,
    roleReviewer.id
  ], by decide +kernel⟩
  roleInBoot := by decide +kernel
}

public def catalog : Catalog := {
  skills := #[
    humanGates,
    refereeGates,
    skillExec,
    reflect,
    proposeChange,
    applyChange,
    archiveChange,
    roleSpecifier,
    roleBuilder,
    roleReviewer
  ]
  skillsets := #[specChange, specBuilder, specReviewer]
  uniqueSkills := by decide +kernel
  uniqueSkillsets := by decide +kernel
  uniqueTokens := by decide +kernel
  registered := by decide +kernel
  requiresRegistered := by decide +kernel
  requiresAcyclic := by decide +kernel
}

#guard catalog.wellFormed
#guard (catalog.findSkillset? "spec-change").isSome
#guard (catalog.findSkillset? "spec-builder").isSome
#guard (catalog.findSkillset? "spec-reviewer").isSome
#guard (catalog.findSkillset? "company-pack.role").isNone
#guard
  sameIdSet (catalog.skills.map (·.id.value)) (registeredSkills%.map (·.2.id.value))
#guard !(catalog.skills.map (·.id.value)).contains "demo.ping"

end

end LeanSpec.Workflow
