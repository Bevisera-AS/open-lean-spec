module

public import LeanSpec.Elab.Spec
public import LeanSpec.Types
public meta import LeanSpec.Elab.Spec
public meta import LeanSpec.Types

namespace LeanSpec.Demo.SpecSyntax

open LeanSpec

spec demoRequirement := {
  id := ⟨"demo.requirement", by native_decide⟩
  shall := ⟨"The spec command elaborates a Requirement.", by native_decide⟩
  scenarios := ⟨#[{
    name := ⟨"command elaborates", by native_decide⟩
    whenText := ⟨"a requirement is declared with spec", by native_decide⟩
    thenText := ⟨"it inhabits Requirement and is registered", by native_decide⟩
    check := .executable
  }], by native_decide⟩
}

#guard demoRequirement.wellFormed
#guard !demoRequirement.hasDeferredChecks
#guard demoRequirement.id.value == "demo.requirement"
#guard (registeredSpecs%.map (fun p => p.2.id.value)).toList.contains "demo.requirement"
#guard !requirementIdTaken (registeredSpecs%.map (·.2)) "demo.missing"

end LeanSpec.Demo.SpecSyntax
