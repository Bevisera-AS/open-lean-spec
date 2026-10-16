module

public import LeanSpec.Elab.Spec
public import LeanSpec.Types
public meta import LeanSpec.Elab.Spec
public meta import LeanSpec.Types

namespace LeanSpec.Demo.SpecSyntax

open LeanSpec

spec demoRequirement := {
  id := ⟨"demo.requirement", by decide +kernel⟩
  shall := ⟨"The spec command elaborates a Requirement.", by decide +kernel⟩
  scenarios := ⟨#[{
    name := ⟨"command elaborates", by decide +kernel⟩
    whenText := ⟨"a requirement is declared with spec", by decide +kernel⟩
    thenText := ⟨"it inhabits Requirement and is registered", by decide +kernel⟩
    check := .executable
  }], by decide +kernel⟩
}

#guard demoRequirement.wellFormed
#guard !demoRequirement.hasDeferredChecks
#guard demoRequirement.id.value == "demo.requirement"
#guard (registeredSpecs%.map (fun p => p.2.id.value)).toList.contains "demo.requirement"
#guard !requirementIdTaken (registeredSpecs%.map (·.2)) "demo.missing"

end LeanSpec.Demo.SpecSyntax
