module

public import LeanSpec.Validated
public import LeanSpec.Codec.Applicative
public import LeanSpec.ProcessSkill
public import LeanSpec.Skillset
public import LeanSpec.Elab.Skill
public import LeanSpec.Trace
public import LeanSpec.Classification
public import LeanSpec.Reflection
public import LeanSpec.Finding
public import LeanSpec.Workflow.BootClosure
public import LeanSpec.Workflow.Catalog

/-!
Root of the `LeanSpecProcess` library: process skills and skillsets, the
`spec-change` workflow (propose, apply, archive, reflect, human gates, roles),
agent traces and reflections. Company-specific roles stay in a downstream pack.
Lake names a library's native initializer after this module, so a downstream
package that precompiles its modules can load the library as a plugin.
-/
