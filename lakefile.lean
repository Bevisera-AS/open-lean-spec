import Lake
open Lake DSL

package «lean-spec» where
  precompileModules := false

/- The knowledge core is the sibling package lean-kb since 2026-10-29, so a
knowledge-base consumer can take it without the spec and process layers. Its
modules are `LeanKb.Kb`, `LeanKb.Determination`, `LeanKb.WikiAccess`,
`LeanKb.Validated` and `LeanUtil`; the declaration names are unchanged
(`LeanSpec.Kb.*`, `LeanSpec.WikiAccess`). Only `LeanSpecProcess` and `LeanSpecKb`
import it; the agent library `LeanSpec` never does, which
`LeanSpec/Tests/ImportFirewall.lean` enforces, so a workspace that imports
`LeanSpec` still builds Core, Logic and `Lean` and nothing of lean-kb.
For development against a local checkout: `require «lean-kb» from "../open-lean-kb"`. -/
require «lean-kb» from git "https://gitlab.com/bevisera/open-lean-kb.git" @ "v0.1.0"

/-- Shared JSON field helpers. Not the agent kernel. -/
lean_lib LeanJson where

/-- The spec library an agent imports: `LeanSpec.Core` (examples, the JSON runner,
structural checks, the `spec` CLI; merged from lean-spec-core) and `LeanSpec.Logic`
(requirements as `Prop`s, evidence as theorems). Plain `import` modules; its import
closure is these two and `Lean`, so a bench workspace builds it in seconds.
`LeanSpec/Tests/ImportFirewall.lean` enforces that closure. -/
@[default_target]
lean_lib LeanSpec where
  globs := #[`LeanSpec, `LeanSpec.Core, .submodules `LeanSpec.Core,
    `LeanSpec.Logic.Core, `LeanSpec.Logic.Demo.TempConverter, `LeanSpec.Logic.Demo.Lru,
    .submodules `LeanSpec.Spec]

/-- What carries a non-standard axiom on purpose: the Theme demo's `@[sign_off]`
axiom (a person's judgement is an axiom by design, named in the statement) and the
Logic tests' `sorry` and custom axioms, which exercise the gap rules. Not a default
target, so `lake check --paranoid` covers exactly what rests on the standard axioms;
`lake build LeanSpecSigned` and `lake test` still build and check these. -/
lean_lib LeanSpecSigned where
  globs := #[`LeanSpec.Logic.Demo.Theme, `LeanSpec.Logic.Tests]

/-- The process layer: process skills and skillsets, the `spec-change` workflow
(propose / apply / archive / reflect, human gates, roles), traces and reflections.
Module system. What a knowledge-base consumer imports beside `LeanSpec.Logic`.
Rests on lean-kb's `LeanSpec.Validated` and `LeanUtil`. -/
@[default_target]
lean_lib LeanSpecProcess where
  -- One `#[...]` literal. Combining arrays with `++` drops the expected `Glob` type.
  globs := #[
    `LeanSpecProcess,
    `LeanSpec.Codec.Applicative,
    `LeanSpec.ProcessSkill,
    `LeanSpec.Skillset,
    `LeanSpec.Trace,
    `LeanSpec.Classification,
    `LeanSpec.Reflection,
    `LeanSpec.Finding,
    .submodules `LeanSpec.Elab,
    .submodules `LeanSpec.Workflow,
    `LeanSpec.Demo.SkillSyntax,
    -- Test modules, so `lake check` exports and re-checks them too. The driver
    -- `LeanSpec.Tests` defines `main` and stays out.
    `LeanSpec.Tests.ImportFirewall,
    `LeanSpec.Tests.Validated,
    `LeanSpec.Tests.ProcessSkill,
    `LeanSpec.Tests.Skillset,
    `LeanSpec.Tests.Catalog
  ]

/-- lean-spec's instance of lean-kb's core: the agent `Wiki` (agent-experience
memory with run provenance), its store and codec, and `KbAdapter`, which proves the
`Wiki` operations correspond to the generic ones. `LeanSpecKb` re-exports the core
(`Kb`, `Determination`, `WikiAccess`) so `import LeanSpecKb` is unchanged. Depends
on `LeanSpecProcess` (a `Wiki` holds `Reflection`s); nothing below depends on it. -/
@[default_target]
lean_lib LeanSpecKb where
  globs := #[
    `LeanSpecKb,
    `LeanSpec.Wiki,
    `LeanSpec.WikiStore,
    `LeanSpec.Codec.Reflection,
    .submodules `LeanSpec.KbAdapter,
    `LeanSpec.Tests.KernelPredicates
  ]

/- The executables are not default targets. `lake check` exports every default
target into one environment, and each executable root defines `main`, so two of
them cannot be imported together. Build them by name:
`lake build LeanSpecSigned lean-spec lean-spec-logic-statement`. -/

/-- Prints the demo requirement statements. -/
lean_exe «lean-spec-logic-statement» where
  root := `LeanSpec.Demo.PrintLogicStatement

lean_exe «lean-spec» where
  root := `LeanSpec.Query

lean_exe «lean-spec-tests» where
  root := `LeanSpec.Tests

/-- Spec tests only. -/
@[test_driver]
script test do
  let code ← exe `«lean-spec-tests»
  if code != 0 then return code
  return 0
