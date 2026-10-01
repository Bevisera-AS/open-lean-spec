import Lake
open Lake DSL

package «lean-spec» where
  precompileModules := false

/-- Shared string helpers. Sits below the spec types; must not import them. -/
lean_lib LeanUtil where

/-- Shared JSON field helpers. Not the agent kernel. -/
lean_lib LeanJson where

@[default_target]
lean_lib LeanSpec where
  -- One `#[...]` literal. Combining arrays with `++` drops the expected `Glob` type.
  globs := #[
    `LeanSpec,
    `LeanSpec.Types,
    `LeanSpec.Validated,
    `LeanSpec.Determination,
    `LeanSpec.Change,
    `LeanSpec.Design,
    `LeanSpec.Snapshot,
    `LeanSpec.Precedent,
    `LeanSpec.Skillset,
    `LeanSpec.Trace,
    `LeanSpec.Reflection,
    `LeanSpec.Wiki,
    `LeanSpec.WikiStore,
    `LeanSpec.Kb,
    .submodules `LeanSpec.KbAdapter,
    .submodules `LeanSpec.Elab,
    .submodules `LeanSpec.Workflow,
    .submodules `LeanSpec.Codec,
    `LeanSpec.Store,
    `LeanSpec.Emit,
    `LeanSpec.Verification,
    `LeanSpec.Demo.Theme,
    `LeanSpec.Demo.Archive,
    `LeanSpec.Demo.HumanAccept,
    `LeanSpec.Demo.StorePath,
    `LeanSpec.Demo.SkillSyntax,
    `LeanSpec.Demo.SpecSyntax,
    `LeanSpec.Demo.SugarSyntax,
    `LeanSpec.Demo.TargetLang,
    `LeanSpec.Demo.TempConverter,
    `LeanSpec.Demo.Verification
  ]

/-- Prints the demo verification statements. Built by `lake build`. -/
@[default_target]
lean_exe «lean-spec-verification» where
  root := `LeanSpec.Demo.PrintVerification

@[default_target]
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
