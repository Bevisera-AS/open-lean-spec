module

public import LeanSpec.Elab.Verification
public import LeanSpec.Demo.Archive
public meta import LeanSpec.Elab.Verification
public meta import LeanSpec.Demo.Archive

namespace LeanSpec.Demo.Verification

open LeanSpec
open LeanSpec.Demo.Archive

-- Theme snapshot: one executable scenario, witnessed by toggleDarkCheck_of_light.
-- The proof is kernel-checked: only the standard axioms, no `native_decide`.
verification_statement themeVerified for initialSnapshot

public def themeVerifiedSource : String := emitVerificationStatement themeVerified

#guard themeVerified.checkable
#guard themeVerified.certifies themeVerifiedSource
#guard themeVerified.citationsOk
#guard themeVerified.disjoint
#guard themeVerified.openObligations.isEmpty
#guard themeVerified.coversSuffix "theme.selection" "toggleDarkCheck_of_light"
#guard !(themeVerified.axioms.any (· == "sorryAx"))
#guard !themeVerified.axioms.isEmpty
#guard themeVerified.extraAxioms.isEmpty

public def archivedSnapshot : SpecSnapshot :=
  match archived? with
  | .ok snap => snap
  | .error _ => initialSnapshot

-- Archived theme: the kernel theorem still covers theme.selection.
-- The new deferred scenarios stay outside the mark.
verification_statement archivedVerified for archivedSnapshot

public def archivedVerifiedSource : String := emitVerificationStatement archivedVerified

#guard archivedVerified.checkable
#guard archivedVerified.certifies archivedVerifiedSource
#guard archivedVerified.citationsOk
#guard archivedVerified.disjoint
#guard archivedVerified.coversSuffix "theme.selection" "toggleDarkCheck_of_light"
#guard archivedVerified.hasOpen "theme.contrast" .deferred "contrast stated"
#guard archivedVerified.hasOpen "theme.selection" .deferred "persist across restart"
#guard !archivedVerified.hasOpen "theme.selection" .unwitnessedExecutable "toggle dark"
#guard !(archivedVerified.axioms.any (· == "sorryAx"))
#guard archivedVerifiedSource.contains "mark lean-spec-verified"
#guard themeVerified.specDigest != archivedVerified.specDigest
#guard themeVerified.toolchain == Lean.versionString
#guard archivedVerifiedSource.contains "schema lean-spec.verification/1"

end LeanSpec.Demo.Verification
