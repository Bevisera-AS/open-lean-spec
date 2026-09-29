module

public import LeanSpec.Design
public meta import LeanSpec.Design

/-!
# Target-language policy demo

Shows the closed set of strongly-typed implementation targets and the
web/native pairing rule. Usage examples only; no solution content.

Policy:
- web    => TypeScript
- native => Lean 4 (preferred), Scala, Rust, or Java-via-Strata
-/

namespace LeanSpec.Demo.TargetLang

open LeanSpec

-- A web design unit must target TypeScript. The proof obligation is discharged
-- by `native_decide`; a wrong pairing would not compile.
def webDashboard : DesignUnit := {
  id := ⟨"page.dashboard", by native_decide⟩
  surface := .web
  target := .typescript
  interfaces := ⟨#[⟨"DashboardProps", by native_decide⟩], by native_decide⟩
  tests := ⟨#[⟨"rendersLatestYear", by native_decide⟩], by native_decide⟩
}

#guard webDashboard.wellFormed
#guard webDashboard.surface == .web
#guard webDashboard.target == .typescript

-- A native design unit prefers Lean 4.
def nativeCore : DesignUnit := {
  id := ⟨"core.snapshot", by native_decide⟩
  surface := .native
  target := .lean4
  interfaces := ⟨#[⟨"SpecSnapshot", by native_decide⟩], by native_decide⟩
  tests := ⟨#[⟨"archiveCheck", by native_decide⟩], by native_decide⟩
}

#guard nativeCore.wellFormed
#guard nativeCore.target == .lean4

-- Rust is allowed on native (the type-checker accepts the proof obligation).
def nativeRust : DesignUnit := {
  id := ⟨"core.parser", by native_decide⟩
  surface := .native
  target := .rust
  interfaces := ⟨#[⟨"Parser", by native_decide⟩], by native_decide⟩
  tests := ⟨#[⟨"parsesValidInput", by native_decide⟩], by native_decide⟩
}

#guard nativeRust.wellFormed
#guard nativeRust.target == .rust

/-
The following would NOT compile — a web unit cannot target Rust, because
`targetAllowed : AllowedTarget .web .rust` is `false = true`, which
`native_decide` cannot prove:

  def bad : DesignUnit := {
    id := ⟨"page.bad", by native_decide⟩
    surface := .web
    target := .rust                       -- rejected by construction
    interfaces := ⟨#[⟨"X", by native_decide⟩], by native_decide⟩
    tests := ⟨#[⟨"t", by native_decide⟩], by native_decide⟩
  }
-/

-- The policy predicate, exercised directly:
#guard TargetLang.allowedFor .web .typescript
#guard !TargetLang.allowedFor .web .rust
#guard !TargetLang.allowedFor .web .lean4
#guard TargetLang.allowedFor .native .lean4
#guard TargetLang.allowedFor .native .scala
#guard TargetLang.allowedFor .native .rust
#guard TargetLang.allowedFor .native .javaViaStrata
#guard !TargetLang.allowedFor .native .typescript

-- Preference ordering (advisory): Lean 4 < Scala = Rust < Java-via-Strata.
#guard TargetLang.preference .lean4 < TargetLang.preference .scala
#guard TargetLang.preference .rust < TargetLang.preference .javaViaStrata

end LeanSpec.Demo.TargetLang
