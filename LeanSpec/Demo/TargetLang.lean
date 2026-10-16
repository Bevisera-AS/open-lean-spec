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
-- by `decide +kernel`; a wrong pairing would not compile.
def webDashboard : DesignUnit := {
  id := ⟨"page.dashboard", by decide +kernel⟩
  surface := .web
  target := .typescript
  interfaces := ⟨#[⟨"DashboardProps", by decide +kernel⟩], by decide +kernel⟩
  tests := ⟨#[⟨"rendersLatestYear", by decide +kernel⟩], by decide +kernel⟩
}

#guard webDashboard.wellFormed
#guard webDashboard.surface == .web
#guard webDashboard.target == .typescript

-- A native design unit prefers Lean 4.
def nativeCore : DesignUnit := {
  id := ⟨"core.snapshot", by decide +kernel⟩
  surface := .native
  target := .lean4
  interfaces := ⟨#[⟨"SpecSnapshot", by decide +kernel⟩], by decide +kernel⟩
  tests := ⟨#[⟨"archiveCheck", by decide +kernel⟩], by decide +kernel⟩
}

#guard nativeCore.wellFormed
#guard nativeCore.target == .lean4

-- Rust is allowed on native (the type-checker accepts the proof obligation).
def nativeRust : DesignUnit := {
  id := ⟨"core.parser", by decide +kernel⟩
  surface := .native
  target := .rust
  interfaces := ⟨#[⟨"Parser", by decide +kernel⟩], by decide +kernel⟩
  tests := ⟨#[⟨"parsesValidInput", by decide +kernel⟩], by decide +kernel⟩
}

#guard nativeRust.wellFormed
#guard nativeRust.target == .rust

/-
The following would NOT compile — a web unit cannot target Rust, because
`targetAllowed : AllowedTarget .web .rust` is `false = true`, which
`decide +kernel` cannot prove:

  def bad : DesignUnit := {
    id := ⟨"page.bad", by decide +kernel⟩
    surface := .web
    target := .rust                       -- rejected by construction
    interfaces := ⟨#[⟨"X", by decide +kernel⟩], by decide +kernel⟩
    tests := ⟨#[⟨"t", by decide +kernel⟩], by decide +kernel⟩
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
