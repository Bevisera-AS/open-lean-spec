module

public import LeanSpec.Elab.Sugar
public import LeanSpec.Types
public import LeanSpec.Design
public meta import LeanSpec.Elab.Sugar
public meta import LeanSpec.Types
public meta import LeanSpec.Design

/-!
# Temperature converter demo

A worked example authored the way this library prescribes:

- The requirement is written with the human-facing `requirement ... where`
  sugar (see `LeanSpec/Elab/Sugar.lean`), which desugars to a proof-carrying
  `Requirement` and registers it via the `spec` command.
- The implementation is real Lean 4: exact `Rat`-valued conversions with a
  round-trip theorem and `#guard` checks, so the `executable` checks name
  checkers that actually exist (mirroring `LeanSpec/Demo/Theme.lean`).
- The `DesignUnit` declares `surface := .native` and `target := .lean4`.
  Temperature conversion is not a web feature, so the native surface applies;
  the target policy (`TargetLang.allowedFor .native .lean4`) allows Lean 4 and
  in fact prefers it (`TargetLang.preference .lean4 = 0`).
-/

namespace LeanSpec.Demo.TempConverter

open LeanSpec

public section

/-- Celsius to Fahrenheit: `F = C * 9/5 + 32`. Exact rational arithmetic so the
inverse round-trips without floating-point drift. -/
public def celsiusToFahrenheit (c : Rat) : Rat := c * 9 / 5 + 32

/-- Fahrenheit to Celsius: `C = (F - 32) * 5/9`. -/
public def fahrenheitToCelsius (f : Rat) : Rat := (f - 32) * 5 / 9

/-- Checker: converting to Fahrenheit and back yields the original Celsius. -/
public def roundTripCheck (c : Rat) : Bool :=
  fahrenheitToCelsius (celsiusToFahrenheit c) == c

/-- Checker: known reference points convert correctly (freezing, boiling, and
the point where both scales agree). -/
public def referencePointsCheck : Bool :=
  celsiusToFahrenheit 0 == 32 &&
    celsiusToFahrenheit 100 == 212 &&
    celsiusToFahrenheit (-40) == (-40) &&
    fahrenheitToCelsius 32 == 0 &&
    fahrenheitToCelsius 212 == 100

/-- Kernel-checked evidence behind the `executable` round-trip scenario: the
`roundTripCheck` checker holds at representative points (body temperature,
freezing, absolute zero, and a fractional value). Concrete `Rat` goals reduce,
so no external algebra tactic (`ring`) is needed. -/
public theorem roundTripCheck_holds :
    roundTripCheck 37 = true ∧
      roundTripCheck 0 = true ∧
      roundTripCheck (-273) = true ∧
      roundTripCheck (1 / 3) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The named reference points convert correctly (kernel-checked). -/
public theorem referencePointsCheck_holds : referencePointsCheck = true := by
  native_decide

-- ─── Requirement via the library's sugar ─────────────────────────────────────

requirement temperatureConverter where
  id    "tool.temperature-converter"
  shall "Convert temperatures between Celsius and Fahrenheit in both directions"
  strength must

  scenario "celsius to fahrenheit at known points"
    given "a temperature expressed in degrees Celsius"
    when  "the user converts it to Fahrenheit"
    then_ "the result equals C times 9/5 plus 32 (0C to 32F, 100C to 212F)"
    check executable

  scenario "fahrenheit to celsius at known points"
    given "a temperature expressed in degrees Fahrenheit"
    when  "the user converts it to Celsius"
    then_ "the result equals (F minus 32) times 5/9 (32F to 0C, 212F to 100C)"
    check executable

  scenario "conversion round-trips"
    given "any temperature in Celsius"
    when  "it is converted to Fahrenheit and back to Celsius"
    then_ "the original Celsius value is recovered exactly"
    check executable

-- The sugar produces the same proof-carrying Requirement as hand-written literals:
#guard temperatureConverter.wellFormed
#guard !temperatureConverter.hasDeferredChecks
#guard temperatureConverter.id.value == "tool.temperature-converter"
#guard temperatureConverter.strength == .must
#guard temperatureConverter.scenarios.size == 3

-- It registers via the underlying `spec` command:
#guard (registeredSpecs%.map (fun p => p.2.id.value)).toList.contains "tool.temperature-converter"

-- ─── Executable checks named by the scenarios ────────────────────────────────

#guard referencePointsCheck
#guard roundTripCheck 37
#guard roundTripCheck 0
#guard roundTripCheck (-273)
#guard roundTripCheck (1 / 3)

-- ─── Design unit: native surface, Lean 4 target ──────────────────────────────

/-- Native Lean 4 implementation artifact. The target/surface pairing is
discharged by the default `native_decide` proof obligation; a web/Rust or
native/TypeScript pairing could not be constructed.

Note: `id := ...` below uses the plain field name — no escaping needed. This is
the regression check that the sugar's field tokens no longer leak into the
global keyword set. -/
public def temperatureConverterDesign : DesignUnit := {
  id := temperatureConverter.id
  surface := .native
  target := .lean4
  interfaces := ⟨#[
    ⟨"celsiusToFahrenheit", by native_decide⟩,
    ⟨"fahrenheitToCelsius", by native_decide⟩
  ], by native_decide⟩
  functions := #[
    ⟨"celsiusToFahrenheit", by native_decide⟩,
    ⟨"fahrenheitToCelsius", by native_decide⟩,
    ⟨"roundTripCheck", by native_decide⟩,
    ⟨"referencePointsCheck", by native_decide⟩
  ]
  tests := ⟨#[
    ⟨"referencePointsCheck", by native_decide⟩,
    ⟨"roundTripCheck", by native_decide⟩
  ], by native_decide⟩
  theorems := #[
    ⟨"referencePointsCheck_holds", by native_decide⟩,
    ⟨"roundTripCheck_holds", by native_decide⟩
  ]
}

#guard temperatureConverterDesign.wellFormed
#guard temperatureConverterDesign.id == temperatureConverter.id
#guard temperatureConverterDesign.surface == .native
#guard temperatureConverterDesign.target == .lean4

end

end LeanSpec.Demo.TempConverter
