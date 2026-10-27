import LeanSpec.Logic.Core

/-!
# Temperature converter, as logic

Port of the 1.x prose demo. 1.x said the conversion round-trips for
"any temperature" and proved it at four points. Here the round trip is a `Prop`
over every `Rat`, and the reference points are examples.
-/

namespace LeanSpec.Logic.Demo.TempConverter

open LeanSpec.Logic

/-- The design: two conversions on exact rationals. -/
structure Sig where
  toF : Rat → Rat
  toC : Rat → Rat

/-- Celsius to Fahrenheit is `C * 9/5 + 32`. -/
@[requirement must]
def fahrenheitFormula (S : Sig) : Prop :=
  ∀ c, S.toF c = c * 9 / 5 + 32

/-- Fahrenheit to Celsius is `(F - 32) * 5/9`. -/
@[requirement must]
def celsiusFormula (S : Sig) : Prop :=
  ∀ f, S.toC f = (f - 32) * 5 / 9

/-- Converting to Fahrenheit and back gives the original value, for every value. -/
@[requirement must]
def roundTrips (S : Sig) : Prop :=
  ∀ c, S.toC (S.toF c) = c

-- ─── Implementation ──────────────────────────────────────────────────────────

def celsiusToFahrenheit (c : Rat) : Rat := c * 9 / 5 + 32
def fahrenheitToCelsius (f : Rat) : Rat := (f - 32) * 5 / 9

/-- These Lean functions are the product, so proofs about `impl` are about it. -/
@[shipped]
def impl : Sig := ⟨celsiusToFahrenheit, fahrenheitToCelsius⟩

@[satisfies] theorem impl_fahrenheitFormula : fahrenheitFormula impl := fun _ => rfl

@[satisfies] theorem impl_celsiusFormula : celsiusFormula impl := fun _ => rfl

@[satisfies] theorem impl_roundTrips : roundTrips impl := by
  intro c
  simp only [impl, celsiusToFahrenheit, fahrenheitToCelsius]
  grind

-- ─── Counter-models ──────────────────────────────────────────────────────────

/-- Directions swapped. -/
def swapped : Sig := ⟨fahrenheitToCelsius, celsiusToFahrenheit⟩

/-- Rounds Fahrenheit to a whole degree, as a UI field might. -/
def rounding : Sig := ⟨fun c => (celsiusToFahrenheit c).floor, fahrenheitToCelsius⟩

@[refutes] theorem swapped_fails_fahrenheit : ¬ fahrenheitFormula swapped := by
  intro h; have := h 0; revert this; decide +kernel

@[refutes] theorem swapped_fails_celsius : ¬ celsiusFormula swapped := by
  intro h; have := h 0; revert this; decide +kernel

@[refutes] theorem rounding_fails : ¬ roundTrips rounding := by
  intro h; have := h (1 / 3); revert this; decide +kernel

-- ─── Scenarios are examples ──────────────────────────────────────────────────

example : impl.toF 0 = 32 := by decide +kernel
example : impl.toF 100 = 212 := by decide +kernel
example : impl.toF (-40) = -40 := by decide +kernel
example : impl.toC 212 = 100 := by decide +kernel

spec_statement statement for LeanSpec.Logic.Demo.TempConverter

#guard statement.verified
#guard statement.rows.all (·.gaps.isEmpty)
#guard statement.rows.all (·.status == "proved")

end LeanSpec.Logic.Demo.TempConverter
