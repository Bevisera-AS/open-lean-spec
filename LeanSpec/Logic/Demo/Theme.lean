import LeanSpec.Logic.Core

/-!
# Theme, as logic

Port of `LeanSpec.Demo.Theme`. The 1.x prose said "switch between light and dark
themes, defaulting to system preference" and the archived version added "the choice
persists across restart". Each clause is now a `Prop`; the 1.x `toggleDark` is kept
as a counter-model.
-/

namespace LeanSpec.Logic.Demo.Theme

open LeanSpec.Logic

inductive Mode where
  | light
  | dark
  deriving DecidableEq, Repr

structure Palette where
  fg : Nat
  bg : Nat
  deriving DecidableEq, Repr

/-- The design: what any implementation exposes. -/
structure Sig where
  State   : Type
  Stored  : Type
  initial : (system : Mode) → State
  mode    : State → Mode
  toggle  : State → State
  save    : State → Stored
  restore : Stored → State
  palette : Mode → Palette

/-- From light, the toggle gives dark. -/
@[requirement must]
def switchesToDark (S : Sig) : Prop :=
  ∀ s, S.mode s = .light → S.mode (S.toggle s) = .dark

/-- From dark, the toggle gives light. -/
@[requirement must]
def switchesToLight (S : Sig) : Prop :=
  ∀ s, S.mode s = .dark → S.mode (S.toggle s) = .light

/-- A fresh start follows the system preference. -/
@[requirement must]
def defaultsToSystem (S : Sig) : Prop :=
  ∀ sys, S.mode (S.initial sys) = sys

/-- The chosen mode survives save and restore. -/
@[requirement must]
def persistsAcrossRestart (S : Sig) : Prop :=
  ∀ s, S.mode (S.restore (S.save s)) = S.mode s

/-- Whether a palette reads clearly. The kernel cannot decide this: it is a judgement. -/
opaque Readable : Palette → Prop

/-- The dark palette reads clearly. -/
@[requirement should]
def darkReadable (S : Sig) : Prop :=
  Readable (S.palette .dark)

-- ─── Implementation ──────────────────────────────────────────────────────────

def flip : Mode → Mode
  | .light => .dark
  | .dark  => .light

def impl : Sig where
  State   := Mode
  Stored  := Mode
  initial := id
  mode    := id
  toggle  := flip
  save    := id
  restore := id
  palette
    | .light => ⟨0, 255⟩
    | .dark  => ⟨230, 18⟩

@[satisfies] theorem impl_switchesToDark : switchesToDark impl := by
  intro s h; cases s <;> simp_all [impl, flip]

@[satisfies] theorem impl_switchesToLight : switchesToLight impl := by
  intro s h; cases s <;> simp_all [impl, flip]

@[satisfies] theorem impl_defaultsToSystem : defaultsToSystem impl := fun _ => rfl

@[satisfies] theorem impl_persistsAcrossRestart : persistsAcrossRestart impl := fun _ => rfl

/-- A person looked at the dark palette and judged it readable. The digest pins
the `Prop` they judged; if `darkReadable` changes, this row turns `stale`. -/
@[sign_off reviewer "fnv1a64:536f0f37ef468acf"]
axiom darkReadable_reviewed : SignOff darkReadable impl

@[satisfies] theorem impl_darkReadable : darkReadable impl := darkReadable_reviewed.holds

-- ─── Counter-models ──────────────────────────────────────────────────────────

/-- The 1.x implementation: `toggleDark` always returns dark. -/
def constDark : Sig := { impl with toggle := fun _ => .dark }

/-- Ignores the toggle. -/
def frozen : Sig := { impl with toggle := id }

/-- Always starts light. -/
def alwaysLight : Sig := { impl with initial := fun _ => .light }

/-- Forgets the choice on restart. -/
def forgetful : Sig := { impl with restore := fun _ => .light }

@[refutes] theorem constDark_fails : ¬ switchesToLight constDark := by
  intro h; cases h .dark rfl

@[refutes] theorem frozen_fails : ¬ switchesToDark frozen := by
  intro h; cases h .light rfl

@[refutes] theorem alwaysLight_fails : ¬ defaultsToSystem alwaysLight := by
  intro h; cases h .dark

@[refutes] theorem forgetful_fails : ¬ persistsAcrossRestart forgetful := by
  intro h; cases h .dark

-- ─── Scenarios are examples, not requirements ────────────────────────────────

example : impl.mode (impl.toggle (impl.initial .light)) = .dark := rfl

spec_statement statement for LeanSpec.Logic.Demo.Theme

-- The UI here is a model of an app, not its code: four rows are `model`.
#guard statement.verified
#guard statement.rows.size == 5
#guard statement.statusOf ``switchesToLight == "model"
#guard statement.gapsOf ``persistsAcrossRestart == #[.modelOnly]
#guard statement.statusOf ``darkReadable == "signed"
#guard statement.gapsOf ``darkReadable == #[.signedOff `reviewer, .modelOnly, .vacuous]

end LeanSpec.Logic.Demo.Theme
