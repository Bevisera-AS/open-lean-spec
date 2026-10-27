import Lean.Data.Json

/-! Core types. An example is a program input and the output it must give. A
black-box program is an `IOSig`; `Req.holds` and `IOReq` build requirements over
it, so a requirement about a Python or C++ program is a `Prop` like any other.
`ReqView` is what the `spec` CLI sees at run time; `spec%` (in `LeanSpec.Logic`)
reflects every `@[requirement]` in scope into one. -/

namespace LeanSpec.Core
open Lean

/-- One worked example: run the program on `input`, expect `output`. -/
structure Ex where
  name   : String
  input  : Json
  output : Json
  deriving BEq

/-- `ex "name" (json% {...}) (json% {...})` -/
def ex (name : String) (input output : Json) : Ex := ⟨name, input, output⟩

/-- The design of a black-box program: one JSON value in, one out. -/
structure IOSig where
  run : Json → Json

/-- A requirement built from examples: it holds at each listed point. `test`
evaluates it against the program; a Lean product cannot prove it without
`native_decide`, so its evidence is always the test run. -/
def Req.holds (exs : List Ex) (S : IOSig) : Prop :=
  ∀ e ∈ exs, S.run e.input = e.output

/-- A general requirement over a black-box program: for every input `pre`
accepts, `post` accepts the input and the program's output. Both are decidable,
so `check` evaluates `post` on every example attached to the requirement. -/
def IOReq (pre : Json → Bool) (post : Json → Json → Bool) (S : IOSig) : Prop :=
  ∀ i, pre i = true → post i (S.run i) = true

/-- One requirement as the CLI sees it at run time. -/
structure ReqView where
  name      : String
  /-- The docstring. -/
  label     : String
  /-- `must` or `should`. -/
  strength  : String
  /-- `system` or `user`. -/
  level     : String := "system"
  /-- Examples written in a `Req.holds` body, then those attached by `@[example]`. -/
  examples  : List Ex
  /-- The `post` of an `IOReq` body. -/
  post      : Option (Json → Json → Bool) := none
  /-- `@[satisfies]` theorems, each with whether it quantifies over an input. -/
  witnesses : List (String × Bool) := []
  /-- `@[evidence]` theorems, each with whether it quantifies over an input. -/
  evidence  : List (String × Bool) := []

end LeanSpec.Core
