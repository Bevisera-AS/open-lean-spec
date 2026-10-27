import LeanSpec.Core.Types

/-! Structural problems with a spec. Every rule is one line naming the violation
and the fix; `check` prints them all. Requirement names are Lean names, so they
are unique by construction, and an `@[example]` or `@[evidence]` naming an unknown
requirement is a compile error, so neither is checked here. -/

namespace LeanSpec.Core
open Lean

private def blank (s : String) : Bool := s.all Char.isWhitespace

/-- Values that occur more than once, each listed once. -/
private def dups (l : List String) : List String :=
  (l.filter fun x => (l.filter (· == x)).length > 1).eraseDups

/-- Same input, different output: a contradiction between two examples. -/
private def clashes : List Ex → List String
  | [] => []
  | e :: rest => rest.filterMap (fun f =>
      if e.input == f.input && e.output != f.output then
        some s!"examples '{e.name}' and '{f.name}' have the same input but different outputs"
      else none) ++ clashes rest

private def ReqView.problems (r : ReqView) : List String :=
  (if blank r.label then [s!"requirement '{r.name}' has no docstring"] else []) ++
  (if r.examples.isEmpty && r.witnesses.isEmpty then
    [s!"requirement '{r.name}': needs at least one example or a @[satisfies] theorem"]
  else []) ++
  (r.examples.filter (blank ·.name)).map
    (fun _ => s!"requirement '{r.name}': an example has a blank name") ++
  (match r.post with
   | some post => (r.examples.filter fun e => !post e.input e.output).map
       fun e => s!"requirement '{r.name}': example '{e.name}' violates its own post"
   | none => [])

/-- Everything wrong with a spec; empty means valid. -/
def problems (rs : List ReqView) : List String :=
  let exs := rs.flatMap (·.examples)
  (if rs.isEmpty then ["spec has no requirements"] else []) ++
  (dups (exs.map (·.name))).map (s!"duplicate example name '{·}'") ++
  rs.flatMap ReqView.problems ++ clashes exs

private def e1 := ex "e1" (Json.str "a") (Json.str "x")
private def e2 := ex "e2" (Json.str "b") (Json.str "y")
private def r1 : ReqView := { name := "R1", label := "do x", strength := "must", examples := [e1] }
private def r2 : ReqView := { name := "R2", label := "do y", strength := "must", examples := [e2] }
private def bad (rs : List ReqView) : Bool := !(problems rs).isEmpty

#guard problems [r1, r2] == []
#guard bad []
#guard bad [{ r1 with label := " " }]
#guard bad [{ r1 with examples := [] }]
#guard !bad [{ r1 with examples := [], witnesses := [("t", true)] }]
#guard bad [{ r1 with examples := [ex "" (Json.str "a") (Json.str "x")] }]
#guard bad [r1, { r2 with examples := [e1] }]
#guard bad [{ r1 with examples := [e1, ex "e3" (Json.str "a") (Json.str "z")] }]
#guard bad [r1, { r2 with examples := [ex "e2" (Json.str "a") (Json.str "y")] }]
#guard bad [{ r1 with post := some fun _ o => o == Json.str "y" }]
#guard !bad [{ r1 with post := some fun _ o => o == Json.str "x" }]

end LeanSpec.Core
