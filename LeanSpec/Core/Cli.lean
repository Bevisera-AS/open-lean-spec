import LeanSpec.Logic.Core
import LeanSpec.Core.Check
import LeanSpec.Core.Run

/-! The `spec` CLI. A workspace defines
`def main (args : List String) : IO UInt32 := LeanSpec.Core.cli spec% statement% args`;
`spec%` and `statement%` reflect every `@[requirement]` the module imports. -/

namespace LeanSpec.Core
open Lean LeanSpec.Logic

/-- Agent manual printed by `help`. -/
def helpText : String := "\
Spec.lean (import LeanSpec; open LeanSpec.Core Lean) states the requirements. Each is a def
marked @[requirement must] (or should) of type IOSig -> Prop; its docstring is the label.
  import LeanSpec
  open LeanSpec.Core Lean

  /-- add two numbers -/
  @[requirement must] def add : IOSig → Prop := Req.holds [
    ex \"basic\" (json% {\"op\": \"add\", \"xs\": [1, 2]}) (json% {\"result\": 3}),
    ex \"neg\" (json% {\"op\": \"add\", \"xs\": [-1, 1]}) (json% {\"result\": 0})]

  /-- unknown op is an error -/
  @[requirement must] def unknownOp : IOSig → Prop := Req.holds [
    ex \"bad\" (json% {\"op\": \"pow\", \"xs\": []}) (json% {\"error\": \"unknown op\", \"detail\": null})]
An example is the requirement at one point: run the program on input, expect output.
Another example for a requirement: @[example add] def add_big : Ex := ex \"big\" (json% ...) (json% ...)
A requirement over every input: IOReq pre post with pre : Json → Bool and post : Json → Json → Bool;
  `check` runs post on each of its examples. Example, every op gets a result or an error:
  IOReq (fun i => (i.getObjVal? \"op\").isOk) (fun _ o => (o.getObjVal? \"result\").isOk || (o.getObjVal? \"error\").isOk)
json%: objects {..}, arrays [..], strings, numbers (-1, 2.5), true/false/null, nesting.
  A Lean value goes in as $x (x : String/Nat/Int/Json...), e.g. json% {\"n\": $n}.
The program reads ONE JSON value on stdin and writes ONE JSON value on stdout.
Examples ARE the tests: write no other tests. Object key order is ignored.
Proofs, Lean target only (Python/C++ skip this; examples are their only tests).
Prog.lean (import LeanSpec and Spec) proves theorems about its functions, each tagged with the
requirements it supports, by name:
  import LeanSpec
  import Spec
  def addInts (a b : Int) : Int := a + b
  @[evidence add] theorem addInts_comm (a b : Int) : addInts a b = addInts b a := by unfold addInts; omega
  @[evidence add unknownOp] takes several. Theorems with ∀/binders over inputs count as general;
  closed statements and ∃ count as examples. No sorry. An unknown name is a compile error.
  `check` prints evidence.<req>.general/examples.
Closing a row by proof (Lean target), when the product is itself a Lean value of the signature:
  structure Sig where f : Nat → Nat
  /-- f fixes zero -/
  @[requirement must] def fixesZero : Sig → Prop := fun S => S.f 0 = 0
  @[shipped] def impl : Sig := ⟨id⟩                       -- the product itself, not a model of it
  @[satisfies] theorem impl_ok : fixesZero impl := rfl     -- closes the row; the requirement is read off the type
  @[refutes] theorem bump_fails : ¬ fixesZero ⟨(· + 1)⟩ := by simp [fixesZero]  -- a counter-model
  A sorry is refused on @[refutes] and @[evidence] and leaves a @[satisfies] row open. A row proved only
  of a model (no @[shipped]) closes as `model`; a requirement with no @[refutes] carries the gap `vacuous`.
  `statement` prints both; the mark `lean-spec-verified` requires neither, so read the gaps, not the mark.
Levels and traceability: @[requirement must user] marks a stakeholder-level requirement (default
  level is system). A theorem `(h1 : R1 S) (h2 : R2 S) : U S` tagged @[refines] records that R1 and
  R2 refine U; U counts as closed once R1 and R2 are. A user requirement needs that or its own proof.
Commands (lake exe spec ...):
  check        one JSON line {ok,reqs,examples,problems,evidence}; exit 0 iff ok
  emit         one JSON line per example {req,name,input,output}
  test PROG    run `sh -c PROG` on every example; prints FAIL lines, then
               `TESTS passed=N failed=M`; exit 1 on any failure or problem
  statement    what the kernel checked, per requirement: witnesses, axioms, counter-models, gaps
  report PROG  one JSON line per requirement: the statement merged with a test run; a row the kernel
               left open is `tested` when all its examples pass, and a row with a failing example is
               open whatever the kernel proved. Exit 0 iff no `must` row is open.
Rules (`check` lists each violation; fix all): every requirement has a docstring and >= 1 example
  (ideally a normal and an edge/error case) or a @[satisfies] theorem; example names are non-blank
  and unique across the WHOLE spec; two examples with the same input must have the same output; an
  example of an IOReq requirement must satisfy its post. Keep the spec and program consistent."

def evidenceJson (rs : List ReqView) (st : Statement) : Json :=
  Json.mkObj <| rs.map fun r =>
    (r.name, Json.mkObj [
      ("general", toJson ((r.evidence.filter (·.2)).map (·.1))),
      ("examples", toJson ((r.evidence.filter (!·.2)).map (·.1))),
      ("witnesses", toJson (r.witnesses.map (·.1))),
      ("status", Json.str (st.statusOf r.name.toName))])

/-- Run one example against `prog`: did the output match? -/
def runExample (prog : String) (e : Ex) : IO Bool := do
  match ← runProg prog e.input.compress with
  | .ok o => return match Json.parse o with | .ok j => jeq j e.output | .error _ => false
  | .error _ => return false

/-- A report row's status from the kernel's verdict and the test run. A row with a
failing example is `open` whatever the kernel proved, since a theorem about a model
says nothing about the program under test; otherwise a closed kernel status stands,
and a row the kernel left open is `tested` when it has examples and every one passed. -/
def reportStatus (kernel : String) (hasExamples tested : Bool) : String :=
  if hasExamples && !tested then "open"
  else if kernel != "open" && kernel != "absent" then kernel
  else if tested then "tested" else "open"

#guard reportStatus "model" true false == "open"
#guard reportStatus "proved" true false == "open"
#guard reportStatus "signed" true false == "open"
#guard reportStatus "model" true true == "model"
#guard reportStatus "model" false false == "model"
#guard reportStatus "open" true true == "tested"
#guard reportStatus "open" true false == "open"
#guard reportStatus "open" false false == "open"
#guard reportStatus "absent" true true == "tested"

/-- `report PROG`: the statement merged with a test run, one JSON object per
requirement, status by `reportStatus`; the kernel's own verdict is kept beside it
as `kernel`. -/
def report (rs : List ReqView) (st : Statement) (prog : String) : IO UInt32 := do
  let ps := problems rs
  let mut allOk := ps.isEmpty
  for r in rs do
    let mut results : List (String × Bool) := []
    for e in r.examples do
      results := results ++ [(e.name, ← runExample prog e)]
    let name := r.name.toName
    let row := st.row? name
    let kernel := st.statusOf name
    let tested := !r.examples.isEmpty && results.all (·.2)
    let status := reportStatus kernel (!r.examples.isEmpty) tested
    if r.strength == "must" && status == "open" then allOk := false
    IO.println (Json.mkObj [
      ("requirement", r.name), ("level", r.level), ("strength", r.strength), ("label", r.label),
      ("kind", Json.str ((row.map (·.kind)).getD "?")), ("digest", Json.str ((row.map (·.digest)).getD "")),
      ("status", status), ("kernel", kernel),
      ("tested", tested),
      ("examples", toJson (results.map fun (n, p) => Json.mkObj [("name", n), ("pass", p)])),
      ("witnesses", toJson (r.witnesses.map (·.1))),
      ("evidence", toJson (r.evidence.map fun (t, g) => Json.mkObj [("theorem", t), ("general", g)])),
      ("refinedBy", toJson (((row.map (·.refinedBy)).getD #[]).map fun (t, cs) =>
        Json.mkObj [("theorem", t.toString), ("from", toJson (cs.map Name.toString))])),
      ("counters", toJson (((row.map (·.counters)).getD #[]).map fun (c, _) => c.toString)),
      ("gaps", toJson (((row.map (·.gaps)).getD #[]).map (·.text)))]).compress
  ps.forM fun p => IO.println (Json.mkObj [("problem", p)]).compress
  return if allOk then 0 else 1

/-- `lake exe spec <help|check|emit|test PROG|statement|report PROG>`. -/
def cli (rs : List ReqView) (st : Statement) (args : List String) : IO UInt32 := do
  let exs := rs.flatMap fun r => r.examples.map (r, ·)
  let ps := problems rs
  match args with
  | ["check"] =>
    IO.println (Json.mkObj [("ok", ps.isEmpty), ("reqs", rs.length), ("examples", exs.length),
      ("problems", toJson ps), ("evidence", evidenceJson rs st)]).compress
    return if ps.isEmpty then 0 else 1
  | ["emit"] =>
    for (r, e) in exs do
      IO.println (Json.mkObj [("req", r.name), ("name", e.name), ("input", e.input),
        ("output", e.output)]).compress
    return 0
  | ["test", prog] =>
    ps.forM fun p => IO.println s!"PROBLEM {p}"
    let mut fails := 0
    for (r, e) in exs do
      let got ← runProg prog e.input.compress
      let bad : Option String := match got with
        | .error m => some m
        | .ok o => match Json.parse o with
          | .error m => some s!"{o} (not JSON: {m})"
          | .ok j => if jeq j e.output then none else some j.compress
      if let some b := bad then
        fails := fails + 1
        IO.println s!"FAIL {r.name}/{e.name}: expected {clip e.output.compress} got {clip b}"
    IO.println s!"TESTS passed={exs.length - fails} failed={fails}"
    return if fails == 0 && ps.isEmpty then 0 else 1
  | ["statement"] => IO.print st.render; return 0
  | ["report", prog] => report rs st prog
  | [] | ["help"] => IO.println helpText; return 0
  | _ => IO.println helpText; return 2

end LeanSpec.Core
