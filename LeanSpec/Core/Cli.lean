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
An example is the requirement at one point: run the program on input, expect output. Another one for a
  requirement: @[example add] def add_big : Ex := ex \"big\" (json% ...) (json% ...)
A requirement over every input: IOReq pre post with pre : Json → Bool and post : Json → Json → Bool;
  `check` runs post on each of its examples. Example, every op gets a result or an error:
  IOReq (fun i => (i.getObjVal? \"op\").isOk) (fun _ o => (o.getObjVal? \"result\").isOk || (o.getObjVal? \"error\").isOk)
json%: objects {..}, arrays [..], strings, numbers (-1, 2.5), true/false/null, nesting.
  A Lean value goes in as $x (x : String/Nat/Int/Json...), e.g. json% {\"n\": $n}.
The program reads ONE JSON value on stdin and writes ONE JSON value on stdout. Examples ARE the tests:
  write no other tests. Object key order is ignored.
The bar says how far a requirement's evidence must reach; `report` says per row whether it is MET.
  tested: every example passes. evidenced: tested, plus one sorry-free theorem with ∀ over an input tagged
  @[evidence R]. proved: a sorry-free @[satisfies] theorem about the @[shipped] product. Default: tested over
  IOSig, proved over any other Sig. Per requirement @[requirement must evidenced]; for the spec `spec_bar evidenced`.
Proofs, Lean target only (Python/C++ skip this). The program is Prog.lean; theorems go in Evidence.lean
  (import LeanSpec, Spec and Prog), so a proof never stops ./build, ./test.sh or ./next:
  def addInts (a b : Int) : Int := a + b                  -- in Prog.lean
  @[evidence add] theorem addInts_comm (a b : Int) : addInts a b = addInts b a := by unfold addInts; omega
  @[evidence add unknownOp] takes several. ∀/binders over inputs count as general, closed statements and ∃
  as examples. A theorem you cannot close: leave `sorry` in it. It is a SKETCH, listed by check/report and
  never counted, at any bar. Do not fight a proof the bar does not need; the tests are the loop's gate.
Closing a row by proof, when the product is itself a Lean value of the signature:
  structure Sig where f : Nat → Nat
  /-- f fixes zero -/
  @[requirement must] def fixesZero : Sig → Prop := fun S => S.f 0 = 0
  @[shipped] def impl : Sig := ⟨id⟩                       -- the product itself, not a model of it
  @[satisfies] theorem impl_ok : fixesZero impl := rfl     -- closes the row; the requirement is read off the type
  @[refutes] theorem bump_fails : ¬ fixesZero ⟨(· + 1)⟩ := by simp [fixesZero]  -- a counter-model
  A row proved only of a model (no @[shipped]) is `model`: it meets `evidenced`, not `proved`. No sorry-free
  @[refutes]: gap `vacuous`, reported at every bar. The mark names its weakest bar: `lean-spec-verified at tested`.
Levels and traceability: @[requirement must user] marks a stakeholder-level requirement (default
  level is system). A theorem `(h1 : R1 S) (h2 : R2 S) : U S` tagged @[refines] records that R1 and
  R2 refine U; U counts as closed once R1 and R2 are. A user requirement needs that or its own proof.
Commands (lake exe spec ...):
  check        one JSON line {ok,reqs,examples,problems,evidence}; exit 0 iff ok
  emit         one JSON line per example {req,name,input,output}
  test PROG    run `sh -c PROG` on every example; prints FAIL lines, then
               `TESTS passed=N failed=M`; exit 1 on any failure or problem
  statement    what the kernel checked, per requirement: bar, witnesses, axioms, counter-models, gaps
  report PROG  one JSON line per requirement: the statement merged with a test run; status is how far
               the evidence reaches (tested, evidenced, model, proved, signed, refined, open), `meets`
               whether it reaches the bar; a row with a failing example is open whatever the kernel
               proved. Last line: the mark. Exit 0 iff every `must` row meets its bar.
Rules (`check` lists each violation; fix all): every requirement has a docstring and >= 1 example
  (ideally a normal and an edge/error case) or a @[satisfies] theorem; example names are non-blank
  and unique across the WHOLE spec; two examples with the same input must have the same output; an
  example of an IOReq requirement must satisfy its post. Keep the spec and program consistent."

def evidenceJson (rs : List ReqView) (st : Statement) : Json :=
  Json.mkObj <| rs.map fun r =>
    let live := r.evidence.filter fun (_, _, sk) => !sk
    (r.name, Json.mkObj [
      ("general", toJson ((live.filter (·.2.1)).map (·.1))),
      ("examples", toJson ((live.filter (!·.2.1)).map (·.1))),
      ("sketched", toJson ((r.evidence.filter (·.2.2)).map (·.1))),
      ("witnesses", toJson (r.witnesses.map (·.1))),
      ("bar", Json.str (((st.row? r.name.toName).map (·.bar.text)).getD "tested")),
      ("status", Json.str (st.statusOf r.name.toName))])

/-- Run one example against `prog`: did the output match? -/
def runExample (prog : String) (e : Ex) : IO Bool := do
  match ← runProg prog e.input.compress with
  | .ok o => return match Json.parse o with | .ok j => jeq j e.output | .error _ => false
  | .error _ => return false

/-- A report row's status from the kernel's verdict, the evidence and the test run:
how far the evidence reaches. A row with a failing example is `open` whatever the
kernel proved, since a theorem about a model says nothing about the program under
test; otherwise a closed kernel status stands, and a row the kernel left open is
`evidenced` when every example passed and a sorry-free general `@[evidence]`
theorem exists, `tested` when every example passed. -/
def reportStatus (kernel : String) (hasExamples tested generalEvidence : Bool) : String :=
  if hasExamples && !tested then "open"
  else if kernel != "open" && kernel != "absent" then kernel
  else if tested && generalEvidence then "evidenced"
  else if tested then "tested" else "open"

#guard reportStatus "model" true false false == "open"
#guard reportStatus "proved" true false false == "open"
#guard reportStatus "signed" true false false == "open"
#guard reportStatus "model" true true false == "model"
#guard reportStatus "model" false false false == "model"
#guard reportStatus "open" true true false == "tested"
#guard reportStatus "open" true true true == "evidenced"
#guard reportStatus "open" true false true == "open"
#guard reportStatus "open" false false true == "open"
#guard reportStatus "open" true false false == "open"
#guard reportStatus "open" false false false == "open"
#guard reportStatus "absent" true true false == "tested"

/-- Whether a report row meets its bar. `closedAt b` is the kernel's side (no gap
blocking at `b`), which meets any bar it closes at; a failing example meets none;
`tested` meets `tested`, and with a sorry-free general `@[evidence]` theorem also
`evidenced`. Nothing but the kernel meets `proved`. -/
def meetsBar (bar : Bar) (closedAt : Bar → Bool) (generalEvidence hasExamples tested : Bool) : Bool :=
  if hasExamples && !tested then false
  else match bar with
    | .proved => closedAt .proved
    | .evidenced => closedAt .evidenced || (tested && generalEvidence)
    | .tested => closedAt .tested || tested

private def never : Bar → Bool := fun _ => false
private def always : Bar → Bool := fun _ => true
#guard meetsBar .tested never false true true
#guard !meetsBar .tested never false true false
#guard !meetsBar .tested never false false false
#guard meetsBar .tested always false false false
#guard !meetsBar .tested always false true false
#guard !meetsBar .evidenced never false true true
#guard meetsBar .evidenced never true true true
#guard meetsBar .evidenced (· != .proved) false false false
#guard !meetsBar .proved never true true true
#guard meetsBar .proved always false false false
#guard !meetsBar .proved (· != .proved) false true true

/-- `report PROG`: the statement merged with a test run, one JSON object per
requirement, status by `reportStatus`; the kernel's own verdict is kept beside it
as `kernel`. -/
def report (rs : List ReqView) (st : Statement) (prog : String) : IO UInt32 := do
  let ps := problems rs
  let mut allOk := ps.isEmpty
  let mut weakest : Bar := .proved
  for r in rs do
    let mut results : List (String × Bool) := []
    for e in r.examples do
      results := results ++ [(e.name, ← runExample prog e)]
    let name := r.name.toName
    let row := st.row? name
    let kernel := st.statusOf name
    let tested := !r.examples.isEmpty && results.all (·.2)
    let generalEvidence := r.evidence.any fun (_, g, sk) => g && !sk
    let status := reportStatus kernel (!r.examples.isEmpty) tested generalEvidence
    let bar := (row.map (·.bar)).getD .tested
    let closedAt (b : Bar) : Bool := (row.map fun rw => !rw.gaps.any (Gap.blocksAt b)).getD false
    let meets := meetsBar bar closedAt generalEvidence (!r.examples.isEmpty) tested
    if r.strength == "must" then
      weakest := weakest.min bar
      unless meets do allOk := false
    IO.println (Json.mkObj [
      ("requirement", r.name), ("level", r.level), ("strength", r.strength), ("label", r.label),
      ("kind", Json.str ((row.map (·.kind)).getD "?")), ("digest", Json.str ((row.map (·.digest)).getD "")),
      ("bar", bar.text), ("meets", meets), ("status", status), ("kernel", kernel),
      ("tested", tested),
      ("examples", toJson (results.map fun (n, p) => Json.mkObj [("name", n), ("pass", p)])),
      ("witnesses", toJson (r.witnesses.map (·.1))),
      ("evidence", toJson (r.evidence.map fun (t, g, sk) =>
        Json.mkObj [("theorem", t), ("general", g), ("sorry", sk)])),
      ("refinedBy", toJson (((row.map (·.refinedBy)).getD #[]).map fun (t, cs) =>
        Json.mkObj [("theorem", t.toString), ("from", toJson (cs.map Name.toString))])),
      ("counters", toJson (((row.map (·.counters)).getD #[]).map fun (c, _) => c.toString)),
      ("sketchedCounters", toJson (((row.map (·.sketchedCounters)).getD #[]).map Name.toString)),
      ("gaps", toJson (((row.map (·.gaps)).getD #[]).map (·.text)))]).compress
  ps.forM fun p => IO.println (Json.mkObj [("problem", p)]).compress
  IO.println (Json.mkObj [("mark", Json.str
    (if allOk then s!"lean-spec-verified at {weakest.text}" else "none"))]).compress
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
