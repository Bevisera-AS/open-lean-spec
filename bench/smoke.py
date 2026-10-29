"""Deterministic bench smoke, no model: build a workspace for every arm from the
templates, put a known spec and program in the Lean-arm ones, and run the
referee on them (check, test, report, the ./next gate, the jeq comparator).
Then a Lean-target workspace: theorems in Evidence.lean, a sketch among them, a
proof that does not compile, and the bar (`spec_bar evidenced`) in the report.

  python3 bench/smoke.py [DIR]      DIR defaults to a temp directory

Exit 0 iff every step behaves as the brief promises. CI runs it in `verify`.
"""
import json, os, subprocess, sys, tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import workspace

SPEC = '''import LeanSpec
open LeanSpec.Core Lean

/-- add two numbers -/
@[requirement must] def add : IOSig → Prop := Req.holds [
  ex "basic" (json% {"op": "add", "xs": [1, 2]}) (json% {"result": 3}),
  ex "neg" (json% {"op": "add", "xs": [-1, 1]}) (json% {"result": 0})]

/-- unknown op is an error -/
@[requirement must] def unknownOp : IOSig → Prop := Req.holds [
  ex "bad" (json% {"op": "pow", "xs": []}) (json% {"error": "unknown op", "detail": null})]

@[example add] def add_big : Ex := ex "big" (json% {"op": "add", "xs": [100, 200, 300]}) (json% {"result": 600})

/-- every answer is an object -/
@[requirement should] def answersObject : IOSig → Prop :=
  IOReq (fun i => (i.getObjVal? "op").isOk)
        (fun _ o => (o.getObjVal? "result").isOk || (o.getObjVal? "error").isOk)
@[example answersObject] def obj_one : Ex := ex "obj" (json% {"op": "add", "xs": []}) (json% {"result": 0})
'''
PROG = '''import json, sys
j = json.load(sys.stdin)
if j.get("op") == "add":
    print(json.dumps({"result": sum(j["xs"])}))
else:
    print(json.dumps({"error": "unknown op", "detail": None}))
'''
BROKEN = PROG.replace("sum(j[\"xs\"])", "0")

# The Lean target: the same program in Lean, theorems about it in Evidence.lean.
LEAN_PROG = '''import Lean.Data.Json
open Lean

def addInts (xs : List Int) : Int := xs.foldl (· + ·) 0

def answer (j : Json) : Json :=
  match j.getObjValAs? String "op", j.getObjVal? "xs" with
  | .ok "add", .ok (.arr xs) =>
    Json.mkObj [("result", toJson (addInts (xs.toList.filterMap fun x => x.getInt?.toOption)))]
  | _, _ => Json.mkObj [("error", "unknown op"), ("detail", Json.null)]
'''
LEAN_MAIN = '''import Prog

def main : IO Unit := do
  let s ← (← IO.getStdin).readToEnd
  match Lean.Json.parse s with
  | .ok j => IO.println (answer j).compress
  | .error e => IO.eprintln e
'''
# One general theorem, one example-scope theorem, one sketch.
LEAN_EVIDENCE = '''import LeanSpec
import Spec
import Prog

@[evidence add] theorem addInts_single (x : Int) : addInts [x] = x := by simp [addInts]
@[evidence add] theorem addInts_nil : addInts [] = 0 := rfl
@[evidence add unknownOp] theorem answer_total (j : Lean.Json) : (answer j).isNull = false := by sorry
'''
LEAN_EVIDENCE_BROKEN = LEAN_EVIDENCE + "theorem wrong : addInts [1] = 2 := rfl\n"


def sh(cmd, cwd, env=None):
    p = subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True,
                       env={**os.environ, **(env or {})}, timeout=900)
    return p.returncode, p.stdout + p.stderr


def expect(cond, what, out=""):
    print(("ok   " if cond else "FAIL ") + what)
    if not cond and out:
        print("\n".join(out.strip().splitlines()[-8:]))
    return cond


def main(root):
    ok = True
    for arm in ("md", "core", "logic"):
        rdir = root / f"smoke-py-{arm}"
        ws = rdir / "ws"
        brief = workspace.make(ws, "lru", arm, "py")
        (rdir / "meta.json").write_text(json.dumps({"task": "lru"}))
        ok &= expect("./jeq" in brief if arm == "md" else "lake exe spec" in brief, f"{arm}: brief names its referee")
        code, _ = sh('./jeq \'{"a": 1, "b": [1,2]}\' \'{"b":[1,2],"a":1}\' && ! ./jeq \'{"a":1}\' \'{"a":2}\'', ws)
        ok &= expect(code == 0, f"{arm}: jeq compares by value")
        (ws / "main.py").write_text(PROG)
        if arm == "md":
            continue
        (ws / "Spec.lean").write_text(SPEC)
        code, out = sh("lake build spec", ws)
        ok &= expect(code == 0, f"{arm}: workspace builds against lean-spec", out)
        if code:
            continue
        code, out = sh("lake exe spec check", ws)
        ok &= expect(code == 0 and '"ok":true' in out.replace(" ", ""), f"{arm}: check passes", out)
        code, out = sh("lake exe spec statement", ws)
        ok &= expect(code == 0 and "mark none" in out and out.count("status open") == 3
                     and out.count("gap no-witness") == 3,
                     f"{arm}: statement leaves an example-only spec open, mark none", out)
        code, out = sh("./test.sh", ws)
        ok &= expect(code == 0 and "TESTS passed=5 failed=0" in out, f"{arm}: test runs the five examples", out)
        code, out = sh("lake exe spec report ./run", ws)
        rows = [json.loads(l) for l in out.splitlines() if l.startswith("{") and '"requirement"' in l]
        ok &= expect(code == 0 and len(rows) == 3 and all(r["tested"] for r in rows),
                     f"{arm}: report marks every row tested", out)
        mark = next((json.loads(l)["mark"] for l in out.splitlines() if l.startswith('{"mark"')), None)
        ok &= expect(all(r["meets"] and r["bar"] == "tested" for r in rows) and mark == "lean-spec-verified at tested",
                     f"{arm}: every row meets `tested` and the mark says so", out)
        (ws / "main.py").write_text(BROKEN)
        code, out = sh("lake exe spec report ./run", ws)
        rows = [json.loads(l) for l in out.splitlines() if l.startswith("{") and '"requirement"' in l]
        add = [r for r in rows if r["requirement"].endswith("add")]
        ok &= expect(code == 1 and len(add) == 1 and add[0]["status"] == "open" and not add[0]["tested"],
                     f"{arm}: report keeps a row with a failing example open", out)
        code, out = sh("./next", ws)
        ok &= expect(code == 1 and "fix it first" in out, f"{arm}: ./next refuses while tests fail", out)
        (ws / "main.py").write_text(PROG)
        code, out = sh("./next", ws)
        ok &= expect(code == 0 and "Change request 1" in out, f"{arm}: ./next releases the next change request", out)
        st = json.loads((rdir / "stage.json").read_text())
        ok &= expect(st["i"] == 1 and len(st["log"]) == 2, f"{arm}: stage.json records both calls")
    ok &= lean_target(root)
    return 0 if ok else 1


def lean_target(root):
    """Theorems live in Evidence.lean: the loop never waits on one, a sketch is
    listed and not counted, and the bar decides what `report` accepts."""
    ok = True
    rdir = root / "smoke-lean-core"
    ws = rdir / "ws"
    brief = workspace.make(ws, "lru", "core", "lean", bar="evidenced")
    (rdir / "meta.json").write_text(json.dumps({"task": "lru"}))
    ok &= expect("Evidence.lean" in brief and "spec_bar evidenced" in (ws / "Spec.lean").read_text(),
                 "lean: brief names Evidence.lean and Spec.lean carries the bar")
    (ws / "Spec.lean").write_text(SPEC.replace("open LeanSpec.Core Lean\n", "open LeanSpec.Core Lean\n\nspec_bar evidenced\n"))
    (ws / "Prog.lean").write_text(LEAN_PROG)
    (ws / "Main.lean").write_text(LEAN_MAIN)
    (ws / "Evidence.lean").write_text(LEAN_EVIDENCE_BROKEN)
    code, out = sh("./build", ws)
    ok &= expect(code == 0, "lean: ./build builds the program with a broken Evidence.lean", out)
    code, out = sh("./test.sh", ws)
    ok &= expect(code == 0 and "TESTS passed=5 failed=0" in out,
                 "lean: ./test.sh passes with a broken Evidence.lean (spec-test imports Spec only)", out)
    code, out = sh("lake exe spec check", ws)
    ok &= expect(code != 0 and "Evidence.lean" in out, "lean: check stops on a proof that does not compile", out)
    (ws / "Evidence.lean").write_text(LEAN_EVIDENCE)
    code, out = sh("lake exe spec check", ws)
    flat = out.replace(" ", "")
    ok &= expect(code == 0 and '"sketched":["answer_total"]' in flat and '"general":["addInts_single"]' in flat
                 and '"bar":"evidenced"' in flat,
                 "lean: check lists the sketch apart from the general evidence, with the bar", out)
    code, out = sh("lake exe spec report ./run", ws)
    rows = {json.loads(l)["requirement"].split(".")[-1]: json.loads(l)
            for l in out.splitlines() if l.startswith("{") and '"requirement"' in l}
    mark = next((json.loads(l)["mark"] for l in out.splitlines() if l.startswith('{"mark"')), None)
    ok &= expect(code == 1 and rows["add"]["meets"] and rows["add"]["status"] == "evidenced"
                 and not rows["unknownOp"]["meets"] and rows["unknownOp"]["status"] == "tested"
                 and rows["unknownOp"]["bar"] == "evidenced" and mark == "none"
                 and any(e["sorry"] for e in rows["add"]["evidence"]),
                 "lean: at `evidenced` the row with general evidence meets, the one without does not; the sketch is flagged", out)
    (ws / "Spec.lean").write_text(SPEC.replace("open LeanSpec.Core Lean\n", "open LeanSpec.Core Lean\n\nspec_bar tested\n"))
    code, out = sh("lake exe spec report ./run", ws)
    mark = next((json.loads(l)["mark"] for l in out.splitlines() if l.startswith('{"mark"')), None)
    ok &= expect(code == 0 and mark == "lean-spec-verified at tested",
                 "lean: at `tested` every row meets and the mark names the bar", out)
    code, out = sh("lake exe spec help 2>/dev/null", ws)  # stdout only: lake's progress lines go to stderr
    ok &= expect(code == 0 and len(out.strip().splitlines()) <= 60, f"lean: help is {len(out.strip().splitlines())} lines (<= 60)")
    return ok


if __name__ == "__main__":
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(tempfile.mkdtemp(prefix="lean-spec-smoke-"))
    print(f"smoke in {root}")
    sys.exit(main(root))
