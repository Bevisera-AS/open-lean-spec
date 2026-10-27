"""Deterministic bench smoke, no model: build a workspace for every arm from the
templates, put a known spec and program in the Lean-arm ones, and run the
referee on them (check, test, report, the ./next gate, the jeq comparator).

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
        code, out = sh("./test.sh", ws)
        ok &= expect(code == 0 and "TESTS passed=5 failed=0" in out, f"{arm}: test runs the five examples", out)
        code, out = sh("lake exe spec report ./run", ws)
        rows = [json.loads(l) for l in out.splitlines() if l.startswith("{") and '"requirement"' in l]
        ok &= expect(code == 0 and len(rows) == 3 and all(r["tested"] for r in rows),
                     f"{arm}: report marks every row tested", out)
        (ws / "main.py").write_text(BROKEN)
        code, out = sh("./next", ws)
        ok &= expect(code == 1 and "fix it first" in out, f"{arm}: ./next refuses while tests fail", out)
        (ws / "main.py").write_text(PROG)
        code, out = sh("./next", ws)
        ok &= expect(code == 0 and "Change request 1" in out, f"{arm}: ./next releases the next change request", out)
        st = json.loads((rdir / "stage.json").read_text())
        ok &= expect(st["i"] == 1 and len(st["log"]) == 2, f"{arm}: stage.json records both calls")
    return 0 if ok else 1


if __name__ == "__main__":
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(tempfile.mkdtemp(prefix="lean-spec-smoke-"))
    print(f"smoke in {root}")
    sys.exit(main(root))
