"""Score a finished workspace. All checks are deterministic; no model is called.

correctness   hidden cases on the agent's program, tallied per ground-truth requirement
repr_drift    the agent's own tests/examples on its own program (code vs its spec)
spec_drift    the agent's own tests/examples on the reference (its spec vs the truth)
strength      planted mutants of the reference killed by the agent's tests
coverage      line coverage of the agent's program under its own tests (py, cpp)

  python3 bench/check.py RUN_DIR      re-score an existing run
"""
import json, os, re, shutil, subprocess, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from workspace import CXX, LEAN_ARMS

BENCH = Path(__file__).resolve().parent
VENV_PY = BENCH.parent / ".venv" / "bin" / "python"
TESTS_RE = re.compile(r"TESTS passed=(\d+) failed=(\d+)")


def sh(cmd, cwd, inp=None, env=None, timeout=600):
    try:
        p = subprocess.run(cmd, cwd=cwd, input=inp, capture_output=True, text=True, shell=True,
                           env={**os.environ, **(env or {})}, timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return -9, "", "timeout"


def tests(ws, prog):
    """Run the agent's test.sh against PROG; None when it produced no TESTS line."""
    if not (ws / "test.sh").exists():
        return None
    env = {"PROG": prog}
    env.pop("MUTANT", None)
    code, out, err = sh("./test.sh", ws, env=env)
    m = TESTS_RE.findall(out)
    if not m:
        return {"ok": False, "passed": 0, "failed": None, "exit": code, "tail": (out + err)[-300:]}
    p, f = map(int, m[-1])
    return {"ok": code == 0 and f == 0, "passed": p, "failed": f, "exit": code}


def hidden(ws, task_dir):
    passed, total, fails = 0, 0, {}
    for line in (task_dir / "cases.jsonl").read_text().splitlines():
        c = json.loads(line)
        total += 1
        code, out, _ = sh("./run", ws, inp=json.dumps(c["input"]), timeout=20)
        try:
            ok = code == 0 and json.loads(out) == c["output"]
        except json.JSONDecodeError:
            ok = False
        passed += ok
        if not ok:
            for r in c["req"]:
                fails[r] = fails.get(r, 0) + 1
    return {"passed": passed, "total": total, "failed_by_req": fails}


def coverage(ws, lang):
    cov = ws / ".cov"
    shutil.rmtree(cov, ignore_errors=True)
    cov.mkdir()
    if lang == "py":
        prog = f"{VENV_PY} -m coverage run --parallel-mode --data-file={cov}/c main.py"
        tests(ws, prog)
        sh(f"{VENV_PY} -m coverage combine --data-file={cov}/c {cov}", ws)
        code, out, _ = sh(f"{VENV_PY} -m coverage report --data-file={cov}/c --format=total", ws)
        return float(out.strip()) if code == 0 and out.strip() else None
    if lang == "cpp":
        code, _, _ = sh(f"{CXX} -O0 -fprofile-instr-generate -fcoverage-mapping -o {cov}/prog *.cpp", ws)
        if code:
            return None
        tests(ws, f"LLVM_PROFILE_FILE={cov}/%p.profraw {cov}/prog")
        sh(f"xcrun llvm-profdata merge -o {cov}/m.profdata {cov}/*.profraw", ws)
        code, out, _ = sh(f"xcrun llvm-cov export -summary-only {cov}/prog -instr-profile={cov}/m.profdata", ws)
        try:
            return round(json.loads(out)["data"][0]["totals"]["lines"]["percent"], 1)
        except (json.JSONDecodeError, KeyError, IndexError):
            return None
    return None


def lean_stats(ws):
    src = [p for p in ws.glob("*.lean") if p.name not in ("lakefile.lean", "SpecMain.lean")]
    text = "\n".join(p.read_text(errors="replace") for p in src)
    heads = re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+\S+(.*?):=", text, re.M | re.S)
    general = sum(1 for h in heads if re.match(r"\s*[({\[]", h) or re.match(r"\s*:\s*∀", h))
    return {"theorems": len(heads), "general": general,
            "guards": len(re.findall(r"^\s*#guard\b", text, re.M)),
            "sorries": len(re.findall(r"\bsorry\b", text))}


def sizes(ws):
    def chars(globs):
        return sum(p.stat().st_size for g in globs for p in ws.glob(g))
    return {"spec": chars(["SPEC.md", "Spec.lean"]), "tests": chars(["test.sh", "test_*", "tests/*"]),
            "code": chars(["main.py", "*.cpp", "*.hpp", "*.h", "Main.lean", "Prog.lean"])}


def tokens(stages):
    keys = ["input_tokens", "cache_creation_input_tokens", "cache_read_input_tokens", "output_tokens",
            "total_tokens"]
    tot = {k: sum((s.get("usage") or {}).get(k, 0) for s in stages) for k in keys}
    tot["cost_usd"] = round(sum(s.get("cost_usd") or 0 for s in stages), 4)
    tot["turns"] = sum(s.get("turns") or 0 for s in stages)
    tot["wall_s"] = round(sum(s.get("wall_s") or 0 for s in stages), 1)
    return tot


def score(rdir: Path, meta: dict):
    rdir = rdir.resolve()
    ws, lang = rdir / "ws", meta["lang"]
    task_dir = BENCH / "tasks" / meta["task"]
    ref = f"python3 {task_dir / 'ref.py'}"
    code, _, err = sh("./build", ws)
    r = {k: meta[k] for k in ("run", "task", "lang", "arm", "model", "seed")}
    r["gate"] = bool(meta.get("gate"))
    r["completed"] = all(not s.get("is_error") for s in meta["stages"]) and len(meta["stages"]) == 3
    r["usage"] = tokens(meta["stages"])
    if meta.get("usage_exact"):
        r["usage"].update(meta["usage_exact"], total_tokens=None)
    r["build_ok"] = code == 0
    r["hidden"] = hidden(ws, task_dir) if code == 0 else None
    r["repr_drift"] = tests(ws, "./run") if code == 0 else None
    r["spec_drift"] = tests(ws, ref)
    sd = r["spec_drift"]
    r["strength"] = ({m: not (tests(ws, f"MUTANT={m} {ref}") or {}).get("ok", True)
                      for m in ("m1", "m2", "m3")} if sd and sd["ok"] else None)
    r["coverage"] = coverage(ws, lang) if code == 0 else None
    r["lean"] = lean_stats(ws) if lang == "lean" or meta["arm"] in LEAN_ARMS else None
    if meta["arm"] in LEAN_ARMS:
        _, out, _ = sh("lake exe spec check", ws)
        try:
            r["spec_check"] = json.loads(out.strip().splitlines()[-1])
        except (json.JSONDecodeError, IndexError):
            r["spec_check"] = {"raw": out[-300:]}
    r["sizes"] = sizes(ws)
    (rdir / "result.json").write_text(json.dumps(r, indent=1))
    res = BENCH / "results"
    res.mkdir(exist_ok=True)
    with open(res / "results.jsonl", "a") as f:
        f.write(json.dumps(r) + "\n")
    return r


if __name__ == "__main__":
    d = Path(sys.argv[1])
    print(json.dumps(score(d, json.loads((d / "meta.json").read_text())), indent=1))
