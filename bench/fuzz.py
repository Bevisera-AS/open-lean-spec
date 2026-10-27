"""Differential fuzz: run a workspace program and the reference on random inputs
drawn from the task's own generator style, larger than the hidden cases.

  python3 bench/fuzz.py RUN_DIR [N]
"""
import importlib.util, json, random, subprocess, sys
from pathlib import Path

BENCH = Path(__file__).resolve().parent


def gen_inputs(task, n):
    spec = importlib.util.spec_from_file_location("gen", BENCH / "tasks" / task / "gen.py")
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    rng = random.Random(99)
    return [gen.fuzz(rng) for _ in range(n)]


def run(cmd, cwd, inp):
    p = subprocess.run(cmd, cwd=cwd, input=json.dumps(inp), capture_output=True, text=True, shell=True, timeout=20)
    try:
        return json.loads(p.stdout)
    except json.JSONDecodeError:
        return {"__err__": (p.stdout + p.stderr)[-200:]}


if __name__ == "__main__":
    rdir, n = Path(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 400
    task = json.loads((rdir / "meta.json").read_text())["task"]
    ref = f"python3 {BENCH / 'tasks' / task / 'ref.py'}"
    bad = []
    for inp in gen_inputs(task, n):
        a, b = run("./run", rdir / "ws", inp), run(ref, rdir / "ws", inp)
        if a != b:
            bad.append({"input": inp, "got": a, "want": b})
    print(json.dumps({"run": rdir.name, "cases": n, "mismatches": len(bad), "first": bad[:2]}))
