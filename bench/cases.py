"""Build hidden cases for every task: run the reference, check it reproduces each
hand-computed `expect`, check every mutant is caught, write cases.jsonl."""
import importlib.util, json, os, subprocess, sys
from pathlib import Path

TASKS = Path(__file__).parent / "tasks"


def run(task_dir, inp, mutant=""):
    env = dict(os.environ, MUTANT=mutant)
    p = subprocess.run([sys.executable, str(task_dir / "ref.py")], input=json.dumps(inp),
                       capture_output=True, text=True, env=env, timeout=30)
    return json.loads(p.stdout) if p.returncode == 0 else {"__crash__": p.stderr[-300:]}


def build(task_dir):
    spec = importlib.util.spec_from_file_location("gen", task_dir / "gen.py")
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    mutants = json.loads((task_dir / "task.json").read_text())["mutants"]
    ok, rows, kills = True, [], {m: 0 for m in mutants}
    for n, c in enumerate(gen.cases()):
        out = run(task_dir, c["input"])
        if "expect" in c and out != c["expect"]:
            ok = False
            print(f"  {task_dir.name} case {n} {c['req']}: ref {out} != expect {c['expect']}")
        for m in mutants:
            kills[m] += run(task_dir, c["input"], m) != out
        rows.append({"id": n, "req": c["req"], "input": c["input"], "output": out})
    for m, k in kills.items():
        if k == 0:
            ok = False
            print(f"  {task_dir.name} mutant {m} survives every case")
    (task_dir / "cases.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
    print(f"{task_dir.name}: {len(rows)} cases, kills {kills}, {'OK' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    sys.exit(0 if all([build(d) for d in sorted(TASKS.iterdir()) if d.is_dir()]) else 1)
