"""Run a matrix of bench runs through run.py, a few at a time, skipping runs
that already have a result.json.

  python3 bench/batch.py SEED [SEED ...] [--model haiku,sonnet] [--arms md,core,logic]
                         [--gates off,on] [--tasks lru,...] [--langs py] [-j 3] [--dry]

Round 5 (plan step 8): arms md, core, logic, each with and without the propose
gate, four tasks, seeds 41 and 42, Haiku and Sonnet, Python programs:

  python3 bench/batch.py 41 42 --model haiku,sonnet -j 3
"""
import argparse, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from run import RUNS, BENCH

TASKS = ["ratelimit", "mortgage", "lru", "csvclean"]
# A run that dies within seconds did not reach the model (the `claude` binary was
# being replaced by an update, once); the rest of the matrix is then skipped
# instead of failing one after another.
ABORT = threading.Event()


def one(task, lang, arm, gate, model, seed, dry):
    run_id = f"{task}-{lang}-{arm}{'g' if gate else ''}-{model}-s{seed}"
    if (RUNS / run_id / "result.json").exists():
        return f"{run_id}: have result, skipped"
    if ABORT.is_set():
        return f"{run_id}: not started (batch aborted)"
    cmd = [sys.executable, str(BENCH / "run.py"), task, lang, arm, str(seed), "--model", model]
    if gate:
        cmd.append("--gate")
    if dry:
        return " ".join(cmd)
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0 and time.time() - t0 < 15:
        ABORT.set()
    tail = (p.stdout + p.stderr).strip().splitlines()
    summary = next((l for l in reversed(tail) if l.startswith('{"run"')), tail[-1] if tail else "")
    (RUNS / run_id / "batch.log").write_text(p.stdout + p.stderr) if (RUNS / run_id).exists() else None
    return f"{run_id}: exit {p.returncode} {round(time.time() - t0)}s {summary[:160]}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("seeds", nargs="+", type=int)
    ap.add_argument("--model", default="haiku")
    ap.add_argument("--arms", default="md,core,logic")
    ap.add_argument("--gates", default="off,on")
    ap.add_argument("--tasks", default=",".join(TASKS))
    ap.add_argument("--langs", default="py")
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--dry", action="store_true")
    a = ap.parse_args()
    jobs = [(t, l, arm, g == "on", m, s)
            for m in a.model.split(",") for s in a.seeds for t in a.tasks.split(",")
            for l in a.langs.split(",") for arm in a.arms.split(",") for g in a.gates.split(",")]
    print(f"{len(jobs)} runs, {a.j} at a time", flush=True)
    with ThreadPoolExecutor(max_workers=a.j) as ex:
        for line in ex.map(lambda j: one(*j, a.dry), jobs):
            print(line, flush=True)


if __name__ == "__main__":
    main()
