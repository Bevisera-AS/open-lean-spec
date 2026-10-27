"""All 24 runs (4 tasks x py/cpp/lean x md/lean) for one GLM model, N at a time.

  GLM_API_KEY=... python3 bench/glm_batch.py glm-4.7-flash 2 [SEED] [--only TASK-LANG-ARM ...]
"""
import subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

BENCH = Path(__file__).parent


def one(model, seed, t, l, a):
    t0 = time.time()
    p = subprocess.run([sys.executable, str(BENCH / "glm_agent.py"), t, l, a, seed, model],
                       capture_output=True, text=True)
    line = (p.stdout.strip().splitlines() or ["(no output)"])[-1]
    err = "" if p.returncode == 0 else " ERROR " + p.stderr.strip().splitlines()[-1][:200] if p.stderr.strip() else " ERROR"
    print(f"{t}-{l}-{a} {round(time.time() - t0)}s {line}{err}", flush=True)


if __name__ == "__main__":
    args = sys.argv[1:]
    only = args[args.index("--only") + 1:] if "--only" in args else None
    args = args[:args.index("--only")] if "--only" in args else args
    model, n = args[0], int(args[1])
    seed = args[2] if len(args) > 2 else "41"
    combos = [(t, l, a) for t in ("ratelimit", "mortgage", "lru", "csvclean")
              for l in ("py", "cpp", "lean") for a in ("md", "lean")]
    if only:
        combos = [c for c in combos if "-".join(c) in only]
    with ThreadPoolExecutor(n) as ex:
        for c in combos:
            ex.submit(one, model, seed, *c)
