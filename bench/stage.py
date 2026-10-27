"""`./next` in a workspace: gate to the next change request. Releases it only
when the workspace's ./test.sh passes, and logs every call to stage.json.

  python3 bench/stage.py RUN_DIR
"""
import json, subprocess, sys, time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from workspace import CHANGE

BENCH = Path(__file__).resolve().parent


def main(rdir: Path):
    meta = json.loads((rdir / "meta.json").read_text())
    stages = json.loads((BENCH / "tasks" / meta["task"] / "task.json").read_text())["stages"]
    sp = rdir / "stage.json"
    st = json.loads(sp.read_text()) if sp.exists() else {"i": 0, "log": []}
    p = subprocess.run("./test.sh", cwd=rdir / "ws", shell=True, capture_output=True, text=True, timeout=900)
    ok = p.returncode == 0
    st["log"].append({"t": round(time.time()), "stage": stages[min(st["i"], len(stages) - 1)]["name"], "tests_ok": ok})
    if ok and st["i"] < len(stages):
        st["i"] += 1
    sp.write_text(json.dumps(st, indent=1))
    if not ok:
        print("./test.sh fails - fix it first:\n" + "\n".join((p.stdout + p.stderr).splitlines()[-8:]))
        return 1
    if st["i"] < len(stages):
        print(CHANGE + stages[st["i"]]["text"])
    else:
        print("No more change requests. Reply DONE.")
    return 0


if __name__ == "__main__":
    sys.exit(main(Path(sys.argv[1])))
