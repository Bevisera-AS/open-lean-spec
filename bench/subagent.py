"""Runs driven as in-session subagents (Max plan, no API key). The session
prepares a workspace, hands each stage prompt to a subagent, records what the
subagent's completion notice reports, then scores.

  python3 bench/subagent.py prep  TASK LANG ARM SEED [MODEL]   -> prompts.json
  python3 bench/subagent.py stage RUN_ID STAGE TOKENS TOOL_USES WALL_MS
  python3 bench/subagent.py score RUN_ID
"""
import json, shutil, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import workspace, check
from run import RUNS, BENCH

PREAMBLE = ("You are a coding agent. Your workspace is {ws}. Work ONLY there: start every shell command "
            "with `cd {ws} && `, use absolute paths under {ws} for files, and never read anything outside it. "
            "Be economical: no explanations, no summaries. When finished reply DONE.\n\n")


def prep(task, lang, arm, seed, model="haiku"):
    run_id = f"{task}-{lang}-{arm}-{model}-s{seed}"
    rdir = RUNS / run_id
    if rdir.exists():
        shutil.rmtree(rdir)
    ws = rdir / "ws"
    spec = json.loads((BENCH / "tasks" / task / "task.json").read_text())
    brief = workspace.make(ws, task, arm, lang)
    pre = PREAMBLE.format(ws=ws)
    prompts = [{"stage": "all", "prompt": pre + brief + "\n\nTASK\n" + spec["stages"][0]["text"]}]
    (rdir / "prompts.json").write_text(json.dumps(prompts, indent=1))
    (ws / "BRIEF.txt").write_text(prompts[0]["prompt"])
    meta = {"run": run_id, "task": task, "lang": lang, "arm": arm, "model": model, "seed": int(seed),
            "driver": "subagent", "stages": []}
    (rdir / "meta.json").write_text(json.dumps(meta, indent=1))
    print(run_id)


def stage(run_id, name, tokens, tools, wall_ms):
    p = RUNS / run_id / "meta.json"
    meta = json.loads(p.read_text())
    meta["stages"] = [s for s in meta["stages"] if s["stage"] != name]
    meta["stages"].append({"stage": name, "is_error": False, "turns": int(tools),
                           "usage": {"total_tokens": int(tokens)}, "wall_s": int(wall_ms) / 1000})
    p.write_text(json.dumps(meta, indent=1))


def finish(run_id, transcript, wall_ms):
    """Self-paced run: stages come from ./next's log, usage from the transcript."""
    import usage
    rdir = RUNS / run_id
    meta = json.loads((rdir / "meta.json").read_text())
    st = json.loads((rdir / "stage.json").read_text()) if (rdir / "stage.json").exists() else {"i": 0, "log": []}
    names = ["base", "cr1", "cr2"]
    meta["stages"] = [{"stage": n, "is_error": False, "turns": 0, "usage": {}, "wall_s": 0} for n in names[:st["i"]]]
    if meta["stages"]:
        meta["stages"][0]["wall_s"] = int(wall_ms) / 1000
    meta["next_calls"] = len(st["log"])
    (rdir / "meta.json").write_text(json.dumps(meta, indent=1))
    import shutil
    shutil.copy(transcript, rdir / "transcript.jsonl")
    tot, calls = usage.usage(rdir / "transcript.jsonl")
    meta["usage_exact"] = {**tot, "api_calls": calls}
    (rdir / "meta.json").write_text(json.dumps(meta, indent=1))
    score(run_id)


def score(run_id):
    rdir = RUNS / run_id
    r = check.score(rdir, json.loads((rdir / "meta.json").read_text()))
    print(json.dumps({k: r[k] for k in ("run", "usage", "build_ok", "hidden", "repr_drift", "spec_drift",
                                        "strength", "coverage", "lean", "sizes")}))


if __name__ == "__main__":
    {"prep": prep, "stage": stage, "finish": finish, "score": score}[sys.argv[1]](*sys.argv[2:])
