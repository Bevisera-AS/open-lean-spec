"""One benchmark run: a model builds a task through its stages in a fresh
workspace via headless `claude -p`, then the workspace is scored.

  python3 bench/run.py TASK LANG ARM SEED [--model haiku] [--gate]

ARM is md, core or logic (`lean` is the old name of core). With --gate every
stage is two phases: the builder proposes the spec change alone, a reviewer
(a fresh session with Read only) accepts it or returns it with notes, at most
two returns, and only then the builder applies it. The reviewer's tokens are
added to the stage's usage and kept apart under `gate`.
"""
import argparse, json, shutil, subprocess, sys, time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import workspace, check

BENCH = Path(__file__).parent
RUNS = BENCH.parent.parent / "lean-spec-core-runs"  # outside the repo: agents cannot see references
SYSTEM = ("You are a coding agent. Work only in the current directory, using the tools to write files "
          "and run commands. Be economical: no explanations, no summaries. When finished reply DONE.")
TOOLS = "Bash,Read,Write,Edit"
MAX_TURNS = {"base": 40, "cr1": 25, "cr2": 25}
MAX_RETURNS = 2

PROPOSE = ("Phase 1, propose. Write only the specification, {spec}{check}; do not write the program "
           "or tests yet. When the specification is written, reply PROPOSED.\n\n")
RETURNED = ("The reviewer returned the specification:\n\n{notes}\n\nFix only the specification{check}, "
            "then reply PROPOSED.")
APPLY = ("The specification is accepted. Phase 2, apply: build the program and tests as the brief says, "
         "keep the specification as reviewed unless a test shows it wrong, and when ./test.sh passes "
         "run ./next as the brief says.")
REVIEW_SYSTEM = ("You are the reviewer of a specification. Read the specification file named in the "
                 "request, and nothing else. Do not edit any file.")
REVIEW = ("The task:\n\n{task}\n\nRead {spec} in the current directory. Accept it only if every "
          "requirement follows from the task and nothing the task does not define has been invented "
          "(an undefined input stays undefined, not an error case), and every requirement has a concrete "
          "example. Reply with exactly ACCEPT on the first line, or RETURN on the first line followed by "
          "the requirement names and what is wrong, at most 8 lines.")


def claude(prompt, cwd, model, session=None, max_turns=40, tools=TOOLS, system=SYSTEM):
    cmd = ["claude", "-p", prompt, "--model", model, "--output-format", "json",
           "--max-turns", str(max_turns), "--tools", tools, "--allowedTools", tools,
           "--system-prompt", system, "--setting-sources", "", "--strict-mcp-config",
           "--disable-slash-commands"]
    if session:
        cmd += ["--resume", session]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=3600)
    try:
        out = json.loads(p.stdout)
    except json.JSONDecodeError:
        out = {"is_error": True, "result": (p.stdout + p.stderr)[-2000:]}
    out["wall_s"] = round(time.time() - t0, 1)
    return out


def add_usage(a, b):
    out = dict(a or {})
    for k, v in (b or {}).items():
        if isinstance(v, (int, float)) and not isinstance(v, bool):
            out[k] = (out.get(k) or 0) + v
    return out


def gated(change, ws, model, session, arm, task_text, max_turns):
    """Propose, review, (return, fix)*, then hand back the session for apply."""
    spec = "SPEC.md" if arm == "md" else "Spec.lean"
    chk = "" if arm == "md" else "; `lake exe spec check` must pass"
    gate = {"rounds": 0, "verdicts": [], "usage": {}, "wall_s": 0.0, "turns": 0}
    out = claude(PROPOSE.format(spec=spec, check=chk) + change, ws, model, session, max_turns)
    session = out.get("session_id", session)
    gate["usage"] = add_usage(gate["usage"], out.get("usage"))
    gate["wall_s"] += out["wall_s"]
    gate["turns"] += out.get("num_turns") or 0
    for _ in range(MAX_RETURNS + 1):
        rev = claude(REVIEW.format(task=task_text, spec=spec), ws, model, None, 6, "Read", REVIEW_SYSTEM)
        gate["usage"] = add_usage(gate["usage"], rev.get("usage"))
        gate["wall_s"] += rev["wall_s"]
        gate["rounds"] += 1
        text = str(rev.get("result", "")).strip()
        verdict = "ACCEPT" if text.upper().startswith("ACCEPT") else "RETURN"
        gate["verdicts"].append({"verdict": verdict, "notes": text[:800]})
        if verdict == "ACCEPT" or gate["rounds"] > MAX_RETURNS:
            break
        out = claude(RETURNED.format(notes=text, check=chk), ws, model, session, max_turns)
        session = out.get("session_id", session)
        gate["usage"] = add_usage(gate["usage"], out.get("usage"))
        gate["wall_s"] += out["wall_s"]
        gate["turns"] += out.get("num_turns") or 0
    return gate, session


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("task"); ap.add_argument("lang", choices=["py", "cpp", "lean"])
    ap.add_argument("arm", choices=["md", "lean", "core", "logic"]); ap.add_argument("seed", type=int)
    ap.add_argument("--model", default="haiku")
    ap.add_argument("--gate", action="store_true", help="a reviewer accepts each spec change before apply")
    a = ap.parse_args()
    arm = "core" if a.arm == "lean" else a.arm
    run_id = f"{a.task}-{a.lang}-{arm}{'g' if a.gate else ''}-{a.model}-s{a.seed}"
    rdir = RUNS / run_id
    if rdir.exists():
        shutil.rmtree(rdir)
    ws = rdir / "ws"
    task = json.loads((BENCH / "tasks" / a.task / "task.json").read_text())
    brief = workspace.make(ws, a.task, arm, a.lang)
    stages, session, so_far = [], None, []
    for st in task["stages"]:
        change = (brief + "\n\nTASK\n" + st["text"]) if session is None else workspace.CHANGE + st["text"]
        so_far.append(st["text"])  # the reviewer judges against the whole task so far, not the last change
        gate = None
        if a.gate:
            gate, session = gated(change, ws, a.model, session, arm, "\n\n".join(so_far), MAX_TURNS[st["name"]])
            prompt = APPLY
        else:
            prompt = change
        out = claude(prompt, ws, a.model, session, MAX_TURNS[st["name"]])
        session = out.get("session_id", session)
        stage = {"stage": st["name"], "is_error": out.get("is_error"), "turns": out.get("num_turns"),
                 "cost_usd": out.get("total_cost_usd"), "usage": out.get("usage"),
                 "wall_s": out["wall_s"], "result": str(out.get("result", ""))[-500:]}
        if gate:
            stage["gate"] = gate
            stage["usage"] = add_usage(stage["usage"], gate["usage"])
            stage["wall_s"] = round(stage["wall_s"] + gate["wall_s"], 1)
            stage["turns"] = (stage["turns"] or 0) + gate["turns"]
        stages.append(stage)
        print(f"{run_id} {st['name']}: turns={stage['turns']} err={out.get('is_error')} {stage['wall_s']}s"
              + (f" gate={[v['verdict'] for v in gate['verdicts']]}" if gate else ""))
        if out.get("is_error") and out.get("api_error_status"):
            break
    for t in Path.home().glob(f".claude/projects/*/{session}.jsonl") if session else []:
        shutil.copy(t, rdir / "transcript.jsonl")
    meta = {"run": run_id, "task": a.task, "lang": a.lang, "arm": arm, "model": a.model,
            "seed": a.seed, "gate": a.gate, "driver": "claude-p", "session": session, "stages": stages}
    (rdir / "meta.json").write_text(json.dumps(meta, indent=1))
    score = check.score(rdir, meta)
    print(json.dumps(score))


if __name__ == "__main__":
    main()
