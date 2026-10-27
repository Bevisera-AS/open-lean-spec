"""One benchmark run driven by a GLM model through z.ai's OpenAI-compatible API.
Same workspace, brief and ./next gate as the subagent runs; scored by check.py.

  GLM_API_KEY=... python3 bench/glm_agent.py TASK LANG ARM SEED MODEL
  MODEL: glm-4.7-flash | glm-5.1

Tools: read_file, write_file, run_command (sh in the workspace, 300 s, no API key in its env).
"""
import json, os, subprocess, sys, time, urllib.error, urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import subagent, check
from run import RUNS

API = "https://api.z.ai/api/paas/v4/chat/completions"
MAX_TURNS, MAX_OUT, TIMEOUT_S = 120, 12000, 300
SYSTEM = ("You are a coding agent. Use the tools to read and write files and run commands; "
          "commands run in your workspace directory. Be economical: no explanations.")
TOOLS = [
    {"type": "function", "function": {"name": "read_file", "description": "Read a workspace file.",
        "parameters": {"type": "object", "properties": {"path": {"type": "string"}}, "required": ["path"]}}},
    {"type": "function", "function": {"name": "write_file", "description": "Create or overwrite a workspace file.",
        "parameters": {"type": "object", "properties": {"path": {"type": "string"}, "content": {"type": "string"}},
                       "required": ["path", "content"]}}},
    {"type": "function", "function": {"name": "run_command",
        "description": "Run a shell command in the workspace (pipes allowed), 300 s timeout.",
        "parameters": {"type": "object", "properties": {"command": {"type": "string"}}, "required": ["command"]}}},
]


class Workspace:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.env = {k: v for k, v in os.environ.items() if "KEY" not in k and "TOKEN" not in k}

    def path(self, rel: str) -> Path:
        p = (self.root / rel).resolve()
        if not str(p).startswith(str(self.root)):
            raise PermissionError(f"path escapes workspace: {rel}")
        return p

    def call(self, name: str, a: dict) -> str:
        try:
            if name == "read_file":
                p = self.path(a["path"])
                return p.read_text(errors="replace")[:MAX_OUT * 3] if p.exists() else f"ERROR: no such file: {a['path']}"
            if name == "write_file":
                p = self.path(a["path"]); p.parent.mkdir(parents=True, exist_ok=True); p.write_text(a["content"])
                return f"wrote {len(a['content'])} chars to {a['path']}"
            if name == "run_command":
                r = subprocess.run(a["command"], shell=True, cwd=self.root, env=self.env,
                                   capture_output=True, text=True, timeout=TIMEOUT_S)
                out = r.stdout + (("\n[stderr]\n" + r.stderr) if r.stderr else "")
                return f"[exit {r.returncode}]\n" + (out[:MAX_OUT] + "\n...[truncated]" if len(out) > MAX_OUT else out)
            return f"ERROR: unknown tool {name}"
        except subprocess.TimeoutExpired:
            return f"ERROR: command timed out after {TIMEOUT_S}s"
        except Exception as e:  # tool errors go back to the model
            return f"ERROR: {type(e).__name__}: {e}"


def complete(model, messages, key):
    body = json.dumps({"model": model, "messages": messages, "tools": TOOLS, "temperature": 0,
                       "max_tokens": 32768}).encode()
    for attempt in range(6):
        req = urllib.request.Request(API, data=body, headers={"Authorization": f"Bearer {key}",
                                                              "Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=900) as r:
                return json.loads(r.read())
        except urllib.error.HTTPError as e:
            if e.code not in (429, 500, 502, 503, 504):
                raise RuntimeError(f"HTTP {e.code}: {e.read()[:300]!r}")
        except (urllib.error.URLError, TimeoutError):
            pass
        time.sleep(15 * (attempt + 1))
    raise RuntimeError("z.ai unreachable after retries")


def main(task, lang, arm, seed, model):
    key = os.environ["GLM_API_KEY"]
    label = model.replace(".", "").replace("-", "")  # glm-5.1 -> glm51, glm-4.7-flash -> glm47flash
    subagent.prep(task, lang, arm, seed, label)
    run_id = f"{task}-{lang}-{arm}-{label}-s{seed}"
    rdir = RUNS / run_id
    ws = Workspace(rdir / "ws")
    messages = [{"role": "system", "content": SYSTEM},
                {"role": "user", "content": (rdir / "ws" / "BRIEF.txt").read_text()}]
    tot = {"input_tokens": 0, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0, "output_tokens": 0}
    calls = nudges = 0
    t0 = time.time()
    with open(rdir / "transcript.jsonl", "w") as log:
        for turn in range(1, MAX_TURNS + 1):
            resp = complete(model, messages, key)
            u = resp.get("usage") or {}
            cached = (u.get("prompt_tokens_details") or {}).get("cached_tokens", 0) or 0
            tot["input_tokens"] += (u.get("prompt_tokens", 0) or 0) - cached
            tot["cache_read_input_tokens"] += cached
            tot["output_tokens"] += u.get("completion_tokens", 0) or 0
            calls += 1
            msg = resp["choices"][0]["message"]
            tcs = msg.get("tool_calls") or []
            log.write(json.dumps({"turn": turn, "usage": u, "content": msg.get("content"),
                                  "reasoning": msg.get("reasoning_content"), "tool_calls": tcs}) + "\n")
            log.flush()
            messages.append({"role": "assistant", "content": msg.get("content") or "", "tool_calls": tcs} if tcs
                            else {"role": "assistant", "content": msg.get("content") or ""})
            if not tcs:
                st = json.loads((rdir / "stage.json").read_text()) if (rdir / "stage.json").exists() else {"i": 0}
                if st["i"] >= 3 or nudges >= 3:
                    break
                nudges += 1
                messages.append({"role": "user", "content": "Not finished: make ./test.sh pass, then run ./next "
                                 "and apply each change request until ./next says there are no more."})
                continue
            for tc in tcs:
                try:
                    args = json.loads(tc["function"]["arguments"] or "{}")
                except json.JSONDecodeError as e:
                    out = f"ERROR: tool arguments are not valid JSON: {e}"
                else:
                    out = ws.call(tc["function"]["name"], args)
                messages.append({"role": "tool", "tool_call_id": tc["id"], "content": out})
    meta = json.loads((rdir / "meta.json").read_text())
    st = json.loads((rdir / "stage.json").read_text()) if (rdir / "stage.json").exists() else {"i": 0, "log": []}
    meta["stages"] = [{"stage": n, "is_error": False, "turns": 0, "usage": {}, "wall_s": 0}
                      for n in ["base", "cr1", "cr2"][:st["i"]]]
    if meta["stages"]:
        meta["stages"][0]["wall_s"] = round(time.time() - t0, 1)
        meta["stages"][0]["turns"] = calls
    meta["next_calls"] = len(st["log"])
    meta["usage_exact"] = {**tot, "api_calls": calls}
    (rdir / "meta.json").write_text(json.dumps(meta, indent=1))
    r = check.score(rdir, meta)
    print(json.dumps({"run": run_id, "stages": st["i"], "hidden": r["hidden"] and r["hidden"]["passed"],
                      "spec_ok": (r["spec_drift"] or {}).get("ok"), "out": tot["output_tokens"], "calls": calls}))


if __name__ == "__main__":
    main(*sys.argv[1:6])
