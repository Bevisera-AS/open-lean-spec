"""Exact token usage of a subagent run from its transcript (deduplicated by
message id), stored as the run's usage so check.py and report.py pick it up.

  python3 bench/usage.py RUN_ID TRANSCRIPT_JSONL
"""
import json, shutil, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from run import RUNS

KEYS = ["input_tokens", "cache_creation_input_tokens", "cache_read_input_tokens", "output_tokens"]


def usage(path):
    seen, tot, calls = {}, dict.fromkeys(KEYS, 0), 0
    for line in open(path):
        m = json.loads(line).get("message")
        if isinstance(m, dict) and m.get("usage") and m.get("id") not in seen:
            seen[m.get("id")] = True
            calls += 1
            for k in KEYS:
                tot[k] += m["usage"].get(k) or 0
    return tot, calls


if __name__ == "__main__":
    run_id, src = sys.argv[1], sys.argv[2]
    rdir = RUNS / run_id
    shutil.copy(src, rdir / "transcript.jsonl")
    tot, calls = usage(rdir / "transcript.jsonl")
    meta = json.loads((rdir / "meta.json").read_text())
    meta["usage_exact"] = {**tot, "api_calls": calls}
    (rdir / "meta.json").write_text(json.dumps(meta, indent=1))
    print(run_id, meta["usage_exact"])
