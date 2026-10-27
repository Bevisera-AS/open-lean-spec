"""Round summary over run dirs: per (lang, arm) and per task, md vs lean.

  python3 bench/analyze.py SEED [SEED ...] [--fuzz-log FILE]
  arms: md, core (rounds 1..4 called it lean), logic, each +gate when a reviewer gated the spec
  python3 bench/analyze.py r3 ...   round 3 = seeds 21, 22 + round-2 md runs it reused
"""
import json, re, statistics as st, sys
from collections import defaultdict
from pathlib import Path

RUNS = Path(__file__).resolve().parent.parent.parent / "lean-spec-core-runs"
PRICE = {"input_tokens": 1, "cache_creation_input_tokens": 1.25, "cache_read_input_tokens": 0.1, "output_tokens": 5}


def load(seeds, fuzz):
    rows = []
    for d in sorted(RUNS.iterdir()):
        if not (d / "result.json").exists():
            continue
        r = json.loads((d / "result.json").read_text())
        task, lang, arm, seed = r["task"], r["lang"], r["arm"], str(r["seed"])
        if arm == "lean":
            arm = r["arm"] = "core"  # rounds 1..4 called the Req.holds arm `lean`
        if r.get("gate"):
            arm = r["arm"] = arm + "+gate"
        reused = "r3" in seeds and seed in ("11", "12") and arm == "md" and lang != "lean" and task != "csvclean"
        if seed not in seeds and not reused and not ("r3" in seeds and seed in ("21", "22")):
            continue
        u = r["usage"]
        r["cost"] = sum(PRICE[k] * (u.get(k) or 0) for k in PRICE) / 1000
        r["fuzz_bad"] = fuzz.get(d.name)
        ev = (r.get("spec_check") or {}).get("evidence") or {}
        r["evidence_reqs"] = len(ev)
        r["general_reqs"] = sum(1 for v in ev.values() if isinstance(v, dict) and v.get("general"))
        rows.append(r)
    return rows


def summary(rs):
    hid = [r["hidden"]["passed"] / r["hidden"]["total"] for r in rs if r["hidden"]]
    kills = [sum(r["strength"].values()) / 3 for r in rs if r["strength"]]
    cov = [r["coverage"] for r in rs if r["coverage"] is not None]
    fz = [r["fuzz_bad"] for r in rs if r["fuzz_bad"] is not None]
    return {
        "n": len(rs),
        "done": sum(r["completed"] for r in rs),
        "hidden%": round(100 * st.mean(hid), 1) if hid else None,
        "all_hidden": sum(1 for r in rs if r["hidden"] and r["hidden"]["passed"] == r["hidden"]["total"]),
        "fuzz_clean": sum(1 for x in fz if x == 0),
        "repr_ok": sum(1 for r in rs if (r["repr_drift"] or {}).get("ok")),
        "spec_ok": sum(1 for r in rs if (r["spec_drift"] or {}).get("ok")),
        "kill%": round(100 * st.mean(kills)) if kills else None,
        "cov%": round(st.mean(cov)) if cov else None,
        "thm": sum((r["lean"] or {}).get("theorems", 0) for r in rs),
        "gen_thm": sum((r["lean"] or {}).get("general", 0) for r in rs),
        "ev_reqs": sum(r["evidence_reqs"] for r in rs),
        "gen_reqs": sum(r.get("general_reqs", 0) for r in rs),
        "out_k": round(st.mean(r["usage"]["output_tokens"] for r in rs) / 1000, 1),
        "cost_k": round(st.mean(r["cost"] for r in rs)),
        "wall_s": round(st.mean(r["usage"]["wall_s"] for r in rs)),
        "test_b": round(st.mean(r["sizes"]["tests"] for r in rs)),
    }


def table(title, groups):
    print(f"\n## {title}")
    keys = None
    for g, rs in groups:
        s = summary(rs)
        if keys is None:
            keys = list(s)
            print(f"{'group':16}" + "".join(f"{k:>11}" for k in keys))
        print(f"{g:16}" + "".join(f"{str(s[k]):>11}" for k in keys))


def main():
    args = sys.argv[1:]
    fuzz = {}
    if "--fuzz-log" in args:
        i = args.index("--fuzz-log")
        for line in open(args[i + 1]):
            if line.startswith('{"run"') and '"mismatches"' in line:
                m = re.search(r'"run": "([^"]+)".*"mismatches": (\d+)', line)
                fuzz[m.group(1)] = int(m.group(2))
        args = args[:i] + args[i + 2:]
    rows = load(set(args), fuzz)
    by = defaultdict(list)
    for r in rows:
        by[("all", r["arm"])].append(r)
        by[(r["lang"], r["arm"])].append(r)
        by[(r["task"], r["arm"])].append(r)
    order = ["all", "py", "cpp", "lean", "ratelimit", "mortgage", "lru", "csvclean"]
    arms = ["md", "core", "logic", "md+gate", "core+gate", "logic+gate"]
    table("by arm, language and task", [(f"{k}/{a}", by[(k, a)]) for k in order for a in arms if by[(k, a)]])


if __name__ == "__main__":
    main()
