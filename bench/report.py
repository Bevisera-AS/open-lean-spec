"""Summarise results.jsonl per (lang, arm): pass rates, drift, strength, coverage, tokens.

  python3 bench/report.py [--model haiku]
"""
import json, statistics as st, sys
from collections import defaultdict
from pathlib import Path

RES = Path(__file__).parent / "results" / "results.jsonl"


def rate(xs):
    xs = [x for x in xs if x is not None]
    return f"{sum(xs)}/{len(xs)}" if xs else "-"


def main():
    model = sys.argv[sys.argv.index("--model") + 1] if "--model" in sys.argv else None
    latest = {}
    for line in RES.read_text().splitlines():
        r = json.loads(line)
        if model is None or r["model"] == model:
            latest[r["run"]] = r  # last score wins
    groups = defaultdict(list)
    for r in latest.values():
        groups[(r["lang"], r["arm"] + ("+gate" if r.get("gate") else ""))].append(r)
    cols = ["lang", "arm", "n", "hidden%", "repr_ok", "spec_ok", "mut_kill", "cov%", "out_tok", "tot_tok", "turns", "usd"]
    print(" ".join(f"{c:>9}" for c in cols))
    for (lang, arm), rs in sorted(groups.items()):
        hid = [r["hidden"]["passed"] / r["hidden"]["total"] for r in rs if r["hidden"]]
        kills = [sum(r["strength"].values()) / 3 for r in rs if r["strength"]]
        cov = [r["coverage"] for r in rs if r["coverage"] is not None]
        u = [r["usage"] for r in rs]
        tot = [x.get("total_tokens") or x["input_tokens"] + x["cache_creation_input_tokens"]
               + x["cache_read_input_tokens"] + x["output_tokens"] for x in u]
        row = [lang, arm, len(rs),
               f"{100 * st.mean(hid):.0f}" if hid else "-",
               rate([(r["repr_drift"] or {}).get("ok") for r in rs]),
               rate([(r["spec_drift"] or {}).get("ok") for r in rs]),
               f"{100 * st.mean(kills):.0f}%" if kills else "-",
               f"{st.mean(cov):.0f}" if cov else "-",
               f"{st.median([x['output_tokens'] for x in u]):.0f}",
               f"{st.median(tot):.0f}",
               f"{st.median([x['turns'] for x in u]):.0f}",
               f"{sum(x['cost_usd'] for x in u):.2f}"]
        print(" ".join(f"{str(c):>9}" for c in row))


if __name__ == "__main__":
    main()
