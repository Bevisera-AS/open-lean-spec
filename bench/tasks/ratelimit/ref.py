"""Reference solution (final stage). MUTANT=m1|m2|m3 selects a planted bug."""
import json, os, sys

M = os.environ.get("MUTANT", "")


def solve(d):
    limit, window = d["limit"], d["window"]
    overrides = d.get("overrides", {})
    seen = {}  # user -> times that counted
    allowed, denied = [], {}
    for e in d["events"]:
        t, u = e["t"], e["user"]
        lim = overrides.get(u, limit)
        lo = t - window
        n = sum(1 for s in seen.get(u, []) if (s >= lo if M == "m1" else s > lo) and s <= t)
        ok = n < lim
        allowed.append(ok)
        if ok or M == "m2":
            seen.setdefault(u, []).append(t)
        if not ok:
            denied[u] = denied.get(u, 0) + 1
        elif M == "m3":
            denied.setdefault(u, 0)
    return {"allowed": allowed, "denied": denied}


if __name__ == "__main__":
    print(json.dumps(solve(json.load(sys.stdin))))
