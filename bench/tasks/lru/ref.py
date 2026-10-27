"""Reference solution (final stage). MUTANT=m1|m2|m3 selects a planted bug."""
import json, os, sys
from collections import OrderedDict

M = os.environ.get("MUTANT", "")


def solve(d):
    cap = d["capacity"]
    store = OrderedDict()  # key -> (value, expires_at or None); last = most recent
    clock, res = 0, []

    def expired(k):
        exp = store[k][1]
        return exp is not None and (clock > exp if M == "m2" else clock >= exp)

    for op in d["ops"]:
        if op[0] == "tick":
            clock += op[1]
            res.append(None)
        elif op[0] == "get":
            k = op[1]
            if k in store and expired(k):
                del store[k]
            if k in store:
                if M != "m1":
                    store.move_to_end(k)
                res.append(store[k][0])
            else:
                res.append(None)
        else:
            k, v = op[1], op[2]
            exp = clock + op[3] if len(op) > 3 else None
            if k in store and expired(k):
                del store[k]
            if k in store:
                store[k] = (v, exp)
                store.move_to_end(k)
                res.append(None)
                continue
            if cap == 0:
                res.append(k)
                continue
            evicted = None
            if len(store) >= cap:
                for e in [e for e in store if expired(e)]:
                    del store[e]
                    if M == "m3":
                        evicted = e
            if len(store) >= cap:
                evicted, _ = store.popitem(last=False)
            store[k] = (v, exp)
            res.append(evicted)
    return {"results": res}


if __name__ == "__main__":
    print(json.dumps(solve(json.load(sys.stdin))))
