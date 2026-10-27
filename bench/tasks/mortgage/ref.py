"""Reference solution (final stage). MUTANT=m1|m2|m3 selects a planted bug."""
import json, os, sys
from fractions import Fraction

M = os.environ.get("MUTANT", "")


def half_up(x: Fraction) -> int:
    return (x.numerator * 2 + x.denominator) // (2 * x.denominator)


def payment(p, bp, n):
    if bp == 0:
        return half_up(Fraction(p, n))
    r = Fraction(bp, 120000)
    return half_up(p * r / (1 - (1 + r) ** -n))


def solve(d):
    p, bp, n = d["principal"], d["annual_rate_bp"], d["months"]
    k = d.get("interest_only_months", 0)
    extra = {}
    for e in d.get("extra", []):
        extra[e["month"]] = extra.get(e["month"], 0) + e["amount"]
    pay = payment(p, bp, n if M == "m3" else n - k)
    bal, sched, total = p, [], 0
    for m in range(1, n + 1):
        x = Fraction(bal * bp, 120000)
        i = int(x) if M == "m1" else half_up(x)
        if m <= k:
            pr = 0
        elif m == n or pay - i >= bal:
            pr = bal
        else:
            pr = pay - i
        bal -= pr
        ex = extra.get(m, 0)
        if M != "m2":
            ex = min(ex, bal)
        bal -= ex
        total += i
        sched.append({"month": m, "interest": i, "principal": pr + ex, "balance": bal})
        if bal <= 0:
            break
    return {"payment": pay, "schedule": sched, "total_interest": total}


if __name__ == "__main__":
    print(json.dumps(solve(json.load(sys.stdin))))
