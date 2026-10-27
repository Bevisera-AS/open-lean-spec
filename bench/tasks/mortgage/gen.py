"""Hidden cases: hand cases carry a hand-computed `expect`; random cases get their
output from the reference."""
import random


def row(m, i, p, b):
    return {"month": m, "interest": i, "principal": p, "balance": b}


def cases():
    hand = [
        # 0 % over 3 months: 1000/3 = 333.33 -> 333; last month pays 334.
        (["R1", "R3"], {"principal": 1000, "annual_rate_bp": 0, "months": 3},
         {"payment": 333, "schedule": [row(1, 0, 333, 667), row(2, 0, 333, 334), row(3, 0, 334, 0)],
          "total_interest": 0}),
        # 0 %: 1000/6 = 166.67 -> 167; 5*167 = 835, last pays 165.
        (["R1", "R3"], {"principal": 1000, "annual_rate_bp": 0, "months": 6},
         {"payment": 167, "schedule": [row(1, 0, 167, 833), row(2, 0, 167, 666), row(3, 0, 167, 499),
                                       row(4, 0, 167, 332), row(5, 0, 167, 165), row(6, 0, 165, 0)],
          "total_interest": 0}),
        # 12 %/yr = 1 %/month, 1 month: interest 100, principal 10000.
        (["R1", "R2", "R3", "R4"], {"principal": 10000, "annual_rate_bp": 1200, "months": 1},
         {"payment": 10100, "schedule": [row(1, 100, 10000, 0)], "total_interest": 100}),
        # 1 %/month, 2 months: payment = 10000*0.01/(1-1.01^-2) = 5075.124... -> 5075.
        # m1: i=100, pr=4975, bal=5025; m2: i=50.25 -> 50, pr=5025 (last).
        (["R1", "R2", "R3", "R4"], {"principal": 10000, "annual_rate_bp": 1200, "months": 2},
         {"payment": 5075, "schedule": [row(1, 100, 4975, 5025), row(2, 50, 5025, 0)], "total_interest": 150}),
        # Half-up on interest: 150 * 600/120000 = 0.75 -> 1; 50 * 600/120000 = 0.25 -> 0.
        (["R2"], {"principal": 150, "annual_rate_bp": 600, "months": 3}, None),
        (["R2"], {"principal": 250, "annual_rate_bp": 2400, "months": 2}, None),
        # Extra pays off early; capped.
        (["R5"], {"principal": 1000, "annual_rate_bp": 0, "months": 4, "extra": [{"month": 1, "amount": 500}]},
         {"payment": 250, "schedule": [row(1, 0, 750, 250), row(2, 0, 250, 0)], "total_interest": 0}),
        (["R5"], {"principal": 1000, "annual_rate_bp": 0, "months": 4, "extra": [{"month": 2, "amount": 9999}]},
         {"payment": 250, "schedule": [row(1, 0, 250, 750), row(2, 0, 750, 0)], "total_interest": 0}),
        # Interest only: 0 %, k=2 of 4 -> payment 1000/2 = 500 from month 3.
        (["R6"], {"principal": 1000, "annual_rate_bp": 0, "months": 4, "interest_only_months": 2},
         {"payment": 500, "schedule": [row(1, 0, 0, 1000), row(2, 0, 0, 1000), row(3, 0, 500, 500), row(4, 0, 500, 0)],
          "total_interest": 0}),
        # Interest only at 1 %/month: months 1-2 pay 100 interest each.
        (["R6", "R2"], {"principal": 10000, "annual_rate_bp": 1200, "months": 3, "interest_only_months": 2},
         {"payment": 10100, "schedule": [row(1, 100, 0, 10000), row(2, 100, 0, 10000), row(3, 100, 10000, 0)],
          "total_interest": 300}),
        (["R6", "R5"], {"principal": 1000, "annual_rate_bp": 0, "months": 3, "interest_only_months": 1,
                        "extra": [{"month": 1, "amount": 400}]},
         {"payment": 500, "schedule": [row(1, 0, 400, 600), row(2, 0, 500, 100), row(3, 0, 100, 0)],
          "total_interest": 0}),
    ]
    out = [{"req": r, "input": i, **({"expect": x} if x else {})} for r, i, x in hand]
    rng = random.Random(11)
    for j in range(16):
        d = {"principal": rng.choice([1, 999, 250000, 1234567, 300000000]),
             "annual_rate_bp": rng.choice([0, 1, 199, 450, 525, 1999]),
             "months": rng.choice([1, 2, 7, 12, 36, 360])}
        if j % 3 == 1:
            d["extra"] = [{"month": rng.randint(1, d["months"]), "amount": rng.randint(1, d["principal"])}]
        if j % 4 == 2 and d["months"] > 1:
            d["interest_only_months"] = rng.randint(0, d["months"] - 1)
        out.append({"req": ["R1", "R2", "R3", "R4", "R5", "R6"], "input": d})
    return out


def fuzz(rng):
    """One random input for differential fuzzing."""
    n = rng.choice([1, 2, 3, 6, 12, 24, 120, 360])
    d = {"principal": rng.choice([1, 2, 7, rng.randint(1, 10**6), rng.randint(1, 10**9)]),
         "annual_rate_bp": rng.choice([0, 1, rng.randint(1, 3000)]), "months": n}
    if rng.random() < 0.4:
        d["extra"] = [{"month": m, "amount": rng.randint(1, d["principal"])}
                      for m in sorted(rng.sample(range(1, n + 1), min(n, rng.randint(1, 3))))]
    if rng.random() < 0.4 and n > 1:
        d["interest_only_months"] = rng.randint(0, n - 1)
    return d
