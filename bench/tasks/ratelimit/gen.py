"""Hidden cases: hand cases carry a hand-computed `expect` that the reference must
reproduce; random cases get their output from the reference."""
import random


def ev(*pairs):
    return [{"t": t, "user": u} for t, u in pairs]


def cases():
    T, F = True, False
    hand = [
        (["R1"], {"limit": 2, "window": 10, "events": ev((0, "a"), (1, "a"), (2, "a"))},
         {"allowed": [T, T, F], "denied": {"a": 1}}),
        (["R1"], {"limit": 1, "window": 10, "events": ev((0, "a"), (10, "a"))},
         {"allowed": [T, T], "denied": {}}),
        (["R1"], {"limit": 1, "window": 10, "events": ev((0, "a"), (9, "a"))},
         {"allowed": [T, F], "denied": {"a": 1}}),
        (["R1"], {"limit": 2, "window": 5, "events": ev((3, "a"), (3, "a"), (3, "a"))},
         {"allowed": [T, T, F], "denied": {"a": 1}}),
        (["R2"], {"limit": 1, "window": 10, "events": ev((0, "a"), (5, "a"), (12, "a"))},
         {"allowed": [T, F, T], "denied": {"a": 1}}),
        (["R2"], {"limit": 2, "window": 4, "events": ev((0, "a"), (1, "a"), (2, "a"), (3, "a"), (4, "a"), (5, "a"))},
         {"allowed": [T, T, F, F, T, T], "denied": {"a": 2}}),
        (["R3"], {"limit": 1, "window": 10, "events": ev((0, "a"), (0, "b"), (1, "a"), (1, "b"))},
         {"allowed": [T, T, F, F], "denied": {"a": 1, "b": 1}}),
        (["R4"], {"limit": 0, "window": 3, "events": ev((0, "a"), (100, "a"))},
         {"allowed": [F, F], "denied": {"a": 2}}),
        (["R4"], {"limit": 3, "window": 3, "events": []}, {"allowed": [], "denied": {}}),
        (["R5"], {"limit": 1, "window": 10, "overrides": {"vip": 3},
                  "events": ev((0, "vip"), (1, "vip"), (2, "vip"), (3, "vip"), (3, "x"), (4, "x"))},
         {"allowed": [T, T, T, F, T, F], "denied": {"vip": 1, "x": 1}}),
        (["R5", "R4"], {"limit": 5, "window": 10, "overrides": {"blocked": 0},
                        "events": ev((0, "blocked"), (0, "ok"))},
         {"allowed": [F, T], "denied": {"blocked": 1}}),
        (["R6"], {"limit": 1, "window": 2, "events": ev((0, "a"), (0, "b"), (1, "a"), (5, "b"))},
         {"allowed": [T, T, F, T], "denied": {"a": 1}}),
    ]
    out = [{"req": r, "input": i, "expect": x} for r, i, x in hand]
    rng = random.Random(7)
    for _ in range(18):
        users = ["a", "b", "c"][: rng.randint(1, 3)]
        t, evs = 0, []
        for _ in range(rng.randint(5, 30)):
            t += rng.choice([0, 0, 1, 1, 2, 3, 5])
            evs.append((t, rng.choice(users)))
        d = {"limit": rng.randint(0, 3), "window": rng.randint(1, 6), "events": ev(*evs)}
        if rng.random() < 0.5:
            d["overrides"] = {rng.choice(users): rng.randint(0, 4)}
        out.append({"req": ["R1", "R2", "R3", "R5", "R6"], "input": d})
    return out


def fuzz(rng):
    """One larger random input for differential fuzzing."""
    users = ["a", "b", "c", "d", "e"][: rng.randint(1, 5)]
    t, evs = rng.randint(-50, 50), []
    for _ in range(rng.randint(0, 120)):
        t += rng.choice([0, 0, 0, 1, 1, 2, 3, 7, 20])
        evs.append((t, rng.choice(users)))
    d = {"limit": rng.randint(0, 6), "window": rng.randint(1, 30), "events": ev(*evs)}
    if rng.random() < 0.6:
        d["overrides"] = {u: rng.randint(0, 6) for u in rng.sample(users, rng.randint(0, len(users)))}
    return d
