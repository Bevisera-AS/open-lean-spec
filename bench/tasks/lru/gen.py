"""Hidden cases: hand cases carry a hand-computed `expect`; random cases get their
output from the reference."""
import random


def cases():
    N = None
    hand = [
        (["R1"], {"capacity": 2, "ops": [["get", "a"], ["put", "a", 1], ["get", "a"]]}, [N, N, 1]),
        (["R1", "R2"], {"capacity": 2, "ops": [["put", "a", 1], ["put", "b", 2], ["get", "a"], ["put", "c", 3],
                                                ["get", "b"], ["get", "a"], ["get", "c"]]},
         [N, N, 1, "b", N, 1, 3]),
        (["R2"], {"capacity": 2, "ops": [["put", "a", 1], ["put", "b", 2], ["put", "a", 9], ["put", "c", 3],
                                         ["get", "a"], ["get", "b"]]},
         [N, N, N, "b", 9, N]),
        (["R2", "R4"], {"capacity": 1, "ops": [["put", "a", 1], ["put", "b", 2], ["get", "a"], ["get", "b"]]},
         [N, "a", N, 2]),
        (["R3", "R4"], {"capacity": 0, "ops": [["put", "a", 1], ["get", "a"], ["put", "a", 2]]}, ["a", N, "a"]),
        (["R5"], {"capacity": 3, "ops": [["put", "a", 1, 5], ["tick", 4], ["get", "a"], ["tick", 1], ["get", "a"]]},
         [N, N, 1, N, N]),
        (["R5"], {"capacity": 3, "ops": [["put", "a", 1, 2], ["put", "a", 2], ["tick", 100], ["get", "a"]]},
         [N, N, N, 2]),
        (["R5"], {"capacity": 3, "ops": [["put", "a", 1], ["put", "a", 2, 1], ["tick", 1], ["get", "a"]]},
         [N, N, N, N]),
        (["R5", "R1"], {"capacity": 2, "ops": [["put", "a", 1, 3], ["tick", 3], ["put", "a", 7], ["get", "a"]]},
         [N, N, N, 7]),
        (["R6"], {"capacity": 2, "ops": [["put", "a", 1], ["put", "b", 2, 1], ["tick", 1], ["put", "c", 3],
                                         ["get", "a"], ["get", "c"]]},
         [N, N, N, N, 1, 3]),
        (["R6"], {"capacity": 2, "ops": [["put", "a", 1, 1], ["put", "b", 2, 1], ["tick", 1], ["put", "c", 3],
                                         ["put", "d", 4], ["put", "e", 5]]},
         [N, N, N, N, N, "c"]),
        (["R6", "R2"], {"capacity": 2, "ops": [["put", "a", 1, 9], ["put", "b", 2], ["tick", 1], ["put", "c", 3]]},
         [N, N, N, "a"]),
    ]
    out = [{"req": r, "input": i, "expect": {"results": x}} for r, i, x in hand]
    rng = random.Random(3)
    for _ in range(18):
        keys = list("abcdef")[: rng.randint(2, 6)]
        ops = []
        for _ in range(rng.randint(8, 40)):
            c = rng.random()
            k = rng.choice(keys)
            if c < 0.4:
                ops.append(["get", k])
            elif c < 0.6:
                ops.append(["put", k, rng.randint(0, 99), rng.randint(1, 4)])
            elif c < 0.85:
                ops.append(["put", k, rng.randint(0, 99)])
            else:
                ops.append(["tick", rng.randint(1, 3)])
        out.append({"req": ["R1", "R2", "R4", "R5", "R6"], "input": {"capacity": rng.randint(0, 4), "ops": ops}})
    return out


def fuzz(rng):
    """One larger random input for differential fuzzing."""
    keys = list("abcdefgh")[: rng.randint(1, 8)]
    ops = []
    for _ in range(rng.randint(0, 80)):
        c, k = rng.random(), rng.choice(keys)
        if c < 0.35:
            ops.append(["get", k])
        elif c < 0.55:
            ops.append(["put", k, rng.randint(-5, 99), rng.randint(1, 5)])
        elif c < 0.85:
            ops.append(["put", k, rng.randint(-5, 99)])
        else:
            ops.append(["tick", rng.randint(1, 4)])
    return {"capacity": rng.randint(0, 5), "ops": ops}
