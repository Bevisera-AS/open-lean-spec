"""Hidden cases: hand cases carry a hand-computed `expect`; random cases get their
output from the reference."""
import random


def cases():
    hand = [
        (["R1", "R2"], {"csv": "a,b\n1,2\n"}, [{"a": "1", "b": "2"}], [], 0),
        (["R1"], {"csv": 'name,note\nx,"hi, there"\ny,"say ""yo"""\n'},
         [{"name": "x", "note": "hi, there"}, {"name": "y", "note": 'say "yo"'}], [], 0),
        (["R1", "R3"], {"csv": 'k,v\n1,"two\nlines"\n2,x,extra\n'},
         [{"k": "1", "v": "two\nlines"}], [4], 0),
        (["R1"], {"csv": 'k,v\n1," padded "\n'}, [{"k": "1", "v": " padded "}], [], 0),
        (["R2"], {"csv": " a , b \r\n 1 ,  2 \r\n\r\n3,4"}, [{"a": "1", "b": "2"}, {"a": "3", "b": "4"}], [], 0),
        (["R2", "R3"], {"csv": "a,b\n\n1\n\n2,3\n"}, [{"a": "2", "b": "3"}], [3], 0),
        (["R3"], {"csv": 'a,b\n"x\ny\nz"\n1,2,3\n4,5\n'}, [{"a": "4", "b": "5"}], [2, 5], 0),
        (["R2"], {"csv": "a,b\n1,\n"}, [{"a": "1", "b": ""}], [], 0),
        (["R4"], {"csv": "n,ok\n-12,true\n3,false\n", "types": {"n": "int", "ok": "bool"}},
         [{"n": -12, "ok": True}, {"n": 3, "ok": False}], [], 0),
        (["R4", "R3"], {"csv": "n,ok\n1.5,true\nx,true\n2,True\n7,true\n", "types": {"n": "int", "ok": "bool"}},
         [{"n": 7, "ok": True}], [2, 3, 4], 0),
        (["R4"], {"csv": "n\n\"5\"\n+5\n-\n", "types": {"n": "int"}}, [{"n": 5}], [3, 4], 0),
        (["R5"], {"csv": "id,v\n1,a\n2,b\n1,c\n", "dedupe_on": ["id"]},
         [{"id": "1", "v": "a"}, {"id": "2", "v": "b"}], [], 1),
        (["R5", "R4"], {"csv": "id,v\n01,a\n1,b\n1,c\n", "types": {"id": "int"}, "dedupe_on": ["id", "v"]},
         [{"id": 1, "v": "a"}, {"id": 1, "v": "b"}, {"id": 1, "v": "c"}], [], 0),
        (["R5", "R4"], {"csv": "id,v\n01,a\n1,a\nz,a\n", "types": {"id": "int"}, "dedupe_on": ["id"]},
         [{"id": 1, "v": "a"}], [4], 1),
    ]
    out = [{"req": r, "input": i, "expect": {"rows": rows, "errors": e, "duplicates": dup}}
           for r, i, rows, e, dup in hand]
    rng = random.Random(5)
    vals = ["1", "2", "-3", " x ", "true", "false", '"q,1"', '"a""b"', '"multi\nline"', "", "07"]
    for _ in range(16):
        cols = ["c%d" % j for j in range(rng.randint(1, 3))]
        lines = [",".join(cols)]
        for _ in range(rng.randint(2, 9)):
            if rng.random() < 0.1:
                lines.append("")
                continue
            w = len(cols) + (rng.choice([-1, 1]) if rng.random() < 0.15 else 0)
            lines.append(",".join(rng.choice(vals) for _ in range(max(w, 1))))
        d = {"csv": rng.choice(["\n", "\r\n"]).join(lines) + rng.choice(["", "\n"])}
        if rng.random() < 0.5:
            d["types"] = {rng.choice(cols): rng.choice(["int", "bool"])}
        if rng.random() < 0.5:
            d["dedupe_on"] = [rng.choice(cols)]
        out.append({"req": ["R1", "R2", "R3", "R4", "R5"], "input": d})
    return out


def fuzz(rng):
    """One random input for differential fuzzing (no stray text after a closing quote)."""
    vals = ["1", "-2", "007", " x ", "true", "false", "True", '"q,1"', '"a""b"', '"two\nlines"', '" sp "', "", "-", "1.5"]
    cols = ["c%d" % j for j in range(rng.randint(1, 4))]
    lines = [",".join(cols)]
    for _ in range(rng.randint(0, 12)):
        if rng.random() < 0.1:
            lines.append("")
            continue
        w = len(cols) + (rng.choice([-1, 1]) if rng.random() < 0.15 else 0)
        lines.append(",".join(rng.choice(vals) for _ in range(max(w, 1))))
    d = {"csv": rng.choice(["\n", "\r\n"]).join(lines) + rng.choice(["", "\n"])}
    if rng.random() < 0.5:
        d["types"] = {c: rng.choice(["int", "bool"]) for c in rng.sample(cols, rng.randint(1, len(cols)))}
    if rng.random() < 0.5:
        d["dedupe_on"] = rng.sample(cols, rng.randint(1, len(cols)))
    return d
