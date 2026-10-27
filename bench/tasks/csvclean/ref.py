"""Reference solution (final stage). MUTANT=m1|m2|m3 selects a planted bug."""
import json, os, re, sys

M = os.environ.get("MUTANT", "")


def records(text):
    """Yield (start_line, fields, blank) for each record."""
    i, line, n = 0, 1, len(text)
    while i < n:
        start, fields, blank = line, [], True
        while True:
            if i < n and text[i] == '"':
                blank, i, buf = False, i + 1, []
                while i < n:
                    if text[i] == '"':
                        if i + 1 < n and text[i + 1] == '"':
                            buf.append('"'); i += 2; continue
                        i += 1; break
                    if text[i] == "\n":
                        line += 1
                    buf.append(text[i]); i += 1
                f = "".join(buf)
                fields.append(f.strip(" ") if M == "m1" else f)
            else:
                j = i
                while j < n and text[j] != "," and text[j] != "\n" and text[j:j + 2] != "\r\n":
                    j += 1
                if text[i:j] != "":
                    blank = False
                fields.append(text[i:j].strip(" ")); i = j
            if i < n and text[i] == ",":
                blank, i = False, i + 1
                continue
            break
        if text[i:i + 2] == "\r\n":
            i += 1
        if i < n and text[i] == "\n":
            i += 1
        line += 1
        yield start, fields, blank and fields == [""]


INT = re.compile(r"-?[0-9]+\Z")


def solve(d):
    types, keys = d.get("types", {}), d.get("dedupe_on")
    rows, errors, header, seen, dup, idx = [], [], None, {}, 0, 0
    for start, fields, blank in records(d["csv"]):
        if blank:
            continue
        if header is None:
            header = fields
            continue
        idx += 1
        bad = len(fields) != len(header)
        row = {}
        if not bad:
            for h, v in zip(header, fields):
                t = types.get(h)
                if t == "int":
                    if not INT.match(v):
                        bad = True; break
                    v = int(v)
                elif t == "bool":
                    if v not in ("true", "false"):
                        bad = True; break
                    v = v == "true"
                row[h] = v
        if bad:
            errors.append(idx + 1 if M == "m2" else start)
            continue
        if keys:
            k = json.dumps([row.get(c) for c in keys])
            if k in seen:
                dup += 1
                if M == "m3":
                    rows[seen[k]] = row
                continue
            seen[k] = len(rows)
        rows.append(row)
    return {"rows": rows, "errors": errors, "duplicates": dup}


if __name__ == "__main__":
    print(json.dumps(solve(json.load(sys.stdin))))
