"""Workspace templates: one per (arm, lang). Both arms get the same build/run
scripts; they differ only in how the spec and tests are written."""
import json, os, stat
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent  # the backbone package
# The default macOS SDK here lacks libc++ headers; use the newest SDK that has them.
SDK = next((str(d) for d in sorted(Path("/Library/Developer/CommandLineTools/SDKs").glob("MacOSX*.*.sdk"), reverse=True)
            if (d / "usr/include/c++/v1/iostream").exists()), "")
CXX = f"c++ -isysroot {SDK} -nostdinc++ -isystem {SDK}/usr/include/c++/v1 -std=c++20" if SDK else "c++ -std=c++20"

RUN = {"py": "exec python3 main.py",
       "cpp": "exec ./prog",
       "lean": "exec .lake/build/bin/prog",
       "ts": "exec node dist/main.js"}
BUILD = {"py": "python3 -m py_compile main.py",
         "cpp": f"{CXX} -O1 -o prog *.cpp",
         "lean": "lake build prog",
         "ts": "[ -d node_modules ] || npm install --no-audit --no-fund --loglevel=error\nnpx tsc -p ."}
SRC = {"py": "main.py", "cpp": "*.cpp (C++20, no third-party libraries)",
       "ts": ("TypeScript under src/ (tsc --strict, no runtime dependencies): the logic in src/model.ts, "
              "src/main.ts the stdin/stdout entry over it, and the web page index.html + src/page.ts "
              "importing the SAME src/model.ts, served by `npm start`"),
       "lean": ("Lean 4 core only (Lean.Json is available): the logic in Prog.lean, theorems about it in "
                "Evidence.lean (it imports LeanSpec, Spec and Prog; nothing the program runs depends on it), "
                "Main.lean only does IO (`import Prog`, `def main : IO Unit`)")}

IO_RULE = ("The program reads one JSON value on stdin and writes one JSON value on stdout. "
           "`./build` builds it and `./run` runs it.")

# Arms: `md` (SPEC.md + hand-written test.sh), `core` (Spec.lean, `Req.holds` examples),
# `logic` (Spec.lean, `IOReq` properties with examples attached). `lean` is the
# round-1..4 name of `core`.
LEAN_ARMS = ("lean", "core", "logic")

BRIEF = {
    "md": """Work in the current directory. Deliver:
1. SPEC.md - the requirements as R1..Rn, each with concrete input -> output examples.
2. The program in {src}. {io}
3. test.sh - tests for the program command in $PROG (default ./run). Run each test as
   printf '%s' "$input" | sh -c "$PROG" and compare the JSON output by value with
   ./jeq EXPECTED ACTUAL (exit 0 when equal; key order and spacing do not matter), print as the
   LAST line `TESTS passed=N failed=M`, exit 1 if any failed.
{proofs}Keep SPEC.md, program and tests consistent when change requests arrive.
{loop}""",
    "core": """Work in the current directory. Deliver:
1. Spec.lean - the requirements with examples, in lean-spec: one @[requirement] def each. Run `lake exe spec help` first.
   `lake exe spec check` must pass.
2. The program in {src}. {io}
3. Tests are your spec examples: ./test.sh runs them against $PROG (default ./run). Write no other tests.
{proofs}Keep Spec.lean and program consistent when change requests arrive.
{loop}""",
    "logic": """Work in the current directory. Deliver:
1. Spec.lean - the requirements in lean-spec: one @[requirement] def each. Run `lake exe spec help` first.
   Where the task states a property of input and output, write it as `IOReq pre post` (Bool functions
   over Json) and attach its examples with @[example R], at least one each; use `Req.holds [examples]`
   only where no property can be stated. `lake exe spec check` must pass.
2. The program in {src}. {io}
3. Tests are your spec examples: ./test.sh runs them against $PROG (default ./run), and `check` runs
   each IOReq's post on its examples. Write no other tests.
{proofs}Keep Spec.lean and program consistent when change requests arrive.
{loop}""",
}
BRIEF["lean"] = BRIEF["core"]

CHANGE = "Apply this change request to spec, program and tests.\n\n"

# Every run must show each requirement correct: by tests, and (Lean target) by what the
# bar asks for. The bar is the author's: `tested` (the default), `evidenced` or `proved`.
EVIDENCE = {
    "md": ("4. Correctness: show every requirement is met, by tests in test.sh{orproofs}.\n"
           "   Under each requirement in SPEC.md, name the tests{andproofs} that show it.\n"),
    "lean": ("4. Correctness: every requirement is shown by its examples (./test.sh runs them){orproofs}.\n"),
}
PROOF_TEXT = {
    "md": (" or by theorems in Evidence.lean (no sorry) that hold for all inputs (state them with ∀;\n"
           "   single-input checks are tests, not proofs)", " and theorems"),
    "lean": {
        None: ("", ""),
        "tested": ("", ""),
        "evidenced": (" and, where a property of your functions can be stated, by one theorem per requirement in\n"
                      "   Evidence.lean that holds for all inputs (∀ over an input; single-input checks belong in examples),\n"
                      "   tagged `@[evidence R]` with the requirement's name. A proof you cannot close stays as `sorry`: it is\n"
                      "   a sketch, listed by `check` and never counted. Spec.lean says `spec_bar evidenced`; `lake exe spec\n"
                      "   report ./run` says per row whether it meets the bar", ""),
        "proved": (" and by proof: in Evidence.lean, a `@[shipped]` Lean value of a signature your requirements are\n"
                   "   stated over and a `@[satisfies]` theorem per requirement, `@[evidence]` theorems where a requirement\n"
                   "   cannot be stated that way. A proof you cannot close stays as `sorry`: a sketch, listed and never\n"
                   "   counted. Spec.lean says `spec_bar proved`; `lake exe spec report ./run` says per row whether it\n"
                   "   meets the bar", ""),
    },
}


def evidence(arm, lang, bar=None):
    key = "lean" if arm in LEAN_ARMS else arm
    if lang != "lean":
        orp, andp = "", ""
    elif key == "md":
        orp, andp = PROOF_TEXT["md"]
    else:
        orp, andp = PROOF_TEXT["lean"][bar]
    return EVIDENCE[key].format(orproofs=orp, andproofs=andp)


JEQ = ("#!/bin/sh\n# JSON equality by value: ./jeq EXPECTED ACTUAL\n"
       "exec python3 -c 'import json,sys\n"
       "try: sys.exit(0 if json.loads(sys.argv[1]) == json.loads(sys.argv[2]) else 1)\n"
       "except ValueError: sys.exit(1)' \"$1\" \"$2\"\n")


SERVE = """// Static server for the page: `npm start` -> http://localhost:8080
import { createServer } from "node:http";
import { readFile } from "node:fs/promises";
import { extname, join, normalize } from "node:path";
const root = process.cwd(), port = Number(process.env.PORT ?? 8080);
const types = { ".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8", ".json": "application/json", ".map": "application/json" };
createServer(async (req, res) => {
  try {
    let p = join(root, normalize(new URL(req.url ?? "/", "http://x").pathname));
    if (p.endsWith("/")) p += "index.html";
    res.writeHead(200, { "content-type": types[extname(p)] ?? "application/octet-stream" });
    res.end(await readFile(p));
  } catch { res.writeHead(404); res.end("not found"); }
}).listen(port, () => console.log(`http://localhost:${port}`));
"""

LOOP = ("When ./test.sh passes, run ./next: it prints the next change request (apply it, then run ./next again)\n"
        "or tells you there are no more. Then reply DONE.")


def lakefile(arm, lang):
    lines = ["import Lake", "open Lake DSL", "", "package ws"]
    if arm in LEAN_ARMS:
        lines += [f'require «lean-spec» from "{ROOT}"', "", "lean_lib Spec",
                  "lean_exe spec where", "  root := `SpecMain"]
    if lang == "lean":
        lines += ["", "lean_lib Prog", "", "lean_exe prog where", "  root := `Main"]
        if arm in LEAN_ARMS:
            # Theorems live in Evidence; `spec` (check, statement, report) builds it, the
            # program and `spec-test` (what ./test.sh runs) do not, so a proof never
            # stops the loop.
            lines += ["", "lean_lib Evidence", "", "lean_exe «spec-test» where", "  root := `TestMain"]
    return "\n".join(lines) + "\n"


MAIN = "def main (args : List String) : IO UInt32 :=\n  LeanSpec.Core.cli spec% statement% args\n"


def make(ws: Path, task: str, arm: str, lang: str, bar=None):
    """Write the workspace for one run and return the brief. `bar` (tested, evidenced,
    proved or None for the library's default) is written into Spec.lean as `spec_bar`
    and picks the brief's proof paragraph on the Lean target."""
    ws.mkdir(parents=True)
    files = {"build": f"#!/bin/sh\nset -e\n{BUILD[lang]}\n", "run": f"#!/bin/sh\n{RUN[lang]}\n",
             "next": f"#!/bin/sh\nexec python3 {ROOT / 'bench' / 'stage.py'} {ws.resolve().parent}\n",
             "jeq": JEQ}
    if arm in LEAN_ARMS or lang == "lean":
        files["lakefile.lean"] = lakefile(arm, lang)
        files["lean-toolchain"] = (ROOT / "lean-toolchain").read_text()
    if arm in LEAN_ARMS:
        files["Spec.lean"] = ("import LeanSpec\nopen LeanSpec.Core Lean\n" +
                              (f"\nspec_bar {bar}\n" if bar else "") + "\n")
        if lang == "lean":
            files["SpecMain.lean"] = "import Evidence\n\n" + MAIN
            files["TestMain.lean"] = "import Spec\n\n" + MAIN
            files["test.sh"] = '#!/bin/sh\nexec lake exe spec-test test "${PROG:-./run}"\n'
        else:
            files["SpecMain.lean"] = "import Spec\n\n" + MAIN
            files["test.sh"] = '#!/bin/sh\nexec lake exe spec test "${PROG:-./run}"\n'
    if lang == "lean":
        files["Prog.lean"] = ""
        if arm in LEAN_ARMS:
            files["Evidence.lean"] = "import LeanSpec\nimport Spec\nimport Prog\n"
    if lang == "ts":
        files["package.json"] = json.dumps({"name": "ws", "private": True, "type": "module",
            "scripts": {"build": "tsc -p .", "start": "node serve.mjs"},
            "devDependencies": {"typescript": "^5.6.0", "@types/node": "^22.0.0"}}, indent=1) + "\n"
        files["tsconfig.json"] = json.dumps({"compilerOptions": {"target": "ES2022", "lib": ["ES2022", "DOM"],
            "module": "NodeNext", "moduleResolution": "NodeNext", "rootDir": "src", "outDir": "dist",
            "strict": True, "noUncheckedIndexedAccess": True, "noUnusedLocals": True, "noEmitOnError": True},
            "include": ["src"]}, indent=1) + "\n"
        files["serve.mjs"] = SERVE
    for name, text in files.items():
        p = ws / name
        p.write_text(text)
        if name in ("build", "run", "test.sh", "next", "jeq"):
            p.chmod(p.stat().st_mode | stat.S_IEXEC)
    return BRIEF[arm].format(src=SRC[lang], io=IO_RULE, proofs=evidence(arm, lang, bar), loop=LOOP)
