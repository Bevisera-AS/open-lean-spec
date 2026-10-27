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
       "lean": "exec .lake/build/bin/prog"}
BUILD = {"py": "python3 -m py_compile main.py",
         "cpp": f"{CXX} -O1 -o prog *.cpp",
         "lean": "lake build prog"}
SRC = {"py": "main.py", "cpp": "*.cpp (C++20, no third-party libraries)",
       "lean": ("Lean 4 core only (Lean.Json is available): logic and any theorems in Prog.lean, "
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

# Every run must show each requirement correct: by tests, or (Lean target) also by proofs.
EVIDENCE = {
    "md": ("4. Correctness: show every requirement is met, by tests in test.sh{orproofs}.\n"
           "   Under each requirement in SPEC.md, name the tests{andproofs} that show it.\n"),
    "lean": ("4. Correctness: every requirement is shown by its examples (./test.sh runs them){orproofs}.\n"),
}
PROOF_TEXT = {
    "md": (" or by theorems in Prog.lean (no sorry) that hold for all inputs (state them with ∀;\n"
           "   single-input checks are tests, not proofs)", " and theorems"),
    "lean": (" and, where the property can be stated about your functions, by theorems in Prog.lean\n"
             "   (it imports LeanSpec and Spec) that hold for all inputs (state them with ∀; single-input checks belong\n"
             "   in examples), tagged `@[evidence R]` with the requirement's name, no sorry; `lake exe spec check` lists them as general", ""),
}


def evidence(arm, lang):
    key = "lean" if arm in LEAN_ARMS else arm
    orp, andp = PROOF_TEXT[key] if lang == "lean" else ("", "")
    return EVIDENCE[key].format(orproofs=orp, andproofs=andp)


JEQ = ("#!/bin/sh\n# JSON equality by value: ./jeq EXPECTED ACTUAL\n"
       "exec python3 -c 'import json,sys\n"
       "try: sys.exit(0 if json.loads(sys.argv[1]) == json.loads(sys.argv[2]) else 1)\n"
       "except ValueError: sys.exit(1)' \"$1\" \"$2\"\n")


LOOP = ("When ./test.sh passes, run ./next: it prints the next change request (apply it, then run ./next again)\n"
        "or tells you there are no more. Then reply DONE.")


def lakefile(arm, lang):
    lines = ["import Lake", "open Lake DSL", "", "package ws"]
    if arm in LEAN_ARMS:
        lines += [f'require «lean-spec» from "{ROOT}"', "", "lean_lib Spec",
                  "lean_exe spec where", "  root := `SpecMain"]
    if lang == "lean":
        lines += ["", "lean_lib Prog", "", "lean_exe prog where", "  root := `Main"]
    return "\n".join(lines) + "\n"


def make(ws: Path, task: str, arm: str, lang: str):
    ws.mkdir(parents=True)
    files = {"build": f"#!/bin/sh\nset -e\n{BUILD[lang]}\n", "run": f"#!/bin/sh\n{RUN[lang]}\n",
             "next": f"#!/bin/sh\nexec python3 {ROOT / 'bench' / 'stage.py'} {ws.resolve().parent}\n",
             "jeq": JEQ}
    if arm in LEAN_ARMS or lang == "lean":
        files["lakefile.lean"] = lakefile(arm, lang)
        files["lean-toolchain"] = (ROOT / "lean-toolchain").read_text()
    if arm in LEAN_ARMS:
        files["Spec.lean"] = "import LeanSpec\nopen LeanSpec.Core Lean\n\n"
        files["SpecMain.lean"] = ("import Spec\n" + ("import Prog\n" if lang == "lean" else "") + "\ndef main (args : List String) : IO UInt32 :=\n"
                                  "  LeanSpec.Core.cli spec% statement% args\n")
        files["test.sh"] = '#!/bin/sh\nexec lake exe spec test "${PROG:-./run}"\n'
    if lang == "lean":
        files["Prog.lean"] = "import LeanSpec\nimport Spec\n" if arm in LEAN_ARMS else ""
    for name, text in files.items():
        p = ws / name
        p.write_text(text)
        if name in ("build", "run", "test.sh", "next", "jeq"):
            p.chmod(p.stat().st_mode | stat.S_IEXEC)
    return BRIEF[arm].format(src=SRC[lang], io=IO_RULE, proofs=evidence(arm, lang), loop=LOOP)
