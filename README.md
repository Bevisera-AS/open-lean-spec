# lean-spec

Teach agents to write requirements in **Lean 4** — not Markdown, not JSON.

> **Status: very much a work in progress.** lean-spec is early, experimental
> software. The surface syntax, store format and APIs still change between
> releases, often without a migration path, and parts of the design are still
> being worked out. Version numbers mark our own releases; they are not a
> stability promise. Use it to explore the idea, and expect rough edges. Bug
> reports are welcome.

A requirement is a Lean `Prop` over a design signature. Evidence is a theorem
the kernel checks. There are no requirements in prose: a docstring is a label,
never the claim. The source is [`LeanSpec/Logic/Core.lean`](LeanSpec/Logic/Core.lean);
`lake build` is the check.

## What the bench showed

The same brief, tasks and models, with only the medium of the spec changed
(`bench/`, rounds 1 to 4, 148 scored runs):

| model | spec | runs | mean output tokens | runs with no spec drift | hidden cases |
|---|---|---|---|---|---|
| haiku | Markdown | 56 | 46.6k | 9 | 100% |
| haiku | Lean | 68 | 28.8k | 66 | 100% |
| sonnet | Markdown | 12 | 14.0k | 7 | 100% |
| sonnet | Lean | 12 | 9.1k | 11 | 100% |

Round 5 (2026-10-27) repeats the comparison with a value comparator for the
Markdown tests, a third arm `logic` (`IOReq` properties with examples attached) and,
for each arm, a variant with a reviewer agent gating every spec change (`+gate`):

| model | arm | runs | hidden | no spec drift | mean output tokens | mean input tokens | wall s |
|---|---|---|---|---|---|---|---|
| haiku | core | 8 | 8/8 | 8/8 | 14.1k | 280k | 203 |
| haiku | core+gate | 8 | 8/8 | 8/8 | 34.3k | 622k | 269 |
| haiku | logic | 8 | 8/8 | 8/8 | 30.2k | 699k | 277 |
| haiku | logic+gate | 8 | 8/8 | 6/8 | 78.5k | 1747k | 478 |
| haiku | md | 8 | 8/8 | 6/8 | 26.4k | 393k | 135 |
| haiku | md+gate | 8 | 8/8 | 8/8 | 50.0k | 908k | 308 |
| sonnet | core | 8 | 8/8 | 8/8 | 4.0k | 74k | 80 |
| sonnet | core+gate | 8 | 8/8 | 8/8 | 10.0k | 238k | 197 |
| sonnet | logic | 8 | 8/8 | 8/8 | 4.8k | 112k | 90 |
| sonnet | logic+gate | 8 | 8/8 | 8/8 | 12.8k | 293k | 222 |
| sonnet | md | 8 | 8/8 | 8/8 | 5.6k | 79k | 76 |
| sonnet | md+gate | 8 | 8/8 | 8/8 | 13.3k | 292k | 205 |

What holds across both rounds: an agent that writes the spec as Lean declarations
with examples builds the same program with fewer output tokens (about half on
Haiku, 70% on Sonnet). What round 5 corrected: most of the Markdown drift in rounds
1 to 4 was the harness comparing JSON as text; with a value comparator Markdown
drifts in 2 of 16 runs, Lean in 0 of 32 without the gate. The property surface
costs more tokens than the example surface without a correctness gain, so
`Req.holds` stays the default for black-box programs; the reviewer gate removes
drift only on Haiku Markdown and roughly doubles tokens, so it is an option, not
the default loop. The decisions and the typed findings are in
`docs/lean-spec-3-plan.md`, step 8, and `bench/Findings.lean`.
No run in either round wrote a theorem: every Lean-arm row closed in `report` as
`tested`, and none earned the mark below. What the bench measured is the example
discipline; the kernel evidence is a separate claim with its own gaps.

## The loop

Three parts, two of them agents, one a program:

- the **builder** writes `Spec.lean`, one `@[requirement]` declaration per requirement
  with its examples, then the program, in one workspace;
- the **referee** is `lake exe spec check` (structure), `./test.sh` (the examples
  against the program), `./next` (the next change request, only when the tests
  pass) and `report` (the statement merged with a test run);
- the **reviewer** reads the proposal before apply and audits the result into typed
  `Finding`s, which become `Reflection`s with the run as provenance.

The phases are OpenSpec's: propose, review, apply, archive, reflect, as Lean
`ProcessSkill` values in `LeanSpecProcess`. The loop in Lean, on lean-agent, is
`lean-agent/examples/SpecLoop.lean`.

## Background and naming

lean-spec is inspired by [OpenSpec](https://github.com/Fission-AI/OpenSpec), a
spec-driven development framework for AI coding assistants. We follow its workflow:
propose a change, apply it, then accept it. OpenSpec keeps specs in Markdown.
lean-spec keeps them as Lean propositions, so the checks on them are kernel-checked
proofs.

The name clashes with
[`paulch42/lean-spec`](https://github.com/paulch42/lean-spec), "Program Specification
in Lean 4", a tutorial on using Lean to specify *what* a program must achieve, with
worked examples. The two projects are unrelated and have different goals. That one
teaches formal specification in Lean. This one is a toolkit for keeping a product's
requirements, and an agent's changes to them, as Lean propositions with proofs.

## Why Lean, not Markdown

Until 1.x, requirements were strings (`shall`, given/when/then) and the proofs
showed only that the strings were not empty. 2.0 checks the claim itself.

- **The claim is a `Prop`.** "From light, the toggle gives dark" is
  `∀ s, S.mode s = .light → S.mode (S.toggle s) = .dark`, not a sentence.
- **Evidence is a theorem.** The kernel checks it; the requirement it proves is
  read off its type, so it cannot be attached to the wrong one.
- **Counter-models.** A `@[refutes]` theorem `¬ R bad` shows the `Prop` rules
  something out, so it is not vacuous.
- **People sign what code cannot prove.** A judgement ("the dark palette reads
  clearly") is a `@[sign_off who "digest"]` axiom. When the requirement changes,
  its digest changes and the sign-off goes stale.

## Writing a requirement

```lean
import LeanSpec.Logic.Core
open LeanSpec.Logic

namespace MyApp

inductive Mode | light | dark

def flip : Mode → Mode
  | .light => .dark
  | .dark  => .light

structure Sig where
  State  : Type
  mode   : State → Mode
  toggle : State → State

/-- From light, the toggle gives dark. -/
@[requirement must]
def switchesToDark (S : Sig) : Prop :=
  ∀ s, S.mode s = .light → S.mode (S.toggle s) = .dark

@[shipped] def impl : Sig := ⟨Mode, id, flip⟩

@[satisfies] theorem impl_switchesToDark : switchesToDark impl := by
  intro s h; cases s <;> simp_all [impl, flip]

def frozen : Sig := ⟨Mode, id, id⟩

@[refutes] theorem frozen_fails : ¬ switchesToDark frozen := by
  intro h; cases h .light rfl

spec_statement statement for MyApp

end MyApp
```

- `@[requirement must|should]` on `def R : Sig → Prop`. `must` blocks the mark
  while open; `should` is listed and never blocks.
- `@[satisfies]` on `theorem t : R impl` (or `… → R impl`).
- `@[refutes]` on `theorem t : ¬ R bad`.
- `@[shipped]` on the `def` that is the product, not a model of it.
- `@[sign_off who "digest"]` on `axiom a : SignOff R impl`; `#requirement_digest R`
  prints the digest to quote.

`spec_statement name for Ns` collects every requirement under `Ns` into a
`Statement`. A row is `open` until it has a witness with no `sorry`, no
non-standard axiom and no missing sign-off; a closed row says how far its evidence
reaches: `proved`, `model` (proved of a model, not the shipped code) or `signed`.
The **lean-spec-verified** mark holds when every `must` row is closed. `model`,
`vacuous` and `signed` are reported, not blocking, so read a row's gaps, not the mark
alone. `report` keeps a row open while one of its examples fails, whatever the kernel
proved of a model.
`Statement.render` prints it one field per line. The digest is a fingerprint, not
a signature; commit the statement next to the spec so the commit binds it.

Worked examples: [`LeanSpec/Logic/Demo/Theme.lean`](LeanSpec/Logic/Demo/Theme.lean)
and [`TempConverter.lean`](LeanSpec/Logic/Demo/TempConverter.lean).

## Black-box programs

A Python or C++ program is an `IOSig` (`run : Json → Json`). A requirement about it
is `Req.holds [examples]`, which holds at the listed points, or `IOReq pre post`,
which holds for every input `pre` accepts. Examples are the tests:

```lean
import LeanSpec
open LeanSpec.Core Lean

/-- add two numbers -/
@[requirement must] def add : IOSig → Prop := Req.holds [
  ex "basic" (json% {"op": "add", "xs": [1, 2]}) (json% {"result": 3})]

@[example add] def add_neg : Ex := ex "neg" (json% {"op": "add", "xs": [-1, 1]}) (json% {"result": 0})

@[evidence add] theorem addInts_comm (a b : Int) : a + b = b + a := by omega
```

A user-level requirement is `@[requirement must user]`. A theorem
`(h1 : R1 S) (h2 : R2 S) : U S` tagged `@[refines]` records that `R1` and `R2`
refine `U`; the statement closes `U` once both are closed. `lake exe spec report
./run` merges the statement with a test run, one JSON line per requirement, and a
row the kernel left open is `tested` when every example passes.
[`LeanSpec/Logic/Demo/Lru.lean`](LeanSpec/Logic/Demo/Lru.lean) carries the whole chain.

A workspace's `SpecMain.lean` is `def main (args : List String) : IO UInt32 :=
LeanSpec.Core.cli spec% statement% args`; `lake exe spec help` is the manual,
`check` lists every structural problem, `test ./run` runs the examples against the
program, `statement` prints what the kernel checked. `@[evidence R]` links a theorem
about the product's functions to the requirement it supports, by name; only a
`@[satisfies]` theorem of type `R impl` closes a row. The bench in `bench/` measures
this surface against Markdown (`docs/lean-spec-3-plan.md`, section 3).

## Process skills

`LeanSpecProcess` ships the loop as Lean `ProcessSkill` values
(`LeanSpec.Workflow.catalog`): the phases propose, apply, archive and reflect; the
referee's gates (`check` before review, `./next` only on passing tests, `report`
before archive, sign-off only by a person); and the builder and reviewer roles as
the skillsets `spec-builder` and `spec-reviewer` beside `spec-change`. A reviewer's
`Finding` (`LeanSpec/Finding.lean`) becomes a `Reflection` with the run as
provenance. `LeanSpecKb` is the knowledge-base kernel and the agent Wiki. Neither
holds requirements.

## Validate

```sh
lake build                                        # LeanSpec, LeanSpecProcess, LeanSpecKb
lake build LeanSpecSigned                         # Theme demo (sign-off axiom) and Logic tests (sorry)
lake build lean-spec lean-spec-logic-statement    # the two executables
lake test
lake env lean bench/Findings.lean                 # the bench's typed findings
python3 bench/smoke.py                            # the referee on a known workspace per arm, no model
lake check --paranoid                             # Linux only; see below
```

There is no `native_decide` in lean-spec: every proof, including those on concrete
literals, is checked by the Lean kernel (`decide +kernel`). Under Lean 4.35.0,
`lake check --paranoid` accepts the development, sandboxed, with all six bundled
checkers, including the verified kernels con-leche and con-ron. CI runs it on every
merge request, on `main` and on tags.

`lake check` sandboxes the build with `bwrap`, so it needs Linux user namespaces. In
Docker that means `--privileged`; on Ubuntu 24.04 it means lifting AppArmor's
`kernel.apparmor_restrict_unprivileged_userns`. Keep the Lean toolchain outside the
project directory, or `lake check` stalls at "Resolving dependencies".
[`docs/lake-check-paranoid-report.md`](docs/lake-check-paranoid-report.md) records
what the checkers found, why, and how the CI job is set up.

## Layout

- `LeanSpec/Core/` — `Ex`, `IOSig`, `Req.holds`, `IOReq`, the JSON runner, structural checks and the `spec` CLI.
- `LeanSpec/Logic/Core.lean` — requirements as `Prop`s: the attributes, gaps, `spec_statement`, `spec%`.
- `bench/` — the Markdown-vs-Lean benchmark: harness, tasks, scored results, typed findings.
- `LeanSpec/Logic/Demo/` — worked examples; `LeanSpec/Logic/Tests.lean` — attribute and gap tests.
- `LeanSpec/ProcessSkill.lean`, `Skillset.lean`, `Workflow/` — process skills and the `spec-change` skillset.
- `LeanSpec/Validated.lean` — `NonBlank`, dotted ids, `NonEmptyArray` with proofs.
- `LeanSpec/Kb.lean`, `Wiki.lean`, `WikiAccess.lean` — knowledge-base kernel and agent Wiki.

## Notes (Lean 4.35)

- After `module`, no doc comment before `import`.
- Write decidable predicates over `List` (`s.toList.any …`, `arr.toList.all …`), not
  `String.any`/`splitOn` or `Array.all`/`any`. The kernel cannot evaluate the latter,
  so `decide +kernel` would get stuck. Mark definitions that other modules' proofs
  unfold `@[expose]`.
- Cross-file `#guard` needs `public meta import` of the module defining the checker.
- `LeanSpec` (`Core` and `Logic`) is plain `import Lean`, not the module system; the
  module-system layers are their own libraries, `LeanSpecProcess` and `LeanSpecKb`,
  each with a root module of that name.

## Public release

A history-free public snapshot is published as
[`bevisera/open-lean-spec`](https://gitlab.com/bevisera/open-lean-spec), with a
read-only [GitHub mirror](https://github.com/Bevisera-AS/open-lean-spec).

## License

Copyright 2026 Bevisera AS. Licensed under the [Apache License, Version 2.0](LICENSE)
— see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). Release history is in
[`CHANGELOG.md`](CHANGELOG.md).
