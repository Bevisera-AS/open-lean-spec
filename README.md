# lean-spec

Teach agents to write requirements in **Lean 4** — not Markdown, not JSON.

A requirement is a typed, proof-carrying Lean value. Blank fields, empty
scenario lists, and malformed ids are compile errors, not lint warnings. A
human-friendly `requirement` syntax keeps the source readable without giving up
the guarantees.

## Why Lean, not Markdown

- **Fail-closed.** A `Requirement` with no scenarios cannot be constructed. The
  type is the check.
- **One source of truth.** The Lean value *is* the requirement. JSON is only a
  wire format; Markdown is not a source at all.
- **Reviewable.** The `requirement` sugar reads like plain BDD; it desugars to
  the same proof-carrying structure an agent would hand-write.

## The sugar

```lean
requirement overviewDashboard where
  id    "page.overview-dashboard"
  shall "Display a summary dashboard with national averages per grade"
  strength must

  scenario "latest year shown on load"
    given "the user navigates to the overview page"
    when  "the page finishes loading"
    then_ "national averages for the latest available year are displayed"
    check deferred "dashboard UI not yet built"
```

This expands to a `Requirement` value and registers it. A blank `shall`, a
duplicate id, or a scenario with no `then_` fails at elaboration.

- `check executable` — a named checker (`#guard` or test) exists for this scenario.
- `check deferred "reason"` — not yet checked; the reason must be non-blank.

## Core types

- `Requirement` — id, `shall`, strength (`shall`/`must`/`should`), non-empty scenarios.
- `Scenario` — name, optional `given`, required `when` / `then_`, and a check status.
- `CheckStatus` — `executable` or `deferred` with a non-blank reason.

Wire-facing domain types (requirements, design, change, reflection, precedent,
skillset, …) each have a `Raw` counterpart and a `validate` function proven to
round-trip (`validate_sound` / `validate_complete`).

## Target languages

Implementation artifacts must target a **strongly-typed** language. The allowed
set is closed by construction — an agent cannot name an unlisted language.

- Web: **TypeScript**.
- Everything else: **Lean 4** preferred, then Scala or Rust.
- Java only through [Strata](https://github.com/strata-org/Strata) verification.

A `DesignUnit` carries its `surface` (web / native) and `target`; the pairing is
enforced by a proof obligation (`TargetLang.allowedFor`). A web unit targeting
Rust, or a native unit targeting TypeScript, cannot exist.

## Validate

```sh
lake build
lake test
```

## Layout

- `LeanSpec/Types.lean` — `Requirement`, `Scenario`, `CheckStatus` by construction; `Raw` + validation retraction.
- `LeanSpec/Validated.lean` — `NonBlank`, `RequirementId`, `NonEmptyArray` primitives with proofs.
- `LeanSpec/Design.lean` — `DesignUnit`, `TargetLang`, `Surface`, and the allowed-target policy.
- `LeanSpec/Elab/Spec.lean` — the `spec` command and requirement registry (`registeredSpecs%`).
- `LeanSpec/Elab/Sugar.lean` — the human-facing `requirement` syntax.
- `LeanSpec/Demo/` — usage examples only. No solution content; requirements here exist to show the syntax.

## Notes (Lean 4.33)

- After `module`, no doc comment before `import`.
- Cross-file `#guard` needs `public meta import` of the module defining the checker.
- A `/--` doc comment cannot sit immediately before a `spec` or `requirement` command; use a plain `/-` comment.

## Source

Canonical hosting is on GitLab (`bevisera/open-lean-spec`). A read-only
[GitHub mirror](https://github.com/Bevisera-AS/open-lean-spec) is kept in sync
for discovery and tooling that expects GitHub; open issues and PRs against GitLab
when you can.

## License

Copyright 2026 Bevisera AS. Licensed under the [Apache License, Version 2.0](LICENSE)
— see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). Release history is in
[`CHANGELOG.md`](CHANGELOG.md).
