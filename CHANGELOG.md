# Changelog

All notable changes to **lean-spec** are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Unless noted otherwise, every release builds clean (`lake build`), passes the suite
(`lake test`), and all guarantees rest on the Lean kernel and the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, and `native_decide`
is confined to constructing concrete values whose predicate the kernel cannot reduce
(documented in `LeanSpec/Kb.lean`'s trust-boundary note).

## [1.0.0] — 2026-10-01

### Added
- **Verification statement.** `verification_statement <name> for <snapshot>` is a
  build artefact: what was proved, the requirement ids those proofs attach to, the
  axioms `#print axioms` (`collectAxioms`) reports — including `native_decide`
  auxiliary axioms — and the obligations still open. The `lean-spec-verified` mark
  is that statement. It covers the proved rows only. `sorryAx` keeps a row outside
  the mark. The canonical text round-trips (`emitVerificationStatement` /
  `parseVerificationStatement`).
- The statement names the **Lean toolchain** that checked the proofs and a
  **spec digest** (`fnv1a64:` over the canonical spec source, `specDigestOf`).
  A statement edited to claim another spec or toolchain no longer `certifies`.

### Changed
- The theme demo theorem `toggleDarkCheck_of_light` is now kernel-checked with
  `decide` instead of `native_decide`; its statement lists only `propext`.

## [0.9.0] — 2026-08-31

The **dependency-graph + boot-closure** epic, plus the clean split from the sibling
agent packages. `ProcessSkill` gains first-class `requires` edges, `Catalog` proves
the graph is registered and acyclic, and a deterministic transitive boot closure
removes hand-listed dependency arrays. Additive over 0.8.x — `requires` defaults to
`#[]`, keeping every existing skill and catalog source-compatible.

### Added
- **`ProcessSkill.requires : Array ProcessSkillId := #[]`** — first-class
  dependency edges. The codec gains a `label "requires" (list procId)` factor and
  `validate_sound` / `validate_complete` are re-proved unchanged.
- **`Catalog` dependency invariants**: `AllRequiresRegistered` (every required id
  resolves to a registered skill) and `RequiresAcyclic` (a fuelled Kahn reduction,
  fuel = `skills.size`), both `Decidable` and threaded through `Catalog.of`
  (rejecting unregistered requires, and cycles with a new `.requiresCycle`
  validation issue), `of_sound`, `of_complete`, and `wellFormed` /
  `wellFormed_eq_true`.
- **`Catalog.bootClosure`** (`LeanSpec/Workflow/BootClosure.lean`): the declared
  boot skills plus all transitive `requires`, in a deterministic order (a function
  of catalog + skillset only, no hash-set iteration). Determinism is proved
  (`bootClosure_congr`); contains-boot, contains-role, nodup, and transitive
  closure are validated as `#guard`s on the concrete `specChange` catalog.

### Note on proof strength
- Boot-closure properties 1–4 are validated on the concrete catalog rather than as
  open-variable theorems; determinism (property 5) is a general theorem.
  Strengthening 1–4 to general theorems is a tracked follow-up. No `sorry`, no new
  `axiom`.

### Removed
- **Every reference to the sibling agent packages.** `lean-agent` and
  `lean-spec-agent` are separate projects; the split is clean, so nothing here
  points at them any more.
  - `LeanSpec/Demo/LeanAgentPlan.lean` — a backlog for `lean-agent` parked in this
    tree because that package may not import `LeanSpec.*`. It was never in the
    lakefile globs, so its `#guard`s never ran.
  - The eight `moved:` CLI pointers (`live-ping`, `ask`, `replay-transcript`,
    `extract-live`, `ask-host`, `ask-search`, `ask-catalog`,
    `export-host-proposal`) and the `moved` helper. Unknown commands now print the
    usage line, as any other unknown command does.
  - The agent and bridge clauses of the import firewall, and the `assertMissing`
    checks for `LeanAgent*` / `LeanSpecAgent*` trees. **Kept:** the invariant that
    still has force — `LeanUtil` and `LeanJson` must not import `LeanSpec.*`, so
    the shared helpers stay below the spec types.
  - The `proposeChange` Path A / Path B rule, which existed only to name the
    bridge as the untrusted-JSON path.

## [0.8.1] — 2026-08-31

### Added
- **A CI pipeline** (`.gitlab-ci.yml`, `ci/Dockerfile`). `verify` runs `lake build`
  and `lake test` on merge requests, on the default branch, and on tags — making
  the standing claim at the top of this file a continuous check rather than an
  assertion, and running it on Linux, a second platform from the macOS development
  machine. That distinction is load-bearing here: `native_decide` compiles and
  *executes* at each of its use sites, so CI re-runs those decisions rather than
  re-reading them.

  There is no maintained upstream Lean image to build on
  ([leanprover/lean4#6996](https://github.com/leanprover/lean4/issues/6996)), so
  the environment is defined in `ci/Dockerfile` and pinned. The first pipeline
  needs no preparation: it installs the toolchain named in `lean-toolchain` and
  caches it. A manual `build-ci-image` job builds and pushes that image to the
  project's Container Registry and prints its digest; setting the `LEAN_CI_IMAGE`
  project variable to the digest then skips the install. No source changes.

### Fixed
- The `[0.8.0]` compare link, missing from the link block.

## [0.8.0] — 2026-08-31

The **agent-knowledge governance** epic (Track LW): capability-gated maintenance
and promotion of the agent-experience store, plus a sensitivity classification that
consolidation can only raise. All additive — existing wire fixtures and round-trip
proofs are unchanged. Design notes in `docs/lw0-agent-knowledge-governance-design.md`.

### Added
- **`WikiAccess`** (`LeanSpec/WikiAccess.lean`): a closed capability, ordered
  `none < readEffective < maintain < promoteCandidate`, with gate predicates
  (`canRead` / `canMaintain` / `canPropose`) and capability-inclusion proofs. The
  mapping from a principal/authority to a level is left to downstream policy.
- **`Classification`** (`LeanSpec/Classification.lean`): an opaque, totally ordered
  sensitivity lattice (`open_ < internal < sensitive`) with `join` and lattice proofs
  (`join_comm`, `join_self`, `le_join_left`/`right`, `join_bottom`). The library
  assigns no meaning to the levels; downstream maps its audiences onto them.
- **Capability-gated entry points** on `Wiki`: `recordWith` (maintainer fold,
  requires `canMaintain`) and `proposePromotion` (requires `canPropose` **and**
  Wiki-coherence, so no fabricated-provenance proposal reaches the human gate), with
  `AccessError` and refuse/ok proofs. Acceptance remains the existing human gate
  `archiveWithReflections` — `promoteCandidate` is proposal authority only, so the
  single agent→authority valve is preserved.

### Changed
- **`Reflection` carries a `classification`** (default `Classification.bottom`).
  `Reflection.merge` (and thus `Wiki.record` consolidation) takes the **join** of the
  inputs' classifications: `merge_preserves_classification` and
  `merge_classification_ge_left` prove consolidation can only raise sensitivity, never
  lower it. The codec gains one optional field (composed with the existing applicative
  product); absent-on-the-wire decodes to `bottom`, mirroring `promoted → .noAction`,
  so all prior fixtures decode unchanged.

### Guarantees and non-goals
- Proved: capability gating (refuse below the required level), Wiki-coherence of any
  proposed promotion, and classification-join preservation through consolidation.
- Not claimed: that any reflection is true or useful (the agent store stays
  lower-assurance than the spec store), and no disclosure audiences, `RolePolicy`, or
  separation-of-duties — those are downstream company-pack policy.

## [0.7.2] — 2026-08-31

### Added
- **Apache-2.0 license.** `LICENSE` (full Apache License 2.0 text), `NOTICE`
  (Copyright 2026 Bevisera AS), a `CHANGELOG.md`, and a License section in the README.
  No source changes.

## [0.7.1] — 2026-08-31

### Changed
- **`Wiki` adopts the generic `Kb.Store.record`.** `Wiki` now wraps a
  `Kb.Store Reflection RunId` (all entries at `.provisional`); `record` is two
  `Store.record` consolidations (fold provenance into the content-canonical node,
  keep the reflection as a primary) plus the `supersedes` edge. The bespoke
  `unique_push` / `unique_replace` / `map_preserves_ids` / `not_has_not_mem` lemmas
  and the `pushFresh` / `upsertCanonical` machinery are deleted (net −52 lines).
  `Wiki.entries` reads the merged `item.provenance` back into `derivedFrom` (the
  store's provenance is the source of truth after a consolidation).

## [0.7.0] — 2026-08-31

The **codec-functor** epic: a proof-carrying codec algebra, and every record
validator migrated onto it. Net −102 lines despite adding the reusable algebra.

### Added
- **A codec algebra** (`LeanSpec/Codec/Applicative.lean`): a `Codec R D` bundle
  (decode + encode + `sound` + `complete` as fields) with combinators `prod`,
  `imap`, `comap`, `refine` (cross-field constraints), `label` (per-field error
  paths), `list`, `nonEmpty`, `optional`, and atomic codecs `nonBlank` / `reqId` /
  `procId` / `passthrough`. Each round-trip is proved once.
- A generic `parseList` combinator (collapsing the three hand-rolled list parsers).

### Changed
- **All record validators re-expressed as codec compositions**, deleting their
  bespoke `Raw`/`validate`/`_sound`/`_complete` split-chains: Supersedes, Reflection,
  ProcessSkill, Skillset, Scenario, Requirement, DesignUnit. The sum types
  `CheckStatus` and `Delta` are wrapped as `Codec` values (used as field codecs).

## [0.6.0] — 2026-08-30

### Added
- **Generic consolidation write-path** `Kb.Store.record` (insert-or-consolidate),
  with `uniqueIds`-preservation and provenance-preservation proved once.
- **`Wiki` unique-id invariant and content-canonical consolidation.** Recording a
  learning mints a content-canonical node (id derived from the learning) and *keeps
  the originals* as superseded primaries linked by stored `supersedes` morphisms, so
  history referencing the original ids still resolves.
- A JSON codec for morphisms; the `Wiki` store round-trips its `relations`, and
  `decodeWiki` re-establishes the uniqueness invariant fail-closed.

### Fixed
- **Duplicate `LeanSpec.KbAdapter.toItem` symbol** that broke the `LeanSpec:shared`
  link (two `@[expose]` defs of the same name across adapter modules). Renamed per
  payload (`reflToItem` / `attrToItem`).

### Changed
- **Finalised the consolidation core:** `Determination.defeated` delegates to the
  generic `Kb.defeated`, the morphism→relation mapping and presence predicate live
  once, and the twin `Wiki.hasId`/`present` collapse — removing the last duplicated
  defeat/mapping/presence logic.

## [0.5.1] — 2026-08-30

### Changed
- **Typed ids** (`RunId`, `ReflectionId`) close the string-addressing seam so a
  morphism endpoint or citation cannot silently mix id kinds.
- **`Wiki` migrated onto the `Kb` core in place** — delegate to the generic
  provenance-union and defeasible-resolution rather than reimplementing them.
- Audited `native_decide` vs `decide` across the guarantees and documented the trust
  boundary.

## [0.5.0] — 2026-08-30

Baseline for this changelog. The generic, assurance-indexed `Kb` core; the attributed
archive gate (recording *who* accepted *what*); and the human-authority spec store
(Requirement / Design / Determination / Precedent) alongside the agent-experience
Wiki layer.

[0.9.0]: https://gitlab.com/bevisera/lean-spec/-/compare/v0.8.1...v0.9.0
[0.8.1]: https://gitlab.com/bevisera/lean-spec/-/compare/v0.8.0...v0.8.1
[0.8.0]: https://gitlab.com/bevisera/lean-spec/-/compare/v0.7.2...v0.8.0
[0.7.2]: https://gitlab.com/bevisera/lean-spec/-/compare/v0.7.1...v0.7.2
[0.7.1]: https://gitlab.com/bevisera/lean-spec/-/compare/v0.7.0...v0.7.1
[0.7.0]: https://gitlab.com/bevisera/lean-spec/-/compare/v0.6.0...v0.7.0
[0.6.0]: https://gitlab.com/bevisera/lean-spec/-/compare/v0.5.1...v0.6.0
[0.5.1]: https://gitlab.com/bevisera/lean-spec/-/compare/v0.5.0...v0.5.1
[0.5.0]: https://gitlab.com/bevisera/lean-spec/-/tags/v0.5.0
