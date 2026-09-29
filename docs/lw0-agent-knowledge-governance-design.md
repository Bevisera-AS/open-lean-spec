# LW0 — Agent-knowledge governance: design note (historical)

Status: **landed.** LW1 implemented the invariants below (`WikiAccess`,
capability-gated maintenance/promotion, classification + join-preservation);
LW2 released them as `0.8.0`. Kept here as the design rationale; the live
modules are authoritative.

Repository: `lean-spec`
Recorded: 2026-08-31

Downstream binding of these mechanisms to `RolePolicy` and disclosure audiences
is **out of scope** for this library and belongs in a company pack.

## 1. Why this is upstream

`WikiAccess`, and the treatment of Wiki *maintenance* and *promotion* as
capability-gated governed transitions, are **generic** agent-knowledge
mechanisms. They are properties of any consumer of the agent-experience store,
not of a particular organisation. The reusable substrate belongs in `lean-spec`;
only the mapping from principals/authorities to permitted transitions, and the
concrete disclosure audiences, stay downstream.

## 2. Baseline at design time (pre-LW1)

- `LeanSpec/Reflection.lean`: `Reflection` (`id`, `kind : ReflectionKind`,
  `learning : NonBlank`, `derivedFrom : NonEmptyArray RunId`,
  `promoted : PromotionTarget`), the full house (`Raw` twin, `validate`,
  `validate_sound`/`validate_complete`, codec), and `coherentIn` /
  `coherentIn_rejects_unknown` (the provenance-honesty proofs).
- `LeanSpec/Wiki.lean`: `Wiki` (a `Kb.Store Reflection RunId` + supersession
  `relations`), `Wiki.record` (consolidating maintainer fold), `effectiveByKind`
  readback, `Morphism.coherentInWiki`, and the valve — `ReflectedChange`,
  `SpecSnapshot.archiveWithReflections`, with `archiveWithReflections_uncited`
  and `archiveWithReflections_ok_coherent`.
- `LeanSpec/Trace.lean`: `PromotionTarget` (`skill | requirement | steering |
  noAction`) — the valve *out* of the trace layer.

**Gap (resolved in LW1).** Maintenance (`Wiki.record`) and promotion (the
`promoted` valve / `archiveWithReflections`) were *ambient*: any caller could
invoke them. There was no typed capability guarding who may maintain the Wiki or
propose a promotion, and a `Reflection` carried no classification, so the
library could not state or prove that agent-axis knowledge stays at or below a
declared disclosure level.

## 3. Invariants introduced by Track LW (now shipped)

### 3.1 `WikiAccess` — a closed capability

```
inductive WikiAccess where
  | none            -- no access to the agent-knowledge store
  | readEffective   -- may read effectiveByKind; cannot maintain or promote
  | maintain        -- may run the maintainer fold (record); implies readEffective
  | promoteCandidate -- may PROPOSE a promotion into the human gate; implies maintain
```

Ordered: `none < readEffective < maintain < promoteCandidate`. `promoteCandidate`
lets a caller *propose* a promotion into the human-gate queue — it is **not**
authority to accept. Acceptance remains a human gate (`archiveWithReflections`'s
`ArchiveDecision`), unchanged. This is what keeps the valve singular and keeps
"who may accept" as downstream policy.

### 3.2 Maintenance and promotion as capability-gated transitions

- `Wiki.record` has a capability-gated wrapper: recording requires at least
  `.maintain`. The bare `record` remains for internal/proof use; the gated entry
  point is what downstream callers use.
- Proposing a promotion requires at least `.promoteCandidate`. Promotion
  proposal is expressed as producing a `ReflectedChange` motivated by
  Wiki-coherent reflections; the existing `archiveWithReflections` valve is the
  acceptance gate and is unchanged.

Proofs (discharged in LW1):
- recording below `.maintain` refuses;
- proposing a promotion below `.promoteCandidate` refuses;
- a fabricated-provenance reflection cannot be promoted — reuses the existing
  `Reflection.coherentIn_rejects_unknown` and `archiveWithReflections_uncited`.

### 3.3 Classification tag on `Reflection`, preserved through merge

`Reflection` carries an **opaque, ordered** classification label the library
treats abstractly (a bounded lattice with a `join`); it assigns **no** meaning to
the levels. Downstream packs map their audiences onto this lattice.

Invariant: `Reflection.merge` (and therefore `Wiki.record` consolidation) yields
a node whose classification is the **join** of its inputs — consolidation can
only raise, never lower, classification. This is the generic analogue of "agent
knowledge stays at or below its declared level"; the concrete non-leak rule is
downstream.

Proof (LW1): `merge_preserves_classification` (merged classification = join of
inputs).

## 4. Fixture / wire compatibility

The classification field was added with a **default = bottom** (the least
element, the generic analogue of "unclassified/most-open"). Consequences:

- Existing `Raw.Reflection` wire fixtures **decode unchanged**: absent
  classification key → bottom, exactly as `promoted` absent → `.noAction`.
- Existing `Reflection` `#guard`s and round-trip proofs
  (`validate_complete`/`validate_sound`) remain valid; the codec gains one
  optional field composed with the existing applicative product, following the
  `promoted` precedent.
- `WikiAccess` is additive and touches no existing decode path.

**Decision (taken):** lattice bottom is **most-open**, so `join` means
"consolidation raises sensitivity". The downstream default classification for a
newly captured reflection is a policy choice (often `.private`-equivalent) —
deliberately distinct from the library's lattice bottom.

## 5. Scope decisions

1. **Separation of duties** (a principal may not both propose and accept a
   promotion) is a **downstream** policy choice, not a library invariant — the
   library only provides the capability distinction that makes it expressible.
2. Company audiences, `RolePolicy`, and party scope stay out of `lean-spec`.

## 6. Non-goals (LW)

- No disclosure audiences, `RolePolicy`, or party scope in `lean-spec`.
- No change to the human spec store, `PromotionTarget`, or the acceptance gate's
  meaning.
- No second agent→authority touch-point: `archiveWithReflections` stays the one
  valve.
- No claim that any reflection is true or useful — the library proves
  well-formedness, provenance-coherence, unique ids, and
  classification-preservation, nothing more.
