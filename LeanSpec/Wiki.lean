module

public import LeanSpec.Reflection
public import LeanSpec.WikiAccess
public import LeanSpec.Validated
public import LeanSpec.Determination
public import LeanSpec.Snapshot
public import LeanSpec.Kb
public meta import LeanSpec.Reflection
public meta import LeanSpec.WikiAccess
public meta import LeanSpec.Determination
public meta import LeanSpec.Snapshot
public meta import LeanSpec.Kb
public meta import LeanUtil

/-!
# Wiki: the consolidated agent-experience store (WikiSkill "wiki" layer)

Agent axis, kept apart from the human spec store.

A `Wiki` accumulates `Reflection`s. The point of WikiSkill is *consolidation*: two
reflections recording the **same learning** are folded into one **content-canonical
node** whose id is derived from the learning itself (`canonicalId`), so recording
the same learning again is stable — it always resolves to the same node. Unlike the
earlier design, consolidation **keeps the originals**: each recorded reflection stays
as a primary entry, the canonical node `supersedes` it (a stored `Morphism`), and
`effectiveByKind` returns the canonical view while the originals remain queryable
history. Provenance never shrinks — `derivedFrom` run ids are unioned into the
canonical node (`Kb.dedupUnion`).

The store carries a `uniqueIds` invariant (like `SpecSnapshot`): reflection ids are
unique by construction, and every write path (`record`) is proved to preserve it.

Everything stays *lower-assurance* than the spec store: nothing here is claimed true
or useful, only well-formed, unique, and provenance-honest.

Note on the canonical id: the zero-dep toolchain has no `String.any` reasoning
lemmas (string non-blankness is only ever discharged by `native_decide` on literals),
so an id that *concatenated* a kind tag onto a variable `learning` could not be
proved non-blank. The canonical id therefore reuses the learning's own non-blank
witness verbatim; `kind` lives on the node (and on the kept primaries), not in the id.
-/

namespace LeanSpec

public section

open LeanSpec.TypeSystems (Morphism MorphismKind)

/-! ## Boolean kind-equality (native across modules)

The derived `BEq`/`DecidableEq ReflectionKind` has no interpreter-native
implementation across module boundaries, so `#guard`s that *run* store code can't
use `==` on kinds. A hand-written closed match compiles to native code. -/
public def kindEq : ReflectionKind → ReflectionKind → Bool
  | .pattern, .pattern => true
  | .failureMode, .failureMode => true
  | .strategy, .strategy => true
  | _, _ => false

public theorem kindEq_sound : ∀ {a b : ReflectionKind}, kindEq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [kindEq] at h)

/-! ## Deduplicated union of provenance — delegated to the generic core

`Wiki` delegates provenance union to `Kb.dedupUnion`: the generic core sits below
the domain store (`Validated → Kb → Wiki`), so consolidation on the agent axis *is*
the generic provenance union rather than a parallel copy. -/

/-- All of `a`, then the elements of `b` not already in `a`. The generic
`Kb.dedupUnion`. -/
@[expose] public def dedupUnion (a b : Array RunId) : Array RunId :=
  Kb.dedupUnion a b

/-- The union is at least as large as `a`, so non-empty whenever `a` is. -/
public theorem dedupUnion_size_pos {a b : Array RunId} (h : 0 < a.size) :
    0 < (dedupUnion a b).size :=
  Kb.dedupUnion_size_pos h

/-- Every run id of `a` survives: its value is among the merged values. -/
public theorem mem_map_value_dedupUnion_left {a b : Array RunId} {x : RunId}
    (hx : x ∈ a) : x.value ∈ (dedupUnion a b).map (·.value) :=
  Array.mem_map_of_mem (Kb.mem_dedupUnion_left hx)

/-! ## Content-level consolidation of two reflections (retained for the adapter)

`Reflection.merge` is the pure two-reflection consolidation the `Kb` adapter proves
corresponds to `Kb.merge`. `Wiki.record` no longer routes through it (it consolidates
into a canonical node instead), but it stays as the pointwise merge primitive. -/

/-- Consolidate two reflections that share a `kind` and `learning`: keep `a`'s
identity, union both provenance sets. `none` when they differ. -/
@[expose] public def Reflection.merge (a b : Reflection) : Option Reflection :=
  match kindEq a.kind b.kind && a.learning.value == b.learning.value with
  | true =>
    some { id := a.id, kind := a.kind, learning := a.learning
           derivedFrom :=
             ⟨dedupUnion a.derivedFrom.items b.derivedFrom.items,
              dedupUnion_size_pos a.derivedFrom.property⟩
           promoted := a.promoted
           classification := Classification.join a.classification b.classification }
  | false => none

/-- **Provenance preservation** for the pointwise merge. -/
public theorem Reflection.merge_preserves_provenance
    {a b m : Reflection} (h : Reflection.merge a b = some m)
    {x : RunId} (hx : x ∈ a.derivedFrom.items) :
    x.value ∈ m.derivedFrom.items.map (·.value) := by
  simp only [Reflection.merge] at h
  split at h
  · injection h with h; subst h; exact mem_map_value_dedupUnion_left hx
  · contradiction

/-- **Classification preservation**: consolidation takes the join of the inputs'
classifications — consolidation can only raise sensitivity, never lower it. -/
public theorem Reflection.merge_preserves_classification
    {a b m : Reflection} (h : Reflection.merge a b = some m) :
    m.classification = Classification.join a.classification b.classification := by
  simp only [Reflection.merge] at h
  split at h
  · injection h with h; subst h; rfl
  · contradiction

/-- Corollary: the merged classification is at least as sensitive as each input. -/
public theorem Reflection.merge_classification_ge_left
    {a b m : Reflection} (h : Reflection.merge a b = some m) :
    a.classification.rank ≤ m.classification.rank := by
  rw [Reflection.merge_preserves_classification h]
  exact Classification.le_join_left a.classification b.classification

/-! ## The store: a generic `Kb.Store` + a stored supersession history

`Wiki` wraps a `Kb.Store Reflection RunId` (every entry rests at `.provisional`), so
the uniqueness invariant and the insert-or-consolidate write path come from the
generic core — no bespoke `unique_push`/`unique_replace`. `relations` holds the
`supersedes` edges consolidation mints (canonical node → each original). -/

/-- Reflections are addressed by their id. -/
public instance : Kb.Identified Reflection where
  idOf r := r.id.value

/-- The consolidated agent-experience store: a generic `Kb.Store` of reflections
plus the stored supersession history. -/
public structure Wiki where
  store     : Kb.Store Reflection RunId := { items := #[], uniqueIds := by native_decide }
  relations : Array Morphism := #[]

/-- The reflections held, projected from the store (all at `.provisional`). The
store's `provenance` is the source of truth for run ids (consolidation grows it), so
it is read back into `derivedFrom` — the payload's own copy may be stale after a
merge. -/
@[expose] public def Wiki.entries (w : Wiki) : Array Reflection :=
  w.store.items.map (fun b => { b.item.payload with derivedFrom := b.item.provenance })

/-- Is a reflection with this id present? Delegates to the generic `Store.hasId`.
Originals are kept after consolidation, so a citation to an original id still
resolves — the "clear history" guarantee in practice. -/
public def Wiki.hasId (w : Wiki) (idv : String) : Bool := w.store.hasId idv

/-- Presence as the `present` predicate the generic `Kb.defeated` takes. -/
@[expose] public def Wiki.present (w : Wiki) : String → Bool := fun idv => w.hasId idv

/-! ### Content-canonical ids and the consolidated node -/

/-- The content-canonical id for a learning: the learning text itself, reusing its
non-blank witness, so the same learning always maps to the same node. -/
@[expose] public def canonicalId (learning : NonBlank) : ReflectionId :=
  ⟨learning.value, learning.property⟩

/-- The canonical (consolidated) node for a learning, carrying run provenance. -/
@[expose] public def canonicalNode (kind : ReflectionKind) (learning : NonBlank)
    (runs : NonEmptyArray RunId) : Reflection :=
  { id := canonicalId learning, kind, learning, derivedFrom := runs }

/-- Lift a reflection into a provisional store item (its run provenance carried). -/
@[expose] public def Wiki.itemOf (r : Reflection) : Kb.Item .provisional Reflection RunId :=
  { payload := r, provenance := r.derivedFrom }

/-! ### The write path: `record` via the generic `Kb.Store.record` -/

/-- Record a `supersedes` edge from the canonical node (source = the learning, which
is the canonical id value) to the original reflection, skipping duplicates. -/
public def Wiki.addSupersedes (w : Wiki) (originalId : ReflectionId) (learning : NonBlank) : Wiki :=
  let m : Morphism :=
    { kind := .supersedes, source := learning, target := ⟨originalId.value, originalId.property⟩ }
  if w.relations.any (· == m) then w
  else { w with relations := w.relations.push m }

/-- **Record a reflection.** Two `Kb.Store.record` consolidations — one folding the
run provenance into the content-canonical node (minting it on first sight), one
keeping the reflection as a primary — plus a `supersedes` edge from the node to it.
`uniqueIds` is maintained by the generic `Store.record`; originals are never dropped
(the consolidated view is `effectiveByKind`, the history is the primaries plus
`relations`). -/
public def Wiki.record (w : Wiki) (r : Reflection) : Wiki :=
  let cid := canonicalId r.learning
  let store1 := w.store.record (fun b => b.id == cid.value) .provisional
                  (Wiki.itemOf (canonicalNode r.kind r.learning r.derivedFrom))
  let store2 := store1.record (fun b => b.id == r.id.value) .provisional (Wiki.itemOf r)
  ({ store := store2, relations := w.relations } : Wiki).addSupersedes r.id r.learning

/-! ## Readback -/

/-- Readback: the reflections of a given kind. -/
public def Wiki.byKind (w : Wiki) (k : ReflectionKind) : Array Reflection :=
  w.entries.filter (fun e => kindEq e.kind k)

/-- Readback is sound: every entry `byKind k` returns really has kind `k`. -/
public theorem Wiki.byKind_all_match {w : Wiki} {k : ReflectionKind} {e : Reflection}
    (h : e ∈ w.byKind k) : e.kind = k := by
  simp only [Wiki.byKind, Array.mem_filter] at h
  exact kindEq_sound h.2

/-! ## Relations between reflections — reusing the 2-morphism vocabulary

The morphism→relation mapping lives once, in `Determination` (next to `Morphism`);
`Wiki` reuses it and delegates the defeat algorithm to the generic `Kb.defeated`. -/

/-- Map a wiki morphism-kind to the generic relation-kind. Delegates to
`Determination`. -/
@[expose] public def kindToRelKind : MorphismKind → Kb.RelationKind :=
  TypeSystems.kindToRelKind

/-- Map a wiki morphism to a generic relation. Delegates to `Determination`. -/
@[expose] public def morphismToRelation (m : Morphism) : Kb.Relation :=
  TypeSystems.morphismToRelation m

/-- A relation is coherent against the wiki when both endpoints are present. -/
public def TypeSystems.Morphism.coherentInWiki (w : Wiki) (m : Morphism) : Bool :=
  w.hasId m.source.value && w.hasId m.target.value

/-- A coherent relation's target reflection is present. -/
public theorem TypeSystems.Morphism.coherentInWiki_target_present {w : Wiki} {m : Morphism}
    (h : m.coherentInWiki w = true) : w.hasId m.target.value = true := by
  simp only [TypeSystems.Morphism.coherentInWiki] at h
  cases ht : w.hasId m.target.value with
  | true => rfl
  | false => rw [ht] at h; simp at h

/-- `r` is superseded when some defeating morphism targets its id and the source
reflection is present. Delegates to the generic `Kb.defeated`. -/
@[expose] public def Wiki.superseded (w : Wiki) (ms : List Morphism) (r : Reflection) : Bool :=
  Kb.defeated w.present (ms.map morphismToRelation) r.id.value

/-- Effective readback: entries of kind `k` not superseded, resolved against the
store's own `relations`. The consolidated canonical nodes survive; the primaries
they supersede drop out — this is the canonical view. -/
public def Wiki.effectiveByKind (w : Wiki) (k : ReflectionKind) : Array Reflection :=
  (w.byKind k).filter (fun r => !w.superseded w.relations.toList r)

/-- Effective readback returns only entries of the asked kind that are undefeated. -/
public theorem Wiki.effectiveByKind_sound {w : Wiki}
    {k : ReflectionKind} {r : Reflection} (h : r ∈ w.effectiveByKind k) :
    r.kind = k ∧ w.superseded w.relations.toList r = false := by
  simp only [Wiki.effectiveByKind, Array.mem_filter] at h
  refine ⟨Wiki.byKind_all_match h.1, ?_⟩
  have h2 := h.2
  cases hs : w.superseded w.relations.toList r with
  | false => rfl
  | true => rw [hs] at h2; simp at h2

/-! ## The valve: a spec change may cite Wiki reflections

The one place the agent axis touches the human-authority axis. A spec `Change` may
declare the reflection(s) that motivated it. The archive gate refuses a change that
cites a reflection the Wiki does not hold — no fabricated motivation crosses the
valve. Because originals are kept, a citation to a now-consolidated reflection still
resolves. A pure human-authored change cites nothing and passes freely. -/

/-- A change together with the ids of the Wiki reflections that motivated it. -/
public structure ReflectedChange where
  change : Change
  motivations : Array NonBlank := #[]
  deriving Repr

/-- Every cited motivation is a reflection the Wiki actually holds. Empty is
vacuously coherent (a human-authored change motivated by nothing). -/
public def ReflectedChange.coherentInWiki (w : Wiki) (rc : ReflectedChange) : Bool :=
  rc.motivations.all (fun m => w.hasId m.value)

/-- Refusal reasons. `uncited` is the new gate; `archive` forwards the ordinary
archive refusal (e.g. no human accept). -/
public inductive ReflectedArchiveError where
  | uncited
  | archive (e : ArchiveError)
  deriving Repr, BEq

/-- Archive a change together with its Wiki motivations. A citation the Wiki does not
hold is refused before the human gate is consulted; otherwise this delegates to the
ordinary `SpecSnapshot.archive`. Coherence is thus a precondition of success. -/
public def SpecSnapshot.archiveWithReflections
    (s : SpecSnapshot) (rc : ReflectedChange) (w : Wiki) (gate : ArchiveDecision) :
    Except ReflectedArchiveError SpecSnapshot :=
  if rc.coherentInWiki w then
    match s.archive rc.change gate with
    | .ok s' => .ok s'
    | .error e => .error (.archive e)
  else
    .error .uncited

/-- A change citing a reflection the Wiki lacks is refused, whatever the gate says. -/
public theorem archiveWithReflections_uncited
    {s : SpecSnapshot} {rc : ReflectedChange} {w : Wiki} {gate : ArchiveDecision}
    (h : rc.coherentInWiki w = false) :
    s.archiveWithReflections rc w gate = .error .uncited := by
  simp [SpecSnapshot.archiveWithReflections, h]

/-- A successful reflected-archive proves every cited motivation was in the Wiki. -/
public theorem archiveWithReflections_ok_coherent
    {s : SpecSnapshot} {rc : ReflectedChange} {w : Wiki} {gate : ArchiveDecision}
    {s' : SpecSnapshot} (h : s.archiveWithReflections rc w gate = .ok s') :
    rc.coherentInWiki w = true := by
  unfold SpecSnapshot.archiveWithReflections at h
  split at h
  · next hc => exact hc
  · simp at h

/-! ## Capability-gated entry points

Maintenance (`Wiki.record`) and promotion-proposal are *ambient* on the bare
functions; downstream callers go through these capability-gated wrappers instead.
`WikiAccess` says who may do what; the mapping from a principal/authority to a
`WikiAccess` level is downstream company-pack policy. Acceptance of a promotion
remains a human gate (`archiveWithReflections`) — `promoteCandidate` is proposal
authority only, so the valve stays singular. -/

/-- Refusal reason for a capability-gated agent-knowledge operation. -/
public inductive AccessError where
  | insufficientCapability (held required : WikiAccess)
  deriving Repr, BEq

/-- **Capability-gated maintainer fold.** Recording requires at least `.maintain`. -/
public def Wiki.recordWith (cap : WikiAccess) (w : Wiki) (r : Reflection) :
    Except AccessError Wiki :=
  if cap.canMaintain then .ok (w.record r)
  else .error (.insufficientCapability cap .maintain)

/-- Recording below `.maintain` refuses. -/
public theorem Wiki.recordWith_refuses
    {cap : WikiAccess} {w : Wiki} {r : Reflection} (h : cap.canMaintain = false) :
    w.recordWith cap r = .error (.insufficientCapability cap .maintain) := by
  simp [Wiki.recordWith, h]

/-- A successful gated record proves the caller could maintain, and yields the same
value as the bare fold. -/
public theorem Wiki.recordWith_ok
    {cap : WikiAccess} {w w' : Wiki} {r : Reflection} (h : w.recordWith cap r = .ok w') :
    cap.canMaintain = true ∧ w' = w.record r := by
  unfold Wiki.recordWith at h
  split at h
  · next hc => exact ⟨hc, by injection h with h; exact h.symm ▸ rfl⟩
  · contradiction

/-- **Capability-gated promotion proposal.** Producing the `ReflectedChange` that a
human gate will adjudicate requires at least `.promoteCandidate`. The proposal must
also be Wiki-coherent (every motivation is a reflection the Wiki holds), so a
fabricated motivation cannot even be proposed. -/
public def Wiki.proposePromotion (cap : WikiAccess) (w : Wiki) (rc : ReflectedChange) :
    Except AccessError ReflectedChange :=
  if cap.canPropose then
    if rc.coherentInWiki w then .ok rc
    else .error (.insufficientCapability cap .promoteCandidate)
  else .error (.insufficientCapability cap .promoteCandidate)

/-- Proposing below `.promoteCandidate` refuses. -/
public theorem Wiki.proposePromotion_refuses
    {cap : WikiAccess} {w : Wiki} {rc : ReflectedChange} (h : cap.canPropose = false) :
    w.proposePromotion cap rc = .error (.insufficientCapability cap .promoteCandidate) := by
  simp [Wiki.proposePromotion, h]

/-- A successful proposal proves both capability and Wiki-coherence — so the
downstream human gate never sees a proposal with fabricated provenance. -/
public theorem Wiki.proposePromotion_ok
    {cap : WikiAccess} {w : Wiki} {rc rc' : ReflectedChange}
    (h : w.proposePromotion cap rc = .ok rc') :
    cap.canPropose = true ∧ rc.coherentInWiki w = true ∧ rc' = rc := by
  unfold Wiki.proposePromotion at h
  split at h
  · next hcap =>
    split at h
    · next hcoh => exact ⟨hcap, hcoh, by injection h with h; exact h.symm⟩
    · contradiction
  · contradiction

end

/-! ## Worked examples (executable `#guard`s) -/

private def nb (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : NonBlank := ⟨s, h⟩

private def rid (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : ReflectionId := ⟨s, h⟩

private def runid (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : RunId := ⟨s, h⟩

private def r1 : Reflection :=
  { id := rid "wiki.enum-canary", kind := .pattern
    learning := nb "round-trip guards catch enum typos"
    derivedFrom := ⟨#[runid "run-001", runid "run-002"], by native_decide⟩ }

private def r1' : Reflection :=  -- same learning, overlapping + new run
  { id := rid "wiki.enum-canary", kind := .pattern
    learning := nb "round-trip guards catch enum typos"
    derivedFrom := ⟨#[runid "run-002", runid "run-003"], by native_decide⟩ }

private def r2 : Reflection :=  -- different learning
  { id := rid "wiki.read-first", kind := .strategy
    learning := nb "read the snapshot before proposing a delta"
    derivedFrom := ⟨#[runid "run-009"], by native_decide⟩ }

-- Recording one reflection mints a content-canonical consolidated node AND keeps the
-- primary: two entries, unique ids, a supersedes edge. The canonical id IS the
-- learning text.
#guard
  let w := Wiki.record {} r1
  w.entries.size == 2 && w.relations.size == 1 &&
    w.hasId "wiki.enum-canary" &&                          -- original kept
    w.hasId "round-trip guards catch enum typos"           -- canonical id = learning

-- Effective readback returns the canonical node (provenance carried); the superseded
-- original drops out.
#guard
  let w := Wiki.record {} r1
  (w.effectiveByKind .pattern).size == 1 &&
    match (w.effectiveByKind .pattern)[0]? with
    | some c => c.id.value == "round-trip guards catch enum typos" &&
                c.derivedFrom.items.map (·.value) == #["run-001", "run-002"]
    | none => false

-- Recording the same learning again folds provenance into the SAME canonical node
-- (stable content id) and never duplicates an id.
#guard
  let w := Wiki.record (Wiki.record {} r1) r1'
  w.entries.size == 2 &&
    match (w.effectiveByKind .pattern)[0]? with
    | some c => c.derivedFrom.items.map (·.value) == #["run-001", "run-002", "run-003"]
    | none => false

-- A different learning mints its own canonical node; ids stay unique; each kind's
-- effective view is its one canonical node.
#guard
  let w := Wiki.record (Wiki.record {} r1) r2
  w.entries.size == 4 &&
    (w.effectiveByKind .pattern).size == 1 && (w.effectiveByKind .strategy).size == 1

-- History: the supersedes edge points from the canonical node to the kept original.
#guard
  let w := Wiki.record {} r1
  w.relations.any (fun m => m.kind == .supersedes &&
    m.source.value == "round-trip guards catch enum typos" &&
    m.target.value == "wiki.enum-canary")

-- Merge takes the join of classifications: consolidating an internal and a
-- sensitive reflection yields sensitive (consolidation raises, never lowers).
#guard
  let ai : Reflection := { r1 with classification := .internal }
  let bs : Reflection := { r1' with classification := .sensitive }
  match Reflection.merge ai bs with
  | some m => m.classification == .sensitive
  | none => false



/-! ### The valve: change motivations gated against the Wiki -/

private def wiki2 : Wiki := Wiki.record (Wiki.record {} r1) r2

private def exScenarioW : Scenario :=
  { name := ⟨"n", by native_decide⟩
    whenText := ⟨"w", by native_decide⟩
    thenText := ⟨"t", by native_decide⟩
    check := .executable }

private def exReqW : Requirement :=
  { id := ⟨"cap.x", by native_decide⟩
    shall := ⟨"do x", by native_decide⟩
    scenarios := ⟨#[exScenarioW], by decide⟩ }

private def exChgW : Change :=
  { id := ⟨"chg-x", by native_decide⟩
    why := ⟨"because", by native_decide⟩
    deltas := ⟨#[.added exReqW], by decide⟩ }

-- Cites a kept original the Wiki holds → coherent.
#guard ({ change := exChgW, motivations := #[nb "wiki.enum-canary"] } : ReflectedChange).coherentInWiki wiki2
-- Cites a reflection the Wiki lacks → refused.
#guard !({ change := exChgW, motivations := #[nb "wiki.ghost"] } : ReflectedChange).coherentInWiki wiki2
-- Pure human-authored change (no motivation) → allowed; the valve never forces the coupling.
#guard ({ change := exChgW } : ReflectedChange).coherentInWiki wiki2

-- The archive gate refuses an uncited change before the human gate is consulted.
private def emptySnap : SpecSnapshot := ⟨#[], by native_decide, #[], by native_decide, by native_decide⟩
private def isUncited : Except ReflectedArchiveError SpecSnapshot → Bool
  | .error .uncited => true
  | _ => false
#guard isUncited (emptySnap.archiveWithReflections
  { change := exChgW, motivations := #[nb "wiki.ghost"] } wiki2 .accepted)

/-! ### Capability-gated entry points -/

private def isRecordOk : Except AccessError Wiki → Bool
  | .ok _ => true | .error _ => false

-- Maintainer fold refuses below .maintain, succeeds at .maintain and above.
#guard !isRecordOk (Wiki.recordWith .readEffective {} r1)
#guard isRecordOk (Wiki.recordWith .maintain {} r1)
#guard isRecordOk (Wiki.recordWith .promoteCandidate {} r1)

private def isProposeOk : Except AccessError ReflectedChange → Bool
  | .ok _ => true | .error _ => false

-- Promotion proposal needs .promoteCandidate AND a Wiki-coherent motivation.
-- Refused below .promoteCandidate even with a coherent motivation.
#guard !isProposeOk (wiki2.proposePromotion .maintain
  { change := exChgW, motivations := #[nb "wiki.enum-canary"] })
-- Allowed at .promoteCandidate with a motivation the Wiki holds (the kept original).
#guard isProposeOk (wiki2.proposePromotion .promoteCandidate
  { change := exChgW, motivations := #[nb "wiki.enum-canary"] })
-- Refused at .promoteCandidate when the motivation is fabricated (not in the Wiki):
-- no proposal with fabricated provenance ever reaches the human gate.
#guard !isProposeOk (wiki2.proposePromotion .promoteCandidate
  { change := exChgW, motivations := #[nb "wiki.ghost"] })

end LeanSpec
