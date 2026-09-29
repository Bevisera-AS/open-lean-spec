module

public import LeanSpec.Validated
public meta import LeanUtil

/-!
# Kb: a generic, assurance-indexed knowledge core

The human spec store (`SpecSnapshot`) and the agent wiki (`Wiki`) are two
*instances* of a single structure, and the trust properties (traceability,
provenance-preservation, defeasible resolution, gated promotion, redaction) belong
on that structure and are proved **once**. This core is wired into the library:
`LeanSpec/KbAdapter/*` proves the existing domain operations correspond to the
generic ones, and `Wiki` delegates its provenance-union and defeasible-resolution
to `Kb.dedupUnion` / `Kb.defeated` (so `Validated → Kb → Wiki`, acyclic — `Kb`
imports only `Validated`).

The four design commitments this sketch encodes, in response to the obvious ways
a naive "one flat type" would be unsound:

1. **Assurance is a type INDEX, not a field.** `Item a P S` is indexed by its
   assurance level `a`. The only door that produces an item at a *higher* level is
   `promote`, and `promote` demands a `Gate`. Because there is no other producer at
   a higher index, "assurance can only rise through a gate" is the *shape* of the
   API, not a runtime check we hope holds.

2. **Merge takes the MEET of assurance (anti-laundering).** Consolidating two
   items unions their provenance (it grows) but lowers assurance to the weaker of
   the two (`merge_assurance_le_both`). This closes the second door: an agent-
   provisional item cannot launder itself into the trusted tier by sharing a
   `sameAs` key with a proved item.

3. **Citations resolve cross-store WITHOUT inheriting assurance.** A proved spec
   item may *cite* a provisional reflection (the "valve"). `coherentVia`
   checks the cited source exists; it never raises the source nor lowers the
   citer. This is "differ in degree, not kind" made formal.

4. **Payload validity stays in `P`.** The core owns identity, provenance,
   assurance, relations, promotion. It does NOT own "what makes this payload
   well-formed" — that is `[Identified P]` plus whatever proofs `P` carries
   internally (`Requirement`'s `NonEmptyArray Scenario`, etc.). Keep this boundary
   crisp or the core stops being generic.

`Kb` imports only `Validated` (and `LeanUtil`); it depends on no domain module, so
`Snapshot`/`Wiki`/`Reflection`/`Determination` are free to instantiate it.

## Trust boundary (what is in the trusted computing base, and why)

The generic **guarantees** in this file — `merge_assurance_le_both`,
`merge_preserves_provenance`, `coherentVia_rejects_unknown`,
`promote_lands_at_target`, `toProved_carries_gate`,
`no_direct_provisional_to_proved`, `defeated_false_of_sources_absent`,
`effectiveIds_undefeated`, `admit_redacted`, and the consolidation write-path laws
`mergeStep_map_uniqueIds`, `push_uniqueIds`, `record_preserves_provenance` — are
proved with kernel tactics (`simp`, `cases`, `omega`, `rfl`, `congr`). They do
**not** depend on `native_decide` (only `propext`/`Quot.sound`), so the guarantees
rest on the Lean kernel alone.

`native_decide` still appears in three narrow, deliberate roles, none of which is a
guarantee:

1. **Example `#guard`s and literal test data.** The worked examples below and the
   `nb`/`rid`/`runid` smart-constructor defaults discharge `nonemptyText "..."` on
   fixed string literals. These are compile-time sanity checks, not the library's
   theorems.

2. **Invariant defaults on store constructors** (`SpecSnapshot.uniqueDesignIds`,
   `designsLinked`, `empty`; `NonEmptyArray` size proofs). These establish a
   decidable predicate about a *concrete* array at construction time.

3. **Fixed-string cleanliness lemmas** for redaction (`redactMarker_clean` and the
   adapters' `redactedLearning_clean`/`specRedacted_clean`).

Roles 2 and 3 are load-bearing but **cannot** be moved to kernel `decide`: every
predicate here bottoms out in `String` operations (`nonemptyText`, `splitOn`,
`Nodup`/`Pairwise` over `.value` strings), and the Lean kernel does not reduce
`String` computations — plain `decide` gets stuck even on `#[]` or `"[REDACTED]"`.
The realistic alternatives are `native_decide` (trusts the compiler + the
`Decidable` instance) or a bespoke `simp` proof with `String` lemmas. We keep
`native_decide` for these, and localise it: it never gates a generic guarantee,
only the construction of concrete values whose predicate the kernel cannot evaluate
directly.

Other TCB caveats documented elsewhere: `CheckStatus.executable` is a *claim* a
named checker exists, not its kernel derivation (`Types.lean`); atomic-write
crash-safety is not a kernel theorem (`Store.lean`).
-/

namespace LeanSpec.Kb

open LeanSpec

public section

/-! ## Assurance: the trust index

Ordered lattice of how much we trust an item. `provisional` is the agent wiki's
resting level (never proved true, only provenance-honest). `coherent` is
"references check out" (the precedent/coherence gate). `proved` is the spec
store's level (kernel-checked obligations discharged). The order and the meet are
what make the anti-laundering law expressible. -/
public inductive Assurance where
  | provisional
  | coherent
  | proved
  deriving Repr, BEq, DecidableEq

/-- Numeric rank; higher is more trusted. Used to define `≤` and `⊓` concretely. -/
@[expose] public def Assurance.rank : Assurance → Nat
  | .provisional => 0
  | .coherent    => 1
  | .proved      => 2

/-- `a ≤ b` when `a` is no more trusted than `b`. -/
public def Assurance.le (a b : Assurance) : Bool := a.rank ≤ b.rank

/-- Meet (greatest lower bound): the *weaker* of two assurances. -/
@[expose] public def Assurance.meet (a b : Assurance) : Assurance :=
  if a.rank ≤ b.rank then a else b

/-- The meet is ≤ its left argument. -/
public theorem Assurance.meet_le_left (a b : Assurance) :
    (a.meet b).le a = true := by
  simp only [Assurance.meet, Assurance.le]
  split
  · next h => simp
  · next h => simp; omega

/-- The meet is ≤ its right argument. -/
public theorem Assurance.meet_le_right (a b : Assurance) :
    (a.meet b).le b = true := by
  simp only [Assurance.meet, Assurance.le]
  split
  · next h => simp; omega
  · next h => simp

/-! ## Identity: what `P` must expose to live in the store

The core addresses items by id; it does not care what `P` *is* beyond that. This
is the whole generic boundary — `Requirement`, `Reflection`, `ProcessSkill` each
give an `Identified` instance and keep their own internal invariants. -/
public class Identified (P : Type) where
  idOf : P → String

/-! ## Item: a payload + provenance, indexed by assurance

`S` is the provenance source type — `RunId` for the agent axis, an author/why ref
for the human axis. Provenance is non-empty by construction: an item with no
justification cannot exist, on either axis. -/
public structure Item (a : Assurance) (P S : Type) where
  payload    : P
  provenance : NonEmptyArray S

@[expose] public def Item.id {a : Assurance} {P S : Type} [Identified P] (i : Item a P S) : String :=
  Identified.idOf i.payload

/-! ## The store: items at MIXED assurance, unique ids

One store holds items at different assurance levels (`Sigma` over the index), so a
single `Store` can model a snapshot that is mostly `proved` with a few `coherent`
rows, or a wiki that is all `provisional`. Uniqueness of id is the generic
analogue of `SpecSnapshot.uniqueIds`, proved here once for all instances. -/
public structure Boxed (P S : Type) where
  assurance : Assurance
  item      : Item assurance P S

@[expose] public def Boxed.id {P S : Type} [Identified P] (b : Boxed P S) : String :=
  b.item.id

public abbrev UniqueIds {P S : Type} [Identified P] (items : Array (Boxed P S)) : Prop :=
  (items.map Boxed.id).toList.Nodup

public instance {P S : Type} [Identified P] (items : Array (Boxed P S)) :
    Decidable (UniqueIds items) := inferInstance

public structure Store (P S : Type) [Identified P] where
  items     : Array (Boxed P S)
  uniqueIds : UniqueIds items

public def Store.hasId {P S : Type} [Identified P] (st : Store P S) (idv : String) : Bool :=
  decide (idv ∈ (st.items.map Boxed.id).toList)

/-! ## Provenance union — grows, never shrinks (the traceability law)

Generic version of `Wiki.dedupUnion`. Keeps `a` as a verbatim prefix so
preservation of `a`'s provenance is immediate and non-emptiness survives. -/
@[expose] public def dedupUnion {S : Type} [BEq S] (a b : Array S) : Array S :=
  a ++ b.filter (fun x => !a.contains x)

public theorem dedupUnion_size_pos {S : Type} [BEq S] {a b : Array S} (h : 0 < a.size) :
    0 < (dedupUnion a b).size := by
  simp only [dedupUnion, Array.size_append]; omega

public theorem mem_dedupUnion_left {S : Type} [BEq S] {a b : Array S} {x : S}
    (hx : x ∈ a) : x ∈ dedupUnion a b := by
  simp only [dedupUnion, Array.mem_append]
  exact Or.inl hx

/-! ## Consolidation — one `record`/`merge`, proved once

`merge` unions provenance and takes the MEET of assurance. The result is boxed at
the meet, so its *type index* records the weaker level. This is the anti-laundering
law: you cannot end up more trusted than the weaker input. -/
@[expose] public def merge {P S : Type} [Identified P] [BEq S]
    (keep : P) (x : Boxed P S) (y : Boxed P S)
    (_hx : Identified.idOf keep = x.id) : Boxed P S :=
  let a := x.assurance.meet y.assurance
  { assurance := a
    item :=
      { payload := keep
        provenance :=
          ⟨dedupUnion x.item.provenance.items y.item.provenance.items,
           dedupUnion_size_pos x.item.provenance.property⟩ } }

/-- **Anti-laundering.** The merged assurance is ≤ both inputs. Proved once; every
domain that consolidates inherits it. -/
public theorem merge_assurance_le_both {P S : Type} [Identified P] [BEq S]
    (keep : P) (x y : Boxed P S) (_hx : Identified.idOf keep = x.id) :
    (merge keep x y _hx).assurance.le x.assurance = true ∧
      (merge keep x y _hx).assurance.le y.assurance = true := by
  refine ⟨?_, ?_⟩
  · simpa [merge] using Assurance.meet_le_left x.assurance y.assurance
  · simpa [merge] using Assurance.meet_le_right x.assurance y.assurance

/-- **Provenance preservation.** Every source justifying `x` still justifies the
merge. Generic version of `Wiki.merge_preserves_provenance`. -/
public theorem merge_preserves_provenance {P S : Type} [Identified P] [BEq S]
    (keep : P) (x y : Boxed P S) (_hx : Identified.idOf keep = x.id)
    {s : S} (hs : s ∈ x.item.provenance.items) :
    s ∈ (merge keep x y _hx).item.provenance.items := by
  simp only [merge]
  exact mem_dedupUnion_left hs

/-! ## The consolidation write-path — `Store.record`, the missing generic op

`merge` consolidates two items; `record` is the store-level insert-or-consolidate
that both axes need: find an entry matching `sameAs` (by id, or by content like the
wiki's same-kind-same-learning), merge into it (keeping that entry's id, unioning
provenance, meeting assurance), otherwise append. It is the generic form of
`Wiki.record`'s hand-rolled `findIdx?`/`set!`/`push` and `SpecSnapshot`'s bespoke
`unique_push`/`unique_replace`, and — unlike either — it is **proved to preserve
`uniqueIds`**. A new item whose id already exists but matches no `sameAs` entry is
refused (the store is returned unchanged) rather than silently duplicating an id,
so uniqueness is an invariant of the write path, not a hope. -/

/-- The merge-or-keep step `record` maps over each entry: consolidate into a match,
leave a non-match untouched. -/
@[expose] public def mergeStep {P S : Type} [Identified P] [BEq S]
    (sameAs : Boxed P S → Bool) (a : Assurance) (i : Item a P S) (b : Boxed P S) : Boxed P S :=
  if sameAs b then merge b.item.payload b ⟨a, i⟩ rfl else b

/-- `mergeStep` never changes an entry's id: a merge keeps the matched entry's
payload (hence its id), and a non-match is untouched. This is exactly what makes
`record` preserve `uniqueIds`. -/
public theorem mergeStep_id {P S : Type} [Identified P] [BEq S]
    (sameAs : Boxed P S → Bool) (a : Assurance) (i : Item a P S) (b : Boxed P S) :
    (mergeStep sameAs a i b).id = b.id := by
  simp only [mergeStep]
  split <;> rfl

/-- Consolidating (mapping `mergeStep`) leaves the id-list identical, so uniqueness
survives — the generic analogue of `SpecSnapshot.unique_replace`. -/
public theorem mergeStep_map_uniqueIds {P S : Type} [Identified P] [BEq S]
    (st : Store P S) (sameAs : Boxed P S → Bool) (a : Assurance) (i : Item a P S) :
    UniqueIds (st.items.map (mergeStep sameAs a i)) := by
  have hids : (st.items.map (mergeStep sameAs a i)).map Boxed.id
      = st.items.map Boxed.id := by
    rw [Array.map_map]
    congr 1
    funext b
    simp only [Function.comp_apply]
    exact mergeStep_id sameAs a i b
  simp only [UniqueIds, hids]
  exact st.uniqueIds

/-- `hasId` false means the id is absent from the id-list — the generic analogue of
`SpecSnapshot.not_has_not_mem`. -/
public theorem Store.not_hasId_not_mem {P S : Type} [Identified P]
    {st : Store P S} {idv : String} (h : st.hasId idv = false) :
    idv ∉ (st.items.map Boxed.id).toList :=
  of_decide_eq_false h

/-- Appending a fresh-id item preserves uniqueness — the generic analogue of
`SpecSnapshot.unique_push`. -/
public theorem push_uniqueIds {P S : Type} [Identified P]
    (st : Store P S) (a : Assurance) (i : Item a P S)
    (hFresh : st.hasId (Item.id i) = false) :
    UniqueIds (st.items.push ⟨a, i⟩) := by
  simp only [UniqueIds, Array.map_push, Array.toList_push]
  rw [List.nodup_append]
  refine ⟨st.uniqueIds, by simp, ?_⟩
  intro x hx y hy
  have hy' : y = Boxed.id (⟨a, i⟩ : Boxed P S) := by simp_all
  subst hy'
  intro hEq
  subst hEq
  exact Store.not_hasId_not_mem hFresh hx

/-- **Insert-or-consolidate.** Merge into the first `sameAs`-matching entry, else
append a fresh-id item, else (colliding id, no content match) refuse. `uniqueIds` is
discharged by construction in every branch. -/
@[expose] public def Store.record {P S : Type} [Identified P] [BEq S]
    (st : Store P S) (sameAs : Boxed P S → Bool) (a : Assurance) (i : Item a P S) :
    Store P S :=
  if st.items.any sameAs then
    ⟨st.items.map (mergeStep sameAs a i), mergeStep_map_uniqueIds st sameAs a i⟩
  else if h : st.hasId (Item.id i) = true then
    st
  else
    ⟨st.items.push ⟨a, i⟩, push_uniqueIds st a i (by simpa using h)⟩

/-- **Provenance is preserved by `record`.** When `record` consolidates into a
matching entry, every source that justified that entry still justifies it
afterwards. Nothing that was recorded is lost. -/
public theorem record_preserves_provenance {P S : Type} [Identified P] [BEq S]
    (st : Store P S) (sameAs : Boxed P S → Bool) (a : Assurance) (i : Item a P S)
    (b : Boxed P S) (_hb : b ∈ st.items) (hmatch : sameAs b = true)
    {s : S} (hs : s ∈ b.item.provenance.items) :
    s ∈ (mergeStep sameAs a i b).item.provenance.items := by
  unfold mergeStep
  rw [if_pos hmatch]
  simp only [merge]
  exact mem_dedupUnion_left hs

/-! ## Coherence — one check, cross-store

`coherentVia resolve srcs` holds when every cited source is resolvable. `resolve`
is the store-crossing hook: for the valve, a proved spec item cites a provisional
reflection; `resolve` confirms the reflection exists but the citer's assurance is
untouched (it is not a function of `resolve`). Generic version of
`Reflection.coherentIn` / `Morphism.coherentInWiki` / `ReflectedChange.coherentInWiki`. -/
@[expose] public def coherentVia {S : Type} (resolve : S → Bool) (srcs : Array S) : Bool :=
  srcs.all resolve

/-- **Refusal of fabricated provenance.** A source that does not resolve makes the
whole citation incoherent. One theorem replaces the per-axis `_rejects_unknown`
lemmas. -/
public theorem coherentVia_rejects_unknown {S : Type}
    {resolve : S → Bool} {srcs : Array S} {x : S}
    (hx : x ∈ srcs) (hbad : resolve x = false) :
    coherentVia resolve srcs = false := by
  simp only [coherentVia]
  cases hc : srcs.all resolve with
  | false => rfl
  | true =>
    rw [Array.all_eq_true_iff_forall_mem] at hc
    have := hc x hx
    rw [hbad] at this
    exact absurd this (by simp)

/-! ## The gate — attributed, not a boolean

Turn-1's accountability gap fixed once: the gate carries *who* approved and *what*
(a content hash), so `promote_ok` can testify to both. `Gate` is opaque payload
here; a real impl signs it. -/
public structure Gate where
  approver    : NonBlank
  contentHash : NonBlank
  deriving Repr

/-! ## Redaction — privacy as a class obligation, proved once

`Redactable P` says `P` knows how to scrub itself, and `redact` is idempotent:
scrubbing twice is the same as once (`redact_idempotent`). Because `record` and
`promote` scrub on the way in, nothing crosses a store boundary un-redacted — the
audit trail and the wiki are protected by the *same* obligation, discharged once
per payload type rather than re-argued per axis. This is the formal home for the
turn-1 privacy gap, which had no model on either axis. -/
public class Redactable (P : Type) where
  redact : P → P
  redact_idempotent : ∀ p, redact (redact p) = redact p

/-- Scrub a whole item's payload. Provenance (run ids / author refs) is assumed
non-sensitive by construction here; a stricter model would redact `S` too. -/
public def Item.redact {a : Assurance} {P S : Type} [Redactable P] (i : Item a P S) :
    Item a P S :=
  { payload := Redactable.redact i.payload, provenance := i.provenance }

/-- Redacting an item is idempotent, inherited directly from the payload law. -/
public theorem Item.redact_idempotent {a : Assurance} {P S : Type} [Redactable P]
    (i : Item a P S) : i.redact.redact = i.redact := by
  simp only [Item.redact, Redactable.redact_idempotent]

/-! ## The obligation stack — transition-indexed, replacing the boolean gate

`Obligation from to` is inhabited *only* for the legal assurance transitions, and
each constructor carries exactly the evidence that transition requires:

* `refl a` — a no-op re-box at the same level (needs nothing).
* `toCoherent` — `provisional → coherent`: a proof the citations resolve
  (`coherentVia … = true`). This is the precedent/coherence gate.
* `toProved` — `coherent → proved`: an *attributed* `Gate` (approver + content
  hash). This is the human-authority gate, and it is the only path to `.proved`.

Because the type is indexed by `(from, to)`, you cannot call `promote` into
`.proved` while holding only a coherence proof: there is no `Obligation .provisional
.proved` constructor at all. Illegal or under-evidenced transitions are type errors,
not runtime `false`. -/
public inductive Obligation : Assurance → Assurance → Type where
  | refl (a : Assurance) : Obligation a a
  | toCoherent (coherenceHolds : Bool) (h : coherenceHolds = true) :
      Obligation .provisional .coherent
  | toProved (g : Gate) : Obligation .coherent .proved

/-- **Promotion is the only assurance-raising door**, and the obligation type says
what each raise costs. Given an `Obligation a a'`, re-box the (redacted) payload at
`a'`. No other function in the core produces an item at a higher index, and the
only inhabitants of `Obligation` are the three legal transitions above — so the API
*shape* is the guarantee. -/
@[expose] public def promote {P S : Type} [Identified P] [Redactable P] {a a' : Assurance}
    (i : Item a P S) (_obl : Obligation a a') :
    Boxed P S :=
  -- Re-box the (redacted) payload+provenance at the target index `a'`. We cannot
  -- reuse `i.redact` directly: `Item a P S` and `Item a' P S` are distinct types,
  -- so the only producer at `a'` is right here, behind the `Obligation`.
  { assurance := a'
    item := { payload := Redactable.redact i.payload, provenance := i.provenance } }

/-- **Assurance can only be what the obligation targeted.** A promotion lands at
exactly the level its `Obligation` is indexed to — you cannot end up more trusted
than the transition you discharged. -/
public theorem promote_lands_at_target {P S : Type} [Identified P] [Redactable P]
    {a a' : Assurance} (i : Item a P S) (obl : Obligation a a') :
    (promote i obl).assurance = a' := rfl

/-- **The only door to `.proved` is `toProved`, which carries an attributed gate.**
If a promotion reaches `.proved` from `.coherent`, it did so via a `toProved g`, so
the caller can log *who* (`g.approver`) approved *what* (`g.contentHash`) at exactly
this transition. Accountability is in the type: there is no other constructor
producing `Obligation _ .proved`. -/
public theorem toProved_carries_gate
    (obl : Obligation .coherent .proved) :
    ∃ g : Gate, obl = .toProved g := by
  cases obl with
  | toProved g => exact ⟨g, rfl⟩

/-- **No shortcut to `.proved`.** There is no obligation witnessing a direct
`provisional → proved` jump; the type is uninhabited. Reaching `.proved` therefore
*must* pass through `.coherent` (the coherence gate) and then `toProved` (the human
gate) — the two-gate discipline is enforced by construction, not convention. -/
public theorem no_direct_provisional_to_proved
    (obl : Obligation .provisional .proved) : False := by
  cases obl

/-- Everything entering the store is redacted first, uniformly. `record` is the
provenance-preserving consolidator (see `merge`); this is the redacted admission
point that both axes share. -/
@[expose] public def admit {P S : Type} [Identified P] [Redactable P] {a : Assurance}
    (i : Item a P S) : Boxed P S :=
  { assurance := a, item := i.redact }

/-- An admitted item is redacted — re-admitting changes nothing further. Privacy is
idempotent at the boundary, proved once for every payload type. -/
public theorem admit_redacted {P S : Type} [Identified P] [Redactable P] {a : Assurance}
    (i : Item a P S) : (admit i).item.redact = (admit i).item := by
  simp only [admit, Item.redact_idempotent]

/-! ## Defeasible relations — one resolution layer for both axes

`Determination.defeated`/`effective` (regulatory decisions superseding each other)
and `Wiki.superseded`/`effectiveByKind` (a later strategy retiring an earlier
failure-mode) are the *same* algorithm written twice: a relation defeats its target
only while its source is still "present," and effective-readback keeps the
undefeated. The only real difference is what "present" means — `Determination`
requires present-*and-active*, `Wiki` requires merely present. That difference is
exactly a `present : String → Bool` parameter.

Relations are addressed by string id (the `RelationId` the ambient system uses),
matching how `Morphism` addresses determinations/reflections. The core owns *when a
relation defeats*; it does not own what a payload is, so this composes with any
`Store P S`. -/

/-- Which relations, when live, defeat their target. Mirrors `MorphismKind`;
`precedentFor`-style relations inform without defeating. -/
public inductive RelationKind where
  | supersedes
  | exceptionOf
  | precedentFor
  deriving Repr, BEq, DecidableEq

@[expose] public def RelationKind.defeats : RelationKind → Bool
  | .supersedes  => true
  | .exceptionOf => true
  | .precedentFor => false

/-- A relation between two items, addressed by id. -/
public structure Relation where
  kind   : RelationKind
  source : String
  target : String
  deriving Repr, BEq

/-- `targetId` is defeated when some defeating relation targets it *and* its source
is present, per `present`. A retracted (absent) source does not defeat — this is
what makes the layer defeasible rather than monotone. Parameterising `present` is
what unifies the two axes: pass `isPresentAndActive` for determinations, `isPresent`
for the wiki. -/
@[expose] public def defeated (present : String → Bool) (rels : List Relation) (targetId : String) : Bool :=
  rels.any fun r => r.kind.defeats && r.target == targetId && present r.source

/-- **A retracted source never defeats.** If every defeating relation aimed at
`targetId` has an absent source, `targetId` is undefeated. This is the generic form
of "a retracted defeater does not defeat" that both `Determination` and `Wiki`
prove separately today. -/
public theorem defeated_false_of_sources_absent
    {present : String → Bool} {rels : List Relation} {targetId : String}
    (h : ∀ r ∈ rels, r.kind.defeats = true → r.target = targetId → present r.source = false) :
    defeated present rels targetId = false := by
  simp only [defeated]
  rw [List.any_eq_false]
  intro r hmem
  simp only [Bool.and_eq_true, beq_iff_eq]
  intro hr
  obtain ⟨⟨hdef, htgt⟩, hpres⟩ := hr
  have := h r hmem hdef htgt
  rw [this] at hpres
  exact absurd hpres (by simp)

/-- Effective readback over a store's item ids: those not defeated under `present`.
Generic form of `Determination.effective`'s undefeated filter and
`Wiki.effectiveByKind`. Resolution is total (a `filter`, never partial). -/
public def effectiveIds (present : String → Bool) (rels : List Relation)
    (ids : List String) : List String :=
  ids.filter (fun id => !defeated present rels id)

/-- **Effective readback returns only undefeated ids.** The generic version of
`Determination.effective_active`'s "kept ⇒ undefeated" and
`Wiki.effectiveByKind_sound`. -/
public theorem effectiveIds_undefeated
    {present : String → Bool} {rels : List Relation} {ids : List String} {id : String}
    (h : id ∈ effectiveIds present rels ids) :
    defeated present rels id = false := by
  simp only [effectiveIds, List.mem_filter] at h
  have := h.2
  cases hd : defeated present rels id with
  | false => rfl
  | true => rw [hd] at this; exact absurd this (by simp)

/-- **Effective ids are a subset of the input.** Nothing is invented during
resolution — a companion to totality. -/
public theorem effectiveIds_mem
    {present : String → Bool} {rels : List Relation} {ids : List String} {id : String}
    (h : id ∈ effectiveIds present rels ids) : id ∈ ids := by
  simp only [effectiveIds, List.mem_filter] at h
  exact h.1

end

/-! ## Do the two axes fall out? Worked instantiation.

Two toy payloads standing in for `Requirement` (human, `proved`) and `Reflection`
(agent, `provisional`), each with an `Identified` instance. The point is only to
show the generic ops typecheck and run on both — not to reproduce their real
payload invariants. -/

private structure HumanReq where
  reqId : String
  shall : String

private structure AgentReflection where
  refId    : String
  learning : String

private instance : Identified HumanReq where idOf r := r.reqId
private instance : Identified AgentReflection where idOf r := r.refId

-- Toy redaction: if the field looks sensitive (contains a "SECRET:" marker),
-- clamp it to a fixed placeholder. Idempotent by construction: the placeholder
-- contains no marker, so a second pass is the identity. This clamp-to-fixpoint
-- shape is trivially provable and is the realistic model for regulated redaction
-- (replace, don't try to surgically edit).
private def redactMarker : String := "[REDACTED]"

private def sensitive (s : String) : Bool := (s.splitOn "SECRET:").length != 1

private def scrub (s : String) : String :=
  if sensitive s then redactMarker else s

private theorem redactMarker_clean : sensitive redactMarker = false := by native_decide

private theorem scrub_idem (s : String) : scrub (scrub s) = scrub s := by
  unfold scrub
  split
  · -- outer input was sensitive → inner is `redactMarker`, which is not sensitive
    rw [if_neg (by rw [redactMarker_clean]; decide)]
  · -- outer input was already clean → inner sees the same (clean) string
    rfl

private instance : Redactable HumanReq where
  redact r := { r with shall := scrub r.shall }
  redact_idempotent r := by simp only [scrub_idem]

private instance : Redactable AgentReflection where
  redact r := { r with learning := scrub r.learning }
  redact_idempotent r := by simp only [scrub_idem]

private def nb (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : NonBlank := ⟨s, h⟩

private def ne (s : String) : NonEmptyArray String := ⟨#[s], by simp⟩

open Kb

-- A human requirement, provenance = author ref, boxed at `proved`.
private def specItem : Boxed HumanReq String :=
  { assurance := .proved
    item := { payload := { reqId := "page.overview", shall := "show dashboard" }
              provenance := ne "author:alice; why:launch" } }

-- An agent reflection, provenance = run ids, boxed at `provisional`.
private def wikiItem : Boxed AgentReflection String :=
  { assurance := .provisional
    item := { payload := { refId := "wiki.enum-canary", learning := "guards catch typos" }
              provenance := ⟨#["run-001", "run-002"], by native_decide⟩ } }

-- Both stores are `Store P S` at different (P, S). Uniqueness proved by the generic instance.
private def specStore : Store HumanReq String := { items := #[specItem], uniqueIds := by native_decide }
private def wikiStore : Store AgentReflection String := { items := #[wikiItem], uniqueIds := by native_decide }

-- Store membership works uniformly on both axes.
#guard specStore.hasId "page.overview"
#guard wikiStore.hasId "wiki.enum-canary"
#guard !wikiStore.hasId "wiki.ghost"

-- Anti-laundering, concretely: merging a `provisional` agent item with a `proved`
-- one yields `provisional` (the meet), never `proved`.
private def launderAttempt : Boxed AgentReflection String :=
  let other : Boxed AgentReflection String :=
    { assurance := .proved
      item := { payload := { refId := "wiki.enum-canary", learning := "guards catch typos" }
                provenance := ⟨#["run-003"], by native_decide⟩ } }
  merge { refId := "wiki.enum-canary", learning := "guards catch typos" } wikiItem other rfl

#guard launderAttempt.assurance == Assurance.provisional          -- meet, not join
#guard launderAttempt.item.provenance.items == #["run-001", "run-002", "run-003"]  -- provenance grew

-- Store.record: the generic consolidation write-path both axes need. A genuinely
-- new item (fresh id, no `sameAs` match) is appended; an item matching an existing
-- entry consolidates in place, unioning provenance — one op, `uniqueIds` preserved
-- by construction (proved, not hoped).
private def newRefl : Item .provisional AgentReflection String :=
  { payload := { refId := "wiki.read-first", learning := "read before proposing" }
    provenance := ne "run-009" }
private def moreRuns : Item .provisional AgentReflection String :=
  { payload := { refId := "wiki.enum-canary", learning := "guards catch typos" }
    provenance := ⟨#["run-003"], by native_decide⟩ }

-- New id → appended (store grows to two entries).
#guard (wikiStore.record (fun b => b.id == "wiki.read-first") .provisional newRefl).items.size == 2
-- Matching id → consolidated in place (still one entry) with provenance unioned.
#guard
  let w := wikiStore.record (fun b => b.id == "wiki.enum-canary") .provisional moreRuns
  w.items.size == 1 &&
    match w.items[0]? with
    | some b => b.item.provenance.items == #["run-001", "run-002", "run-003"]
    | none => false

-- Coherence / valve: a spec item may cite the reflection; the citation resolves
-- against the wiki store, and refuses a source the wiki lacks — without changing
-- either item's assurance.
private def resolveAgainstWiki (s : String) : Bool := wikiStore.hasId s
#guard coherentVia resolveAgainstWiki #["wiki.enum-canary"]        -- coherent
#guard !coherentVia resolveAgainstWiki #["wiki.ghost"]             -- fabricated → refused

-- Redaction at the boundary: a sensitive field is clamped on admit; a clean one
-- passes through. Privacy holds uniformly on both payload types.
private def secretRefl : Item .provisional AgentReflection String :=
  { payload := { refId := "wiki.leak", learning := "note SECRET: patient SSN 123-45-6789" }
    provenance := ⟨#["run-050"], by native_decide⟩ }
#guard (admit secretRefl).item.payload.learning == "[REDACTED]"     -- scrubbed on entry
#guard (admit wikiItem.item).item.payload.learning == "guards catch typos"  -- clean passes

-- Promotion is the only assurance-raising door, and the obligation type says what
-- each raise costs. An agent reflection climbs provisional → coherent → proved.
private def theGate : Gate := { approver := nb "alice", contentHash := nb "sha256:abcd" }

-- Step 1: provisional → coherent requires a discharged coherence proof.
private def coherentStep : Boxed AgentReflection String :=
  promote wikiItem.item (.toCoherent (coherentVia resolveAgainstWiki #["wiki.enum-canary"]) (by native_decide))
#guard coherentStep.assurance == Assurance.coherent

-- Step 2: coherent → proved requires the attributed human gate. Rebuild the item
-- at `.coherent` and promote it the last rung.
private def coherentItem : Item .coherent AgentReflection String :=
  { payload := wikiItem.item.payload, provenance := wikiItem.item.provenance }
private def provedStep : Boxed AgentReflection String :=
  promote coherentItem (.toProved theGate)
#guard provedStep.assurance == Assurance.proved

-- The illegal shortcut provisional → proved does not typecheck: there is no
-- `Obligation .provisional .proved` constructor. (Statically enforced;
-- `no_direct_provisional_to_proved` is the theorem. Uncommenting the next line is
-- a compile error, which is the guarantee.)
-- #guard (promote wikiItem.item (.toProved theGate)).assurance == Assurance.proved

/-! ### Defeasible relations: the SAME layer serves both axes

The wiki axis: a later `strategy` supersedes an earlier `pattern`, present = "id is
in the wiki." The determination axis: one decision supersedes another, present =
"id is in the set AND still active." Same `defeated`/`effectiveIds`, different
`present`. -/

private def rels : List Relation :=
  [{ kind := .supersedes, source := "later", target := "earlier" }]

-- WIKI-STYLE present (merely present): source "later" exists → "earlier" defeated.
private def wikiPresent (id : String) : Bool := ["later", "earlier"].contains id
#guard defeated wikiPresent rels "earlier"                       -- defeated
#guard (effectiveIds wikiPresent rels ["later", "earlier"]) == ["later"]  -- earlier drops out

-- DETERMINATION-STYLE present (present AND active): "later" is present but retracted
-- (inactive) → it does NOT defeat "earlier". Defeasibility, from the same function.
private def activeIds : List String := ["earlier"]                -- "later" retracted
private def detPresent (id : String) : Bool := activeIds.contains id
#guard !defeated detPresent rels "earlier"                        -- retracted source: no defeat
#guard (effectiveIds detPresent rels ["earlier"]) == ["earlier"]  -- earlier stands

-- precedentFor informs but never defeats, on either axis.
#guard !defeated wikiPresent
  [{ kind := .precedentFor, source := "later", target := "earlier" }] "earlier"

end LeanSpec.Kb
