module

public import LeanSpec.Kb
public import LeanSpec.Reflection
public import LeanSpec.Wiki
public meta import LeanSpec.Kb
public meta import LeanSpec.Reflection
public meta import LeanSpec.Wiki
public meta import LeanUtil

/-!
# Adapter: `Wiki` as an instance of the generic `Kb.Store` (correspondence, not rewrite)

This module does **not** touch `Wiki`, `Reflection`, or their frozen proof suites.
It proves that the existing agent-axis operations *agree with* the generic core in
`Kb.lean`, so the unification is established as a theorem before any code is
deleted or migrated. If these correspondences hold, the in-place migration later is
mechanical and its risk is bounded.

Mapping:

* payload `P := Reflection`, provenance source `S := NonBlank` (a run id).
* `Item .provisional Reflection NonBlank` — every wiki entry rests at
  `.provisional` (never proved true, only provenance-honest — the WikiSkill
  invariant).
* `Identified Reflection` via `r.id.value`.
* `Redactable Reflection` — a no-op for now. `Reflection` has *no PII model yet*
  (turn-1 gap). This instance is the honest placeholder that says so: it satisfies
  the idempotence law trivially, and it is the single spot a real scrubber drops in
  later. Wiring it here means the migration inherits redaction the moment the
  instance gains teeth.

What is proved:

1. `coherentIn_eq_coherentVia` — the agent-axis coherence check *is* the generic
   `coherentVia`. The four per-axis `coherentIn`/`coherentInWiki` variants collapse
   to one.
2. `superseded_eq_defeated` — `Wiki.superseded` *is* the generic `defeated` under
   the wiki-style `present` predicate (source merely present). The two duplicated
   defeasible-resolution algorithms are one.
-/

namespace LeanSpec.KbAdapter

open LeanSpec
open LeanSpec.Kb

public section

/-! ## Instances placing `Reflection` into the generic core

(`Kb.Identified Reflection` now lives in `Wiki`, since `Wiki` wraps a `Kb.Store`.)

## Redaction with teeth

The no-op placeholder is replaced by a real scrubber on the one free-text field a
reflection carries: `learning`. That is the leak surface — agent-authored prose
that can contain secrets or PII (the turn-1 privacy gap). `id`/`kind`/`derivedFrom`
(run ids)/`promoted` are structural and pass through.

The scrubber is **clamp-to-fixpoint**: if `learning` trips the sensitivity detector
(`containsSecret`, a stand-in for a real PII classifier), it is replaced wholesale
by a fixed `[REDACTED]` placeholder. This shape is the realistic model for
regulated redaction (replace, don't surgically edit) and it makes idempotence
provable: the placeholder is itself not sensitive, so a second pass is the
identity, and a clean learning is never touched. Crucially the placeholder is
non-blank, so redaction *preserves the `NonBlank` payload invariant* — a scrubbed
reflection is still a well-formed reflection. -/

/-- Sensitivity detector (stand-in for a real PII/secret classifier). -/
public def containsSecret (s : String) : Bool := (s.splitOn "SECRET:").length != 1

/-- The redaction placeholder, proven non-blank so it can inhabit a `NonBlank`. -/
public def redactedLearning : NonBlank := ⟨"[REDACTED]", by native_decide⟩

/-- The placeholder is not itself sensitive — the fixpoint that makes redaction
idempotent. -/
public theorem redactedLearning_clean : containsSecret redactedLearning.value = false := by
  native_decide

/-- Scrub a single learning: clamp to the placeholder when sensitive, else keep. -/
public def scrubLearning (n : NonBlank) : NonBlank :=
  if containsSecret n.value then redactedLearning else n

/-- Scrubbing a learning is idempotent. -/
public theorem scrubLearning_idem (n : NonBlank) :
    scrubLearning (scrubLearning n) = scrubLearning n := by
  unfold scrubLearning
  split
  · -- sensitive → inner is the placeholder, which is clean, so the inner `if` is `else`
    rw [if_neg (by rw [redactedLearning_clean]; decide)]
  · -- already clean → inner sees the same clean string
    rfl

/-- **Redaction with teeth.** Scrub the `learning`; everything structural passes
through. Because `scrubLearning` returns a `NonBlank`, the payload invariant
survives — a redacted reflection is still well-formed. -/
public instance : Kb.Redactable Reflection where
  redact r := { r with learning := scrubLearning r.learning }
  redact_idempotent r := by
    simp only [scrubLearning_idem]

/-- Lift a `Reflection` into a provisional `Item`. Its `derivedFrom` run ids become
the item's provenance verbatim. -/
@[expose] public def reflToItem (r : Reflection) : Kb.Item .provisional Reflection RunId :=
  { payload := r, provenance := r.derivedFrom }

/-- The lifted item's id is the reflection's id — `Identified` agrees with the
domain notion of identity. -/
public theorem reflToItem_id (r : Reflection) : (reflToItem r).id = r.id.value := by
  simp only [reflToItem, Kb.Item.id, Kb.Identified.idOf]

/-- The lifted item's provenance is exactly the reflection's `derivedFrom`. -/
public theorem reflToItem_provenance (r : Reflection) :
    (reflToItem r).provenance = r.derivedFrom := by
  simp only [reflToItem]

/-! ## 1. Coherence: the agent-axis check IS the generic one

`Reflection.coherentIn known` walks `derivedFrom` and checks each run id is in
`known`. The generic `coherentVia resolve srcs` does the same with
`resolve := fun s => known.contains s.value`. We prove they are equal for every
reflection, so `coherentVia_rejects_unknown` (proved once, generically) subsumes
`Reflection.coherentIn_rejects_unknown`. -/

/-- The generic-side resolver for a set of known run ids. -/
public def knownResolver (known : Array String) : RunId → Bool :=
  fun s => known.contains s.value

/-- `allKnown` (the hand-rolled recursive predicate) equals `List.all` under the
generic resolver, by induction on the list. -/
public theorem allKnown_eq_listAll (known : Array String) :
    ∀ xs : List RunId,
      allKnown known xs = xs.all (knownResolver known) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons y rest ih =>
    simp only [allKnown, List.all_cons, knownResolver]
    rw [ih]

/-- **The agent-axis coherence check is the generic `coherentVia`.** Every
`Reflection.coherentIn` is a `coherentVia` on its provenance. -/
public theorem coherentIn_eq_coherentVia (known : Array String) (r : Reflection) :
    r.coherentIn known
      = Kb.coherentVia (knownResolver known) r.derivedFrom.items := by
  simp only [Reflection.coherentIn, Kb.coherentVia]
  rw [allKnown_eq_listAll known r.derivedFrom.items.toList]
  rw [List.all_toArray]

/-- Corollary: the generic refusal theorem, specialised back to reflections. A
reflection citing an unknown run is incoherent — but now it is a *consequence* of
the generic `coherentVia_rejects_unknown`, not a separately-maintained proof. -/
public theorem reflection_rejects_unknown
    {known : Array String} {r : Reflection} {x : RunId}
    (hx : x ∈ r.derivedFrom.items) (hbad : known.contains x.value = false) :
    r.coherentIn known = false := by
  rw [coherentIn_eq_coherentVia]
  exact Kb.coherentVia_rejects_unknown (resolve := knownResolver known) hx hbad

/-! ## 2. Defeasible resolution: `Wiki.superseded` IS the generic `defeated`

Since the migration (task #2), `Wiki.superseded` is *defined* as
`Kb.defeated w.present (ms.map Wiki.morphismToRelation) r.id.value` — the wiki no
longer carries its own defeat algorithm; it delegates to the core. The mapping
(`Wiki.morphismToRelation`, `Wiki.morphismDefeats_eq`, `Wiki.present`) now lives in
`Wiki` alongside the delegation. So the correspondence that once needed a proof is
definitional. -/

open LeanSpec.TypeSystems (Morphism MorphismKind)

/-- **`Wiki.superseded` is the generic `defeated`.** Now definitional: `superseded`
delegates to `Kb.defeated` under the mapped relations and wiki-presence. The
duplicated defeasible-resolution algorithm is one algorithm, in the core. -/
public theorem superseded_eq_defeated (w : Wiki) (ms : List Morphism) (r : Reflection) :
    w.superseded ms r
      = Kb.defeated w.present (ms.map LeanSpec.morphismToRelation) r.id.value := rfl

/-! ## 3. Consolidation: `Reflection.merge`'s provenance union IS the generic one

`Wiki.dedupUnion` (on `Array NonBlank`) dedups by `x.value`; `Kb.dedupUnion`
(generic, `[BEq S]`) dedups by `!a.contains x`. For `S = NonBlank` these are the
*same set* — `NonBlank`'s `BEq` compares by `.value` and is lawful — but not
definitionally equal. Proving they coincide is exactly the friction a real
migration hits: the generic core is correct, but the domain used a bespoke
value-projection where the generic one uses `BEq`. Once bridged, `Reflection.merge`
is `Kb.merge` on the provisional axis (where the assurance meet is degenerate,
always `.provisional`, so the anti-laundering law holds trivially and the whole
content of the merge is the provenance union). -/

/-- Since the migration (task #2), `LeanSpec.dedupUnion` *is* `Kb.dedupUnion` — the
wiki no longer carries a parallel implementation. The correspondence that once
needed a pointwise `contains` bridge is now definitional. -/
public theorem dedupUnion_eq (a b : Array RunId) :
    Kb.dedupUnion a b = LeanSpec.dedupUnion a b := rfl

/-- **`Reflection.merge` is `Kb.merge` on the provisional axis.** When two
reflections consolidate (`some m`), the merged item — lifted through `reflToItem` — has
exactly the payload and provenance the generic `Kb.merge` produces, boxed at
`.provisional` (the degenerate meet). Provenance union, id/kind/learning retention,
and the assurance floor all line up. -/
public theorem merge_eq_kbMerge
    {a b m : Reflection} (h : Reflection.merge a b = some m) :
    (reflToItem m).provenance
      = (Kb.merge m (⟨.provisional, reflToItem a⟩ : Kb.Boxed Reflection RunId)
          ⟨.provisional, reflToItem b⟩
          (show Kb.Identified.idOf m = (reflToItem a).id by
            -- `Reflection.merge` keeps `a`'s id, so `m.id = a.id`.
            simp only [Reflection.merge] at h
            split at h
            · injection h with h; subst h; rfl
            · contradiction)).item.provenance := by
  simp only [Reflection.merge] at h
  split at h
  · injection h with h
    subst h
    -- LHS provenance is the wiki dedupUnion; RHS is the generic one. Bridge them
    -- via NonEmptyArray.ext (proof fields are irrelevant) and dedupUnion_eq.
    simp only [reflToItem, Kb.merge]
    apply NonEmptyArray.ext
    exact (dedupUnion_eq a.derivedFrom.items b.derivedFrom.items).symm
  · contradiction

/-- The merged item still rests at `.provisional`: consolidation on the agent axis
never raises assurance (the anti-laundering law, specialised — the meet of
`.provisional` with itself is `.provisional`). -/
public theorem merge_stays_provisional (a b : Reflection) :
    (Kb.merge a (⟨.provisional, reflToItem a⟩ : Kb.Boxed Reflection RunId)
        ⟨.provisional, reflToItem b⟩ (show Kb.Identified.idOf a = (reflToItem a).id from rfl)).assurance
      = .provisional := by
  simp only [Kb.merge, Kb.Assurance.meet, Kb.Assurance.rank, Nat.le_refl, if_true]

/-! ## Worked examples: redaction actually scrubs, and the generic boundary inherits it -/

private def leakyRefl : Reflection :=
  { id := ⟨"wiki.leak", by native_decide⟩
    kind := .failureMode
    learning := ⟨"agent logged SECRET: patient SSN 123-45-6789", by native_decide⟩
    derivedFrom := ⟨#[⟨"run-050", by native_decide⟩], by native_decide⟩ }

private def cleanRefl : Reflection :=
  { id := ⟨"wiki.ok", by native_decide⟩
    kind := .pattern
    learning := ⟨"round-trip guards catch enum typos", by native_decide⟩
    derivedFrom := ⟨#[⟨"run-001", by native_decide⟩], by native_decide⟩ }

-- A leaky learning is clamped to the placeholder on redaction.
#guard (Kb.Redactable.redact leakyRefl).learning.value == "[REDACTED]"
-- A clean learning is untouched.
#guard (Kb.Redactable.redact cleanRefl).learning.value == "round-trip guards catch enum typos"
-- Structural fields survive redaction (id/kind/provenance unchanged).
#guard (Kb.Redactable.redact leakyRefl).id.value == "wiki.leak"
#guard (Kb.Redactable.redact leakyRefl).derivedFrom.items.map (·.value) == #["run-050"]
-- The generic store boundary (`admit`) inherits redaction: nothing crosses un-scrubbed.
#guard (Kb.admit (reflToItem leakyRefl)).item.payload.learning.value == "[REDACTED]"
-- Idempotence, witnessed on a concrete leaky value.
#guard (Kb.Redactable.redact (Kb.Redactable.redact leakyRefl)).learning.value
  == (Kb.Redactable.redact leakyRefl).learning.value

end

end LeanSpec.KbAdapter
