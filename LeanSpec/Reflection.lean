module

public import LeanSpec.Trace
public import LeanSpec.Classification
public import LeanSpec.Validated
public import LeanSpec.Codec.Applicative
public meta import LeanSpec.Trace
public meta import LeanSpec.Classification
public meta import LeanSpec.Codec.Applicative
public meta import LeanUtil

/-!
# Reflection: consolidated agent-experience knowledge (the WikiSkill "wiki" node)

This is the **agent axis**, deliberately kept apart from the human-authored spec
store (Requirement / Design / Determination).

A `Reflection` is *provisional* agent knowledge — a recurring pattern, a failure
mode, or a strategy — consolidated from **one or more** runs (`derivedFrom`), not
a single one-shot note. `promoted : PromotionTarget` is the one-way valve into the
human-authority layer, where — and only where — the human proof gate applies.

The invariant that keeps the axes separate: the checker proves a reflection is
*well-formed* (blank learning, empty provenance are impossible) and
*provenance-coherent* (`coherentIn` — every cited run actually exists). It can
**never** prove the learning is true or useful. The agent store is therefore
lower-assurance than the spec store by construction.

Follows the house pattern (`Raw` twin, total `validate`, `validate_sound` /
`validate_complete`), modelled on `Precedent.lean`. `coherentIn` is the
"Wiki Maintainer" provenance check — the `Precedent.coherentIn` analogue on the
agent axis, evaluated against the set of known run ids.
-/

namespace LeanSpec

open LeanSpec.Codec

public section

/-- What kind of agent knowledge a reflection captures. Closed vocabulary: a typo
cannot inhabit this type. Distinct from `PromotionTarget`, which says where the
learning goes, not what it is. -/
public inductive ReflectionKind where
  | pattern      -- a reusable regularity ("round-trip #guards catch enum typos")
  | failureMode  -- a way runs go wrong ("agents forget the NonEmptyArray obligation")
  | strategy     -- a way to succeed ("read the snapshot before proposing a delta")
  deriving Repr, BEq, DecidableEq

/-- A reflection identifier: the stable handle relations and gates address a
reflection by. A newtype over non-blank text, distinct at the type level from
`RunId` (a reflection's provenance) and `RequirementId` (the human axis) — so a
morphism endpoint or a citation cannot silently mix id kinds. `.value`/`.property`
mirror `NonBlank`. -/
public structure ReflectionId where
  value : String
  property : LeanUtil.nonemptyText value = true
  deriving Repr

public instance : BEq ReflectionId where
  beq l r := l.value == r.value

namespace ReflectionId

public theorem ext {l r : ReflectionId} (h : l.value = r.value) : l = r := by
  cases l with
  | mk lv lp => cases r with | mk rv rp => cases h; rfl

public instance : LawfulBEq ReflectionId where
  rfl {a} := BEq.refl a.value
  eq_of_beq h := ext (eq_of_beq h)

public instance : DecidableEq ReflectionId := instDecidableEqOfLawfulBEq

public def parse (path value : String) : Except ValidationError ReflectionId :=
  if h : LeanUtil.nonemptyText value = true then .ok ⟨value, h⟩
  else .error { path, issue := .blank, rejected := some value }

public theorem parse_sound {path value : String} {result : ReflectionId}
    (h : parse path value = .ok result) :
    result.value = value ∧ LeanUtil.nonemptyText value = true := by
  unfold parse at h; split at h
  · cases h; exact ⟨rfl, ‹LeanUtil.nonemptyText value = true›⟩
  · contradiction

public theorem parse_complete {path : String} (result : ReflectionId) :
    parse path result.value = .ok result := by
  unfold parse; split
  · next h => exact congrArg Except.ok (ReflectionId.ext rfl)
  · next h => exact absurd result.property h

end ReflectionId

/-- Consolidated agent-experience knowledge. `derivedFrom` holds the run ids this
learning was distilled from — at least one, by construction. -/
public structure Reflection where
  id             : ReflectionId          -- stable handle, so relations/gates can address it
  kind           : ReflectionKind
  learning       : NonBlank              -- what was learned (one sentence)
  derivedFrom    : NonEmptyArray RunId   -- runIds of the AgentTraces consolidated
  promoted       : PromotionTarget := .noAction
  classification : Classification := Classification.bottom  -- sensitivity; join-preserved by merge
  deriving Repr

/-- Equality ignores proof terms; two reflections compare by payload. -/
public instance : BEq Reflection where
  beq l r :=
    l.id == r.id && l.kind == r.kind && l.learning == r.learning &&
      l.derivedFrom == r.derivedFrom && l.promoted == r.promoted &&
      l.classification == r.classification

/-! ## Provenance coherence — the Wiki Maintainer check

A reflection is coherent against a set of known run ids when every run it claims
to be derived from actually exists. A reflection citing a run that never happened
is refused — the agent-axis analogue of `Supersedes.coherentIn`. Written as a
self-contained recursive predicate so the guarantees are proved by induction,
without leaning on stdlib `Array.all` lemmas. -/

/-- Every element of `xs` is a known run id. -/
@[expose] public def allKnown (known : Array String) : List RunId → Bool
  | [] => true
  | x :: rest => known.contains x.value && allKnown known rest

/-- A recorded reflection is coherent when all of its `derivedFrom` runs are known. -/
@[expose] public def Reflection.coherentIn (known : Array String) (r : Reflection) : Bool :=
  allKnown known r.derivedFrom.items.toList

/-- Coherence transfers to every cited run: a coherent reflection cites only runs
that exist. -/
public theorem allKnown_mem {known : Array String} :
    ∀ {xs : List RunId} {x : RunId},
      allKnown known xs = true → x ∈ xs → known.contains x.value = true := by
  intro xs
  induction xs with
  | nil => intro x _ hmem; cases hmem
  | cons y rest ih =>
    intro x h hmem
    simp only [allKnown] at h
    have hy : known.contains y.value = true := by
      cases hc : known.contains y.value with
      | true => rfl
      | false => rw [hc] at h; simp at h
    have hrest : allKnown known rest = true := by
      cases hc : allKnown known rest with
      | true => rfl
      | false => rw [hc, Bool.and_false] at h; exact absurd h (by simp)
    rcases List.mem_cons.mp hmem with h' | h'
    · subst h'; exact hy
    · exact ih hrest h'

/-- The refusal guarantee: a reflection citing an unknown run cannot be coherent.
This is what stops the Wiki from accumulating learnings with fabricated provenance. -/
public theorem Reflection.coherentIn_rejects_unknown
    {known : Array String} {r : Reflection} {x : RunId}
    (hmem : x ∈ r.derivedFrom.items.toList) (hunk : known.contains x.value = false) :
    r.coherentIn known = false := by
  simp only [Reflection.coherentIn]
  cases hc : allKnown known r.derivedFrom.items.toList with
  | false => rfl
  | true => have := allKnown_mem hc hmem; rw [hunk] at this; exact absurd this (by simp)

/-! ## Wire form: `Reflection` as an untrusted DTO -/

namespace Raw

/-- Untrusted wire representation. `kind` and `promoted` are closed enums (a typo
cannot inhabit them), so they pass through; `learning` and `derivedFrom` are
untrusted text validated on the way in. -/
public structure Reflection where
  id             : String
  kind           : ReflectionKind
  learning       : String
  derivedFrom    : Array String := #[]
  promoted       : PromotionTarget := .noAction
  classification : Classification := Classification.bottom
  deriving Repr, BEq

end Raw

/-- Projection to the untrusted wire representation. -/
public def Reflection.toRaw (r : Reflection) : Raw.Reflection :=
  { id := r.id.value
    kind := r.kind
    learning := r.learning.value
    derivedFrom := r.derivedFrom.items.map (·.value)
    promoted := r.promoted
    classification := r.classification }

/-- `ReflectionId` / `RunId` as atomic codecs (same shape as `nonBlank`). -/
@[expose] public def reflIdCodec : Codec String ReflectionId where
  decode p s := ReflectionId.parse p s
  encode i := i.value
  sound h := (ReflectionId.parse_sound h).1
  complete i := ReflectionId.parse_complete i

@[expose] public def runIdCodec : Codec String RunId where
  decode p s := RunId.parse p s
  encode i := i.value
  sound h := (RunId.parse_sound h).1
  complete i := RunId.parse_complete i

namespace Raw.Reflection

/-- The `Reflection` codec, composed from the generic algebra: a product of the
field codecs (`reflIdCodec`, `passthrough` for the closed enums `kind`/`promoted`,
`nonBlank`, and `nonEmpty runIdCodec` for `derivedFrom`), turned into the domain
record (`imap`) and read from `Raw.Reflection` (`comap`). `encode` is definitionally
`toRaw`, so the round-trips delegate directly — replacing the bespoke `parseRunRefs`
helpers and the nested `split` chain. -/
public def codec : Codec Raw.Reflection LeanSpec.Reflection :=
  comap
    (imap
      (prod (label "id" reflIdCodec) (prod passthrough (prod (label "learning" nonBlank)
        (prod (label "derivedFrom" (nonEmpty runIdCodec)) (prod passthrough passthrough)))))
      (fun t => ({ id := t.1, kind := t.2.1, learning := t.2.2.1,
                   derivedFrom := t.2.2.2.1, promoted := t.2.2.2.2.1,
                   classification := t.2.2.2.2.2 } : LeanSpec.Reflection))
      (fun r => (r.id, r.kind, r.learning, r.derivedFrom, r.promoted, r.classification))
      (fun _ => rfl) (fun _ => rfl))
    (fun raw => (raw.id, raw.kind, raw.learning, raw.derivedFrom, raw.promoted, raw.classification))
    (fun t => ({ id := t.1, kind := t.2.1, learning := t.2.2.1,
                 derivedFrom := t.2.2.2.1, promoted := t.2.2.2.2.1,
                 classification := t.2.2.2.2.2 } : Raw.Reflection))
    (fun _ => rfl) (fun _ => rfl)

/-- Total validation from the untrusted wire DTO into the fail-closed domain type. -/
public def validate (path : String) (raw : Raw.Reflection) :
    Except ValidationError LeanSpec.Reflection :=
  codec.decode path raw

/-- Successful validation projects back to the raw reflection. -/
public theorem validate_sound
    {path : String} {raw : Raw.Reflection} {r : LeanSpec.Reflection}
    (h : validate path raw = .ok r) : r.toRaw = raw := by
  have henc : codec.encode r = r.toRaw := rfl
  rw [← henc]; exact codec.sound h

/-- A domain reflection validates back to itself. -/
public theorem validate_complete (r : LeanSpec.Reflection) (path : String) :
    validate path r.toRaw = .ok r := by
  have henc : codec.encode r = r.toRaw := rfl
  show codec.decode path r.toRaw = .ok r
  rw [← henc]; exact codec.complete r

end Raw.Reflection

end

/-! ## Worked examples (executable `#guard`s) -/

private def nb (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : NonBlank := ⟨s, h⟩

private def rid (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : ReflectionId := ⟨s, h⟩

private def runid (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : RunId := ⟨s, h⟩

-- A learning consolidated from *two* runs — the WikiSkill move a one-shot
-- `traceRef` could not express.
private def consolidated : Reflection :=
  { id := rid "wiki.nonemptyarray-obligation"
    kind := .failureMode
    learning := nb "Agents forget the NonEmptyArray obligation on scenario lists"
    derivedFrom := ⟨#[runid "run-001", runid "run-007"], by decide⟩
    promoted := .skill }

-- Coherent when both source runs are known.
#guard consolidated.coherentIn #["run-001", "run-007", "run-042"]

-- Refused when a cited run does not exist (fabricated provenance).
#guard !consolidated.coherentIn #["run-001"]

-- `kind` is a real axis, separate from `promoted`.
#guard ReflectionKind.pattern != ReflectionKind.failureMode
#guard consolidated.kind == ReflectionKind.failureMode

-- Wire round-trip: a domain reflection validates back to itself (validate_complete,
-- worked on a concrete value).
#guard match Raw.Reflection.validate "ex" consolidated.toRaw with
  | .ok r => r == consolidated
  | .error _ => false

-- Fail-closed on the wire: blank learning is rejected.
#guard match Raw.Reflection.validate "ex"
    { id := "r1", kind := .pattern, learning := "  ", derivedFrom := #["run-001"] } with
  | .error e => e.issue == .blank
  | .ok _ => false

-- Fail-closed on the wire: empty provenance is rejected (a learning must come
-- from at least one run).
#guard match Raw.Reflection.validate "ex"
    { id := "r1", kind := .pattern, learning := "something", derivedFrom := #[] } with
  | .error e => e.issue == .emptyArray
  | .ok _ => false

-- Classification defaults to the lattice bottom when absent on the wire (fixture
-- compatibility: old wire fixtures decode unchanged, like `promoted` → `.noAction`).
#guard match Raw.Reflection.validate "ex"
    { id := "r1", kind := .pattern, learning := "x", derivedFrom := #["run-001"] } with
  | .ok r => r.classification == Classification.bottom
  | .error _ => false

-- An explicit classification round-trips.
private def sensitiveRefl : Reflection :=
  { consolidated with classification := .sensitive }
#guard match Raw.Reflection.validate "ex" sensitiveRefl.toRaw with
  | .ok r => r == sensitiveRefl && r.classification == Classification.sensitive
  | .error _ => false

end LeanSpec
