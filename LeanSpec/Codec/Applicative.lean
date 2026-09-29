module

public import LeanSpec.Validated
public meta import LeanSpec.Validated

/-!
# A codec algebra: `Codec R D` with round-trips proved once

The record validators (`Raw.Foo.validate` / `validate_sound` / `validate_complete`,
repeated ~11×) are all the same shape: decode each field, reassemble, and prove the
two round-trips by an identical nested `split`/`contradiction` chain. This module
factors that shape into a **bidirectional codec bundle** and two combinators —
`prod` (pair two codecs) and `imap` (retype the domain side through an isomorphism)
— whose `sound`/`complete` are proved **once**. A record validator then *composes*
from atomic field codecs instead of re-proving the chain: `prod`s build a nested
tuple, one `imap` turns the tuple into the domain record.

`Codec R D` bundles the decoder, the encoder (the `toRaw` projection), and the two
laws as fields, so a value of this type *is* a proof-carrying round-trip. The
guarantees rest on the kernel (`propext` only): no `native_decide`.

This is the leaf algebra; migrating the existing validators onto it is mechanical
(each needs the trivial `RawRec ≅ R₁×…×Rₙ` / `DomRec ≅ D₁×…×Dₙ` isos, plus a
`guard` step for the few records with a cross-field constraint like `Supersedes`'s
`source ≠ target`).
-/

namespace LeanSpec.Codec

open LeanSpec

public section

/-- A bidirectional, proof-carrying codec between an untrusted wire type `R` and a
fail-closed domain type `D`. `decode` is total (returns a `ValidationError` on bad
input); `encode` is the `toRaw` projection; `sound`/`complete` are the round-trips. -/
public structure Codec (R D : Type) where
  decode   : String → R → Except ValidationError D
  encode   : D → R
  /-- A successful decode projects back to exactly the raw input. -/
  sound    : ∀ {p : String} {r : R} {d : D}, decode p r = .ok d → encode d = r
  /-- A domain value decodes from its own projection. -/
  complete : ∀ {p : String} (d : D), decode p (encode d) = .ok d

/-! ## Atomic codec: a validated string newtype -/

/-- `NonBlank` as a codec: parse a string, project `.value`. The single atomic leaf
the string-newtypes share (others follow the same three-line shape). -/
@[expose] public def nonBlank : Codec String NonBlank where
  decode p s := NonBlank.parse p s
  encode n := n.value
  sound h := (NonBlank.parse_sound h).1
  complete n := NonBlank.parse_complete n

/-- `RequirementId` as a codec — same three-line shape as `nonBlank`. -/
@[expose] public def reqId : Codec String RequirementId where
  decode p s := RequirementId.parse p s
  encode i := i.value
  sound h := (RequirementId.parse_sound h).1
  complete i := RequirementId.parse_complete i

/-- `ProcessSkillId` as a codec — same three-line shape as `nonBlank`. -/
@[expose] public def procId : Codec String ProcessSkillId where
  decode p s := ProcessSkillId.parse p s
  encode i := i.value
  sound h := (ProcessSkillId.parse_sound h).1
  complete i := ProcessSkillId.parse_complete i

/-- A passthrough codec for a field that is the *same* type on the wire and in the
domain (a closed enum copied verbatim, e.g. `kind`, `check`, `promoted`). -/
@[expose] public def passthrough {A : Type} : Codec A A where
  decode _ a := .ok a
  encode a := a
  sound h := by injection h with h'; exact h'.symm
  complete _ := rfl

/-- Prefix a field name onto the path a codec sees, so error messages read
`record.field` (and `record.field[i]` for lists) exactly as the hand-written
validators did. Wrap each field codec in `prod` with its name. Only the path
changes; the round-trips are inherited unchanged. -/
@[expose] public def label {R D : Type} (name : String) (c : Codec R D) : Codec R D where
  decode p r := c.decode s!"{p}.{name}" r
  encode := c.encode
  sound h := c.sound h
  complete d := c.complete d

/-! ## `prod`: pair two codecs, round-trip proved once -/

/-- Pair two codecs into a codec on the product. This is the field-sequencing step:
`decode` runs both (fail-closed, left to right), `encode` pairs the projections. -/
@[expose] public def prod {R₁ D₁ R₂ D₂ : Type} (c₁ : Codec R₁ D₁) (c₂ : Codec R₂ D₂) :
    Codec (R₁ × R₂) (D₁ × D₂) where
  decode p r :=
    match c₁.decode p r.1 with
    | .error e => .error e
    | .ok d₁ =>
      match c₂.decode p r.2 with
      | .error e => .error e
      | .ok d₂ => .ok (d₁, d₂)
  encode d := (c₁.encode d.1, c₂.encode d.2)
  sound h := by
    split at h
    · contradiction
    · next d₁ h₁ =>
      split at h
      · contradiction
      · next d₂ h₂ =>
        cases h
        rw [c₁.sound h₁, c₂.sound h₂]
  complete d := by
    simp only [c₁.complete, c₂.complete]

/-! ## `imap`: retype the domain side through an isomorphism -/

/-- Transport a codec along a domain-side isomorphism `D ≃ D'` (invariant functor).
Used to turn a nested-product codec into a codec for the actual domain record via the
record's `mk`/projection iso. -/
@[expose] public def imap {R D D' : Type} (c : Codec R D)
    (fwd : D → D') (bwd : D' → D)
    (right : ∀ x, fwd (bwd x) = x) (left : ∀ x, bwd (fwd x) = x) :
    Codec R D' where
  decode p r :=
    match c.decode p r with
    | .ok d => .ok (fwd d)
    | .error e => .error e
  encode d' := c.encode (bwd d')
  sound h := by
    split at h
    · next d0 hx =>
      injection h with h'
      subst h'
      rw [left d0]
      exact c.sound hx
    · next e hx => exact absurd h (by simp)
  complete d' := by
    show (match c.decode _ (c.encode (bwd d')) with
          | .ok d => .ok (fwd d) | .error e => .error e) = Except.ok d'
    rw [c.complete (bwd d')]
    exact congrArg Except.ok (right d')

end

/-! ## `comap`: transport along a raw-side isomorphism

The dual of `imap`: retype the *wire* side through `R ≃ R'`, so a record migration
reads its actual `Raw.Foo` (rather than a hand-written product adapter). -/
@[expose] public def comap {R R' D : Type} (c : Codec R D)
    (fwd : R' → R) (bwd : R → R')
    (left : ∀ r', bwd (fwd r') = r') (right : ∀ r, fwd (bwd r) = r) :
    Codec R' D where
  decode p r' := c.decode p (fwd r')
  encode d := bwd (c.encode d)
  sound h := by rw [c.sound h, left]
  complete d := by
    show c.decode _ (fwd (bwd (c.encode d))) = Except.ok d
    rw [right]; exact c.complete d

/-! ## `refine`: a decidable cross-field constraint (proof-carrying)

The few records whose domain type carries a *relational* proof field (e.g.
`Supersedes`'s `source ≠ target`) need one guarded step `prod` cannot express:
decode the unconstrained tuple, check a decidable predicate, and build the refined
value with its proof — or fail closed. `mk`/`un` are the refine/forget iso. -/
@[expose] public def refine {R D D' : Type} (c : Codec R D)
    (ok? : D → Bool) (err : String → R → ValidationError)
    (mk : (d : D) → ok? d = true → D') (un : D' → D)
    (un_mk : ∀ d h, un (mk d h) = d)
    (ok_un : ∀ d', ok? (un d') = true)
    (mk_un : ∀ d', mk (un d') (ok_un d') = d') :
    Codec R D' where
  decode p r :=
    match c.decode p r with
    | .error e => .error e
    | .ok d => if h : ok? d = true then .ok (mk d h) else .error (err p r)
  encode d' := c.encode (un d')
  sound h := by
    split at h
    · contradiction
    · next d hd =>
      split at h
      · next hok =>
        injection h with h'
        subst h'
        rw [un_mk d hok]
        exact c.sound hd
      · contradiction
  complete d' := by
    show (match c.decode _ (c.encode (un d')) with
          | .error e => .error e
          | .ok d => if h : ok? d = true then .ok (mk d h) else .error (err _ (c.encode (un d')))) = Except.ok d'
    rw [c.complete (un d')]
    simp only [dif_pos (ok_un d')]
    exact congrArg Except.ok (mk_un d')

/-! ## Collection combinators: `list`, `nonEmpty`, `optional` -/

/-- Lift a codec over an array, fail-closed element by element (indexed paths).
Reuses the generic `parseList` and its once-proved round-trip. -/
@[expose] public def list {R D : Type} (c : Codec R D) : Codec (Array R) (Array D) where
  decode p rs :=
    match parseList c.decode p 0 rs.toList with
    | .ok ds => .ok ds.toArray
    | .error e => .error e
  encode ds := ds.map c.encode
  sound := by
    intro p r d h
    split at h
    · next ds hpl =>
      cases h
      have hsound := parseList_sound c.encode c.decode (fun he => c.sound he) 0 hpl
      have h2 : (ds.toArray.map c.encode).toList = r.toList := by
        simpa [Array.toList_map] using hsound
      exact Array.toList_inj.mp h2
    · contradiction
  complete ds := by
    show (match parseList c.decode _ 0 (ds.map c.encode).toList with
          | Except.ok d => Except.ok d.toArray | Except.error e => Except.error e) = Except.ok ds
    rw [Array.toList_map,
        parseList_complete c.encode c.decode (fun e => c.complete e) _ 0 ds.toList]

/-- Lift a codec over a non-empty array: `list` then the `ofArray` non-empty check
(fail-closed on empty). For fields like `derivedFrom`, `scenarios`, `deltas`. -/
@[expose] public def nonEmpty {R D : Type} (c : Codec R D) : Codec (Array R) (NonEmptyArray D) where
  decode p rs :=
    match (list c).decode p rs with
    | .ok ds => NonEmptyArray.ofArray p ds
    | .error e => .error e
  encode nea := (list c).encode nea.items
  sound := by
    intro p r nea h
    split at h
    · next ds hld =>
      have hitems := (NonEmptyArray.ofArray_sound h).1
      show nea.items.map c.encode = r
      rw [hitems]; exact (list c).sound hld
    · contradiction
  complete nea := by
    show (match (list c).decode _ ((list c).encode nea.items) with
          | .ok ds => NonEmptyArray.ofArray _ ds | .error e => .error e) = .ok nea
    rw [(list c).complete nea.items]
    exact NonEmptyArray.ofArray_complete nea

/-- Lift a codec over an optional field. -/
@[expose] public def optional {R D : Type} (c : Codec R D) : Codec (Option R) (Option D) where
  decode p r? :=
    match r? with
    | none => .ok none
    | some r =>
      match c.decode p r with
      | .ok d => .ok (some d)
      | .error e => .error e
  encode d? :=
    match d? with
    | none => none
    | some d => some (c.encode d)
  sound := by
    intro p r? d? h
    cases r? with
    | none => cases h; rfl
    | some r =>
      replace h : (match c.decode p r with
        | Except.ok d => Except.ok (some d) | Except.error e => Except.error e) = Except.ok d? := h
      split at h
      · next d0 hd =>
        injection h with h'
        subst h'
        show some (c.encode d0) = some r
        rw [c.sound hd]
      · next e he => simp at h
  complete d? := by
    cases d? with
    | none => rfl
    | some d =>
      show (match c.decode _ (c.encode d) with
            | Except.ok x => Except.ok (some x) | Except.error e => Except.error e) = Except.ok (some d)
      rw [c.complete d]

/-! ## Worked example: a real 2-field record composed from the algebra

A toy `Pair` record (two non-blank fields) built as `imap (prod nonBlank nonBlank)`.
Its decode/encode and the two round-trips are *inherited* — no per-field `split`
chain, no bespoke `validate_sound`. The `#guard`s exercise decode, the fail-closed
path, and the round-trip that `complete` proves. -/

private structure RawPair where
  a : String
  b : String

private structure Pair where
  a : NonBlank
  b : NonBlank

open Codec

private def pairCodec : Codec RawPair Pair :=
  -- read the raw record as a pair of strings, write the domain record as a pair of
  -- non-blanks — the two structure isos are plain `rfl`-level maps.
  let onProduct : Codec (String × String) (NonBlank × NonBlank) := prod nonBlank nonBlank
  let toDomain := imap onProduct
    (fun p => ({ a := p.1, b := p.2 } : Pair)) (fun d => (d.a, d.b))
    (by intro x; rfl) (by intro x; rfl)
  -- adapt the raw side (RawPair ↔ String × String) by pre/post-composing on decode
  -- and encode; stated directly since there is no `comap` combinator yet.
  { decode := fun p r => toDomain.decode p (r.a, r.b)
    encode := fun d => let s := toDomain.encode d; { a := s.1, b := s.2 }
    sound := by
      intro p r d h
      rw [toDomain.sound h]
    complete := by
      intro p d
      simpa using toDomain.complete d }

private def nb (s : String) (h : LeanUtil.nonemptyText s = true := by native_decide) : NonBlank := ⟨s, h⟩

-- Decodes a well-formed pair.
#guard match pairCodec.decode "ex" { a := "x", b := "y" } with
  | .ok d => d.a.value == "x" && d.b.value == "y"
  | .error _ => false

-- Fail-closed: a blank field is refused (inherited from `nonBlank`).
#guard match pairCodec.decode "ex" { a := "x", b := "  " } with
  | .error _ => true
  | .ok _ => false

-- Round-trip (what `complete` proves), on a concrete value.
#guard match pairCodec.decode "ex" (pairCodec.encode { a := nb "x", b := nb "y" }) with
  | .ok d => d.a.value == "x" && d.b.value == "y"
  | .error _ => false

end LeanSpec.Codec
