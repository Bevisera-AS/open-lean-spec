module

public import Lean.Data.Json
public import LeanJson
public import LeanSpec.Reflection
public import LeanSpec.Wiki
public meta import LeanJson
public meta import LeanSpec.Reflection
public meta import LeanSpec.Wiki

/-!
# JSON codec for reflections and the Wiki store

Wire encode/decode for `Reflection` and `Wiki`, mirroring `Codec/Precedent`.
Decoding is exact-field and fail-closed: unknown keys are rejected, unknown enum
tags are rejected (`invalidTag`), and the decoded `Raw` value must `validate` into
the domain type before it is accepted (blank id/learning and empty provenance are
refused there). `promoted` is optional on the wire and defaults to `noAction`.

The one wrinkle versus `Codec/Precedent` (whose fields are all strings): the two
closed enums (`ReflectionKind`, `PromotionTarget`) map to/from strings, and a
string outside the vocabulary is refused rather than coerced.
-/

namespace LeanSpec

open Lean
open LeanJson

public section

/-! ## Closed-enum codecs (fail-closed on unknown tags) -/

public def encodeReflectionKind : ReflectionKind → Json
  | .pattern     => Json.str "pattern"
  | .failureMode => Json.str "failureMode"
  | .strategy    => Json.str "strategy"

public def decodeReflectionKind (context : String) : String → Except DecodeError ReflectionKind
  | "pattern"     => .ok .pattern
  | "failureMode" => .ok .failureMode
  | "strategy"    => .ok .strategy
  | other         => .error (.invalidTag context "kind" other)

public def encodePromotionTarget : PromotionTarget → Json
  | .skill       => Json.str "skill"
  | .requirement => Json.str "requirement"
  | .steering    => Json.str "steering"
  | .noAction    => Json.str "noAction"

public def decodePromotionTarget (context : String) : String → Except DecodeError PromotionTarget
  | "skill"       => .ok .skill
  | "requirement" => .ok .requirement
  | "steering"    => .ok .steering
  | "noAction"    => .ok .noAction
  | other         => .error (.invalidTag context "promoted" other)

/-! ## Reflection -/

public def encodeReflection (r : Reflection) : Json :=
  Json.mkObj [
    ("id", Json.str r.id.value),
    ("kind", encodeReflectionKind r.kind),
    ("learning", Json.str r.learning.value),
    ("derivedFrom", Json.arr (r.derivedFrom.items.map (fun x => Json.str x.value))),
    ("promoted", encodePromotionTarget r.promoted)
  ]

public def encodeRawReflection (r : Raw.Reflection) : Json :=
  Json.mkObj [
    ("id", Json.str r.id),
    ("kind", encodeReflectionKind r.kind),
    ("learning", Json.str r.learning),
    ("derivedFrom", Json.arr (r.derivedFrom.map Json.str)),
    ("promoted", encodePromotionTarget r.promoted)
  ]

public def decodeRawReflection (j : Json) : Except DecodeError Raw.Reflection := do
  let context := "reflection"
  let o ← asObj context j
  exactFields context ["id", "kind", "learning", "derivedFrom", "promoted"] o
  let id ← strField context "id" j
  let kind ← decodeReflectionKind context (← strField context "kind" j)
  let learning ← strField context "learning" j
  let derivedFrom ← arrStrField context "derivedFrom" j
  let promoted ←
    match ← optStrField context "promoted" j with
    | none => pure PromotionTarget.noAction
    | some s => decodePromotionTarget context s
  pure { id, kind, learning, derivedFrom, promoted }

public def decodeReflection (j : Json) : Except DecodeError Reflection := do
  let raw ← decodeRawReflection j
  match Raw.Reflection.validate "reflection" raw with
  | .ok r => pure r
  | .error error => .error (.illFormed error.path error.pretty)

/-- Wire schema for OpenAI-compat extract of an untrusted reflection. -/
public def reflectionSchema : Json :=
  Json.mkObj [
    ("type", Json.str "object"),
    ("properties", Json.mkObj [
      ("id", Json.mkObj [("type", Json.str "string")]),
      ("kind", Json.mkObj [
        ("type", Json.str "string"),
        ("enum", Json.arr #[Json.str "pattern", Json.str "failureMode", Json.str "strategy"])]),
      ("learning", Json.mkObj [("type", Json.str "string")]),
      ("derivedFrom", Json.mkObj [
        ("type", Json.str "array"),
        ("items", Json.mkObj [("type", Json.str "string")])]),
      ("promoted", Json.mkObj [
        ("type", Json.str "string"),
        ("enum", Json.arr #[Json.str "skill", Json.str "requirement", Json.str "steering", Json.str "noAction"])])
    ]),
    ("required", Json.arr #[Json.str "id", Json.str "kind", Json.str "learning", Json.str "derivedFrom"]),
    ("additionalProperties", Json.bool false)
  ]

public def acceptReflection (j : Json) : Except DecodeError Reflection := decodeReflection j

public def acceptReflectionString (s : String) : Except DecodeError Reflection := do
  let j ← parseJson s
  acceptReflection j

/-! ## Supersession relations (the stored consolidation history) -/

public def encodeMorphismKind : TypeSystems.MorphismKind → Json
  | .supersedes   => Json.str "supersedes"
  | .exceptionOf  => Json.str "exceptionOf"
  | .precedentFor => Json.str "precedentFor"

public def decodeMorphismKind (context : String) : String → Except DecodeError TypeSystems.MorphismKind
  | "supersedes"   => .ok .supersedes
  | "exceptionOf"  => .ok .exceptionOf
  | "precedentFor" => .ok .precedentFor
  | other          => .error (.invalidTag context "kind" other)

public def encodeMorphism (m : TypeSystems.Morphism) : Json :=
  Json.mkObj [
    ("kind", encodeMorphismKind m.kind),
    ("source", Json.str m.source.value),
    ("target", Json.str m.target.value)
  ]

public def decodeMorphism (j : Json) : Except DecodeError TypeSystems.Morphism := do
  let context := "morphism"
  let o ← asObj context j
  exactFields context ["kind", "source", "target"] o
  let kind ← decodeMorphismKind context (← strField context "kind" j)
  let sourceS ← strField context "source" j
  let targetS ← strField context "target" j
  match NonBlank.parse s!"{context}.source" sourceS, NonBlank.parse s!"{context}.target" targetS with
  | .ok source, .ok target => pure { kind, source, target }
  | .error e, _ => .error (.illFormed e.path e.pretty)
  | _, .error e => .error (.illFormed e.path e.pretty)

/-! ## Wiki store -/

public def encodeWiki (w : Wiki) : Json :=
  Json.mkObj [
    ("entries", Json.arr (w.entries.map encodeReflection)),
    ("relations", Json.arr (w.relations.map encodeMorphism))
  ]

public def decodeWiki (j : Json) : Except DecodeError Wiki := do
  let context := "wiki"
  let o ← asObj context j
  exactFields context ["entries", "relations"] o
  let entArr ← arrField context "entries" j
  let entries ← mapArrM s!"{context}.entries" entArr (fun _ctx ej => decodeReflection ej)
  let relArr ← arrField context "relations" j
  let relations ← mapArrM s!"{context}.relations" relArr (fun _ctx mj => decodeMorphism mj)
  -- Re-establish the store's uniqueness invariant fail-closed: a persisted store
  -- with a duplicate reflection id is rejected rather than trusted.
  let items := entries.map (fun r => (⟨.provisional, Wiki.itemOf r⟩ : Kb.Boxed Reflection RunId))
  if h : Kb.UniqueIds items then
    pure { store := ⟨items, h⟩, relations }
  else
    .error (.illFormed context "duplicate reflection id")

public def acceptWikiString (s : String) : Except DecodeError Wiki := do
  let j ← parseJson s
  decodeWiki j

end

/-! ## Worked examples (executable `#guard`s) -/

private def nb (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : NonBlank := ⟨s, h⟩

private def rid (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : ReflectionId := ⟨s, h⟩

private def runid (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : RunId := ⟨s, h⟩

private def exR : Reflection :=
  { id := rid "wiki.read-first", kind := .strategy
    learning := nb "read the snapshot before proposing a delta"
    derivedFrom := ⟨#[runid "run-1", runid "run-2"], by native_decide⟩
    promoted := .skill }

-- Domain round-trip: encode then decode recovers the same reflection (compared by
-- re-encoded wire form, to avoid cross-module `BEq` on the enum fields).
#guard match acceptReflection (encodeReflection exR) with
  | .ok r => (encodeReflection r).compress == (encodeReflection exR).compress
  | .error _ => false

-- Unknown top-level key is refused.
#guard match acceptReflectionString
    "{\"id\":\"r1\",\"kind\":\"pattern\",\"learning\":\"x\",\"derivedFrom\":[\"run-1\"],\"oops\":1}" with
  | .error (.unknownFields "reflection" ["oops"]) => true
  | _ => false

-- Unknown enum tag is refused (fail-closed, not coerced).
#guard match acceptReflectionString
    "{\"id\":\"r1\",\"kind\":\"bogus\",\"learning\":\"x\",\"derivedFrom\":[\"run-1\"]}" with
  | .error (.invalidTag "reflection" "kind" "bogus") => true
  | _ => false

-- Absent `promoted` defaults to noAction.
#guard match acceptReflectionString
    "{\"id\":\"r1\",\"kind\":\"pattern\",\"learning\":\"x\",\"derivedFrom\":[\"run-1\"]}" with
  | .ok r => match r.promoted with | .noAction => true | _ => false
  | _ => false

-- Blank learning is refused by validation.
#guard match acceptReflectionString
    "{\"id\":\"r1\",\"kind\":\"pattern\",\"learning\":\"  \",\"derivedFrom\":[\"run-1\"]}" with
  | .error (.illFormed _ _) => true
  | _ => false

-- Empty provenance is refused by validation (a learning must come from a run).
#guard match acceptReflectionString
    "{\"id\":\"r1\",\"kind\":\"pattern\",\"learning\":\"x\",\"derivedFrom\":[]}" with
  | .error (.illFormed _ _) => true
  | _ => false

-- Wiki round-trip through the store: recording exR mints a canonical node and keeps
-- the primary (2 entries), plus one supersedes edge — all survive the round-trip.
#guard match decodeWiki (encodeWiki (Wiki.record {} exR)) with
  | .ok w => w.entries.size == 2 && w.relations.size == 1
  | .error _ => false

-- Fail-closed: a persisted store with a duplicate reflection id is rejected.
#guard match decodeWiki (Json.mkObj [
    ("entries", Json.arr #[encodeReflection exR, encodeReflection exR]),
    ("relations", Json.arr #[])]) with
  | .error (.illFormed "wiki" _) => true
  | _ => false

end LeanSpec
