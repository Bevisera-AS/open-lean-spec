module

public import Lean.Data.Json
public import LeanJson
public import LeanSpec.Precedent
public import LeanSpec.Codec.Change
public meta import LeanJson
public meta import LeanSpec.Precedent
public meta import LeanSpec.Codec.Change

/-!
# JSON codec for precedents

Wire encode/decode for `Supersedes` and `PrecedentedChange`, mirroring
`Codec/Change`. Decoding is exact-field and fail-closed: unknown keys are
rejected, and the decoded `Raw` value must `validate` into the domain type
before it is accepted. `precedents` is optional on the wire and defaults to
empty.
-/

namespace LeanSpec

open Lean
open LeanJson

public section

public def encodeSupersedes (rel : Supersedes) : Json :=
  Json.mkObj [
    ("source", Json.str rel.source.value),
    ("target", Json.str rel.target.value),
    ("rationale", Json.str rel.rationale.value)
  ]

public def encodeRawSupersedes (rel : Raw.Supersedes) : Json :=
  Json.mkObj [
    ("source", Json.str rel.source),
    ("target", Json.str rel.target),
    ("rationale", Json.str rel.rationale)
  ]

public def decodeRawSupersedes (context : String) (j : Json) :
    Except DecodeError Raw.Supersedes := do
  let o ← asObj context j
  exactFields context ["source", "target", "rationale"] o
  let source ← strField context "source" j
  let target ← strField context "target" j
  let rationale ← strField context "rationale" j
  pure { source, target, rationale }

public def decodeSupersedes (context : String) (j : Json) :
    Except DecodeError Supersedes := do
  let raw ← decodeRawSupersedes context j
  match Supersedes.validate context raw with
  | .ok rel => pure rel
  | .error error => .error (.illFormed error.path error.pretty)

public def encodePrecedentedChange (pc : PrecedentedChange) : Json :=
  Json.mkObj [
    ("change", encodeChange pc.change),
    ("precedents", Json.arr (pc.precedents.map encodeSupersedes))
  ]

public def encodeRawPrecedentedChange (pc : Raw.PrecedentedChange) : Json :=
  Json.mkObj [
    ("change", encodeRawChange pc.change),
    ("precedents", Json.arr (pc.precedents.map encodeRawSupersedes))
  ]

/-- Wire schema for OpenAI-compat extract of an untrusted precedented change. -/
public def precedentedChangeSchema : Json :=
  Json.mkObj [
    ("type", Json.str "object"),
    ("properties", Json.mkObj [
      ("change", changeSchema),
      ("precedents", Json.mkObj [
        ("type", Json.str "array"),
        ("items", Json.mkObj [("type", Json.str "object")])
      ])
    ]),
    ("required", Json.arr #[Json.str "change"]),
    ("additionalProperties", Json.bool false)
  ]

public def decodeRawPrecedentedChange (j : Json) :
    Except DecodeError Raw.PrecedentedChange := do
  let context := "precedentedChange"
  let o ← asObj context j
  exactFields context ["change", "precedents"] o
  let changeJson ← field context "change" j
  let change ← decodeRawChange changeJson
  let precedents ←
    match j.getObjVal? "precedents" with
    | .error _ => pure #[]
    | .ok pj =>
      match pj.getArr? with
      | .ok arr => mapArrM s!"{context}.precedents" arr decodeRawSupersedes
      | .error _ => .error (.wrongType context "precedents" "array")
  pure { change, precedents }

public def decodePrecedentedChange (j : Json) :
    Except DecodeError PrecedentedChange := do
  let raw ← decodeRawPrecedentedChange j
  match Raw.PrecedentedChange.validate "precedentedChange" raw with
  | .ok pc => pure pc
  | .error error => .error (.illFormed error.path error.pretty)

/-- Shape decode plus well-formedness. No silent defaults beyond an absent
`precedents` meaning "no precedents". -/
public def acceptPrecedentedChange (j : Json) : Except DecodeError PrecedentedChange :=
  decodePrecedentedChange j

public def acceptPrecedentedChangeString (s : String) :
    Except DecodeError PrecedentedChange := do
  let j ← parseJson s
  acceptPrecedentedChange j

-- Domain round-trip: encode a precedented change, decode it back.
#guard
  let req : Requirement := {
    id := ⟨"cap.overview", by native_decide⟩
    shall := ⟨"show a summary dashboard", by native_decide⟩
    scenarios := ⟨#[{
      name := ⟨"n", by native_decide⟩
      whenText := ⟨"w", by native_decide⟩
      thenText := ⟨"t", by native_decide⟩
      check := .executable
    }], by native_decide⟩
  }
  let c : Change := {
    id := ⟨"tighten-overview", by native_decide⟩
    why := ⟨"overview subsumes detail", by native_decide⟩
    deltas := ⟨#[.modified req], by native_decide⟩
  }
  let sup : Supersedes :=
    ⟨⟨"cap.overview", by native_decide⟩, ⟨"cap.detail", by native_decide⟩,
      ⟨"the dashboard replaces the detail table", by native_decide⟩, by native_decide⟩
  let pc : PrecedentedChange := { change := c, precedents := #[sup] }
  match acceptPrecedentedChange (encodePrecedentedChange pc) with
  | .ok pc2 => pc2.change == pc.change && pc2.precedents == pc.precedents
  | .error _ => false

-- Absent precedents decodes to an empty precedent set.
#guard
  match acceptPrecedentedChangeString
      "{\"change\":{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"renamed\",\"from\":\"a\",\"to\":\"b\"}]}}" with
  | .ok pc => pc.precedents.isEmpty
  | .error _ => false

-- Unknown top-level keys are refused.
#guard
  match acceptPrecedentedChangeString
      "{\"change\":{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"renamed\",\"from\":\"a\",\"to\":\"b\"}]},\"oops\":1}" with
  | .error (.unknownFields "precedentedChange" ["oops"]) => true
  | _ => false

-- A self-superseding precedent fails validation (fail-closed).
#guard
  match acceptPrecedentedChangeString
      "{\"change\":{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"renamed\",\"from\":\"a\",\"to\":\"b\"}]},\"precedents\":[{\"source\":\"x\",\"target\":\"x\",\"rationale\":\"r\"}]}" with
  | .error (.illFormed _ _) => true
  | _ => false

end

end LeanSpec
