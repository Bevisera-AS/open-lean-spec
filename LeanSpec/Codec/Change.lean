module

public import Lean.Data.Json
public import LeanJson
public import LeanSpec.Change
public import LeanSpec.Codec.Requirement
public meta import LeanJson
public meta import LeanSpec.Change
public meta import LeanSpec.Codec.Requirement

namespace LeanSpec

open Lean
open LeanJson

public section

public def encodeDelta : Delta → Json
  | .added r =>
    Json.mkObj [
      ("tag", Json.str "added"),
      ("requirement", encodeRequirement r)
    ]
  | .modified r =>
    Json.mkObj [
      ("tag", Json.str "modified"),
      ("id", Json.str r.id.value),
      ("requirement", encodeRequirement r)
    ]
  | .removed id reason migration =>
    Json.mkObj [
      ("tag", Json.str "removed"),
      ("id", Json.str id.value),
      ("reason", Json.str reason.value),
      ("migration", Json.str migration.value)
    ]
  | .renamed move =>
    Json.mkObj [
      ("tag", Json.str "renamed"),
      ("from", Json.str move.frm.value),
      ("to", Json.str move.to.value)
    ]

public def encodeRawDelta : Raw.Delta → Json
  | .added r =>
    Json.mkObj [
      ("tag", Json.str "added"),
      ("requirement", encodeRawRequirement r)
    ]
  | .modified id r =>
    Json.mkObj [
      ("tag", Json.str "modified"),
      ("id", Json.str id),
      ("requirement", encodeRawRequirement r)
    ]
  | .removed id reason migration =>
    Json.mkObj [
      ("tag", Json.str "removed"),
      ("id", Json.str id),
      ("reason", Json.str reason),
      ("migration", Json.str migration)
    ]
  | .renamed frm to =>
    Json.mkObj [
      ("tag", Json.str "renamed"),
      ("from", Json.str frm),
      ("to", Json.str to)
    ]

public def encodeRawChange (c : Raw.Change) : Json :=
  Json.mkObj [
    ("id", Json.str c.id),
    ("why", Json.str c.why),
    ("deltas", Json.arr (c.deltas.map encodeRawDelta))
  ]

/-- Wire schema for OpenAI-compat extract of an untrusted change. -/
public def changeSchema : Json :=
  Json.mkObj [
    ("type", Json.str "object"),
    ("properties", Json.mkObj [
      ("id", Json.mkObj [("type", Json.str "string")]),
      ("why", Json.mkObj [("type", Json.str "string")]),
      ("deltas", Json.mkObj [
        ("type", Json.str "array"),
        ("minItems", (1 : Nat)),
        ("items", Json.mkObj [("type", Json.str "object")])
      ])
    ]),
    ("required", Json.arr #[Json.str "id", Json.str "why", Json.str "deltas"]),
    ("additionalProperties", Json.bool false)
  ]

public def decodeRawDelta (context : String) (j : Json) : Except DecodeError Raw.Delta := do
  let o ← asObj context j
  let tag ← strField context "tag" j
  match tag with
  | "added" =>
    exactFields context ["tag", "requirement"] o
    let rj ← field context "requirement" j
    let r ← decodeRawRequirement s!"{context}.requirement" rj
    pure (.added r)
  | "modified" =>
    exactFields context ["tag", "id", "requirement"] o
    let id ← strField context "id" j
    let rj ← field context "requirement" j
    let r ← decodeRawRequirement s!"{context}.requirement" rj
    pure (.modified id r)
  | "removed" =>
    exactFields context ["tag", "id", "reason", "migration"] o
    let id ← strField context "id" j
    let reason ← strField context "reason" j
    let migration ← strField context "migration" j
    pure (.removed id reason migration)
  | "renamed" =>
    exactFields context ["tag", "from", "to"] o
    let frm ← strField context "from" j
    let to ← strField context "to" j
    pure (.renamed frm to)
  | other => .error (.invalidTag context "tag" other)

public def decodeDelta (context : String) (j : Json) : Except DecodeError Delta := do
  let raw ← decodeRawDelta context j
  match raw.validate context with
  | .ok delta => pure delta
  | .error error => .error (.illFormed error.path error.pretty)

public def encodeChange (c : Change) : Json :=
  Json.mkObj [
    ("id", Json.str c.id.value),
    ("why", Json.str c.why.value),
    ("deltas", Json.arr (c.deltas.toArray.map encodeDelta))
  ]

public def decodeRawChange (j : Json) : Except DecodeError Raw.Change := do
  let context := "change"
  let o ← asObj context j
  exactFields context ["id", "why", "deltas"] o
  let id ← strField context "id" j
  let why ← strField context "why" j
  let deltasJson ← arrField context "deltas" j
  let deltas ← mapArrM s!"{context}.deltas" deltasJson decodeRawDelta
  pure { id, why, deltas }

public def decodeChange (j : Json) : Except DecodeError Change := do
  let raw ← decodeRawChange j
  match raw.validate "change" with
  | .ok change => pure change
  | .error error => .error (.illFormed error.path error.pretty)

/-- Shape decode plus well-formedness. No silent defaults. -/
public def acceptChange (j : Json) : Except DecodeError Change :=
  decodeChange j

public def acceptChangeString (s : String) : Except DecodeError Change := do
  let j ← parseJson s
  acceptChange j

#guard
  let req : Requirement := {
    id := ⟨"r", by native_decide⟩
    shall := ⟨"does a thing", by native_decide⟩
    scenarios := ⟨#[{
      name := ⟨"n", by native_decide⟩
      whenText := ⟨"w", by native_decide⟩
      thenText := ⟨"t", by native_decide⟩
      check := .executable
    }], by native_decide⟩
  }
  let c : Change := {
    id := ⟨"add-r", by native_decide⟩
    why := ⟨"need r", by native_decide⟩
    deltas := ⟨#[.added req, .renamed {
      frm := ⟨"old", by native_decide⟩
      to := ⟨"new", by native_decide⟩
      property := by native_decide
    }], by native_decide⟩
  }
  match acceptChange (encodeChange c) with
  | .ok c2 => c2 == c
  | .error _ => false

#guard
  let req : Requirement := {
    id := ⟨"r", by native_decide⟩
    shall := ⟨"does a thing", by native_decide⟩
    scenarios := ⟨#[{
      name := ⟨"n", by native_decide⟩
      whenText := ⟨"w", by native_decide⟩
      thenText := ⟨"t", by native_decide⟩
      check := .executable
    }], by native_decide⟩
  }
  let c : Change := {
    id := ⟨"add-r", by native_decide⟩
    why := ⟨"need r", by native_decide⟩
    deltas := ⟨#[.added req], by native_decide⟩
  }
  match decodeRawChange (encodeRawChange c.toRaw) with
  | .ok raw => raw == c.toRaw
  | .error _ => false

#guard
  match acceptChangeString
      "{\"id\":\"c\",\"why\":\"w\",\"deltas\":[{\"tag\":\"renamed\",\"from\":\"a\",\"to\":\"b\"}],\"oops\":true}" with
  | .error (.unknownFields "change" ["oops"]) => true
  | _ => false

end

end LeanSpec
