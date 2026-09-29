module

public import Lean.Data.Json
public import LeanJson
public import LeanSpec.Snapshot
public import LeanSpec.Codec.Requirement
public import LeanSpec.Codec.Design
public meta import LeanJson
public meta import LeanSpec.Snapshot
public meta import LeanSpec.Codec.Requirement
public meta import LeanSpec.Codec.Design

namespace LeanSpec

open Lean
open LeanJson

public section

public def encodeSnapshot (s : SpecSnapshot) : Json :=
  let fields : List (String × Json) := [
    ("requirements", Json.arr (s.requirements.map encodeRequirement))
  ]
  let fields :=
    if s.designs.isEmpty then fields
    else fields ++ [("designs", Json.arr (s.designs.map encodeDesignUnit))]
  Json.mkObj fields

public def decodeSnapshot (j : Json) : Except DecodeError SpecSnapshot := do
  let context := "snapshot"
  let o ← asObj context j
  exactFields context ["requirements", "designs"] o
  let reqsJson ← arrField context "requirements" j
  let requirements ← mapArrM s!"{context}.requirements" reqsJson decodeRequirementAt
  let designs ←
    match j.getObjVal? "designs" with
    | .error _ => pure (#[] : Array DesignUnit)
    | .ok v =>
      match v.getArr? with
      | .error _ => .error (.wrongType context "designs" "array")
      | .ok arr => mapArrM s!"{context}.designs" arr decodeDesignUnitAt
  match SpecSnapshot.ofDesigned s!"{context}.requirements" requirements designs with
  | .ok s => pure s
  | .error error => .error (.illFormed error.path error.pretty)

public def acceptSnapshot (j : Json) : Except DecodeError SpecSnapshot :=
  decodeSnapshot j

public def acceptSnapshotString (s : String) : Except DecodeError SpecSnapshot := do
  let j ← parseJson s
  acceptSnapshot j

#guard
  let snap : SpecSnapshot := {
    requirements := #[{
      id := ⟨"r", by native_decide⟩
      shall := ⟨"does a thing", by native_decide⟩
      scenarios := ⟨#[{
        name := ⟨"n", by native_decide⟩
        whenText := ⟨"w", by native_decide⟩
        thenText := ⟨"t", by native_decide⟩
        check := .executable
      }], by native_decide⟩
    }]
    uniqueIds := by native_decide
  }
  match acceptSnapshot (encodeSnapshot snap) with
  | .ok s => s == snap
  | .error _ => false

#guard
  match acceptSnapshotString "{\"requirements\":[],\"oops\":true}" with
  | .error (.unknownFields "snapshot" ["oops"]) => true
  | _ => false

end

end LeanSpec
