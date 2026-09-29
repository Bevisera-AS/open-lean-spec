module

public import Lean.Data.Json
public import LeanJson
public import LeanSpec.Types
public meta import LeanJson
public meta import LeanSpec.Types

namespace LeanSpec

open Lean
open LeanJson

public section

public def encodeStrength : Strength → String
  | .shall => "shall"
  | .must => "must"
  | .should => "should"

public def decodeStrength (context : String) (j : Json) : Except DecodeError Strength := do
  let raw ← strField context "strength" j
  match raw with
  | "shall" => pure .shall
  | "must" => pure .must
  | "should" => pure .should
  | other => .error (.invalidTag context "strength" other)

public def encodeCheck : CheckStatus → Json
  | .executable => Json.mkObj [("tag", Json.str "executable")]
  | .deferred reason =>
      Json.mkObj [("tag", Json.str "deferred"), ("reason", Json.str reason.value)]

public def encodeRawCheck : Raw.CheckStatus → Json
  | .executable => Json.mkObj [("tag", Json.str "executable")]
  | .deferred reason =>
      Json.mkObj [("tag", Json.str "deferred"), ("reason", Json.str reason)]

public def decodeRawCheck (context : String) (j : Json) : Except DecodeError Raw.CheckStatus := do
  let o ← asObj context j
  let tag ← strField context "tag" j
  match tag with
  | "executable" =>
    exactFields context ["tag"] o
    pure .executable
  | "deferred" =>
    exactFields context ["tag", "reason"] o
    let reason ← strField context "reason" j
    pure (.deferred reason)
  | other => .error (.invalidTag context "tag" other)

public def decodeCheck (context : String) (j : Json) : Except DecodeError CheckStatus := do
  let raw ← decodeRawCheck context j
  match raw.validate context with
  | .ok check => pure check
  | .error error => .error (.illFormed error.path error.pretty)

public def encodeScenario (s : Scenario) : Json :=
  let base : List (String × Json) := [
    ("name", Json.str s.name.value),
    ("when", Json.str s.whenText.value),
    ("then", Json.str s.thenText.value),
    ("check", encodeCheck s.check)
  ]
  let fields :=
    match s.given? with
    | some g => ("given", Json.str g.value) :: base
    | none => base
  Json.mkObj fields

public def encodeRawScenario (s : Raw.Scenario) : Json :=
  let base : List (String × Json) := [
    ("name", Json.str s.name),
    ("when", Json.str s.whenText),
    ("then", Json.str s.thenText),
    ("check", encodeRawCheck s.check)
  ]
  let fields :=
    match s.given? with
    | some g => ("given", Json.str g) :: base
    | none => base
  Json.mkObj fields

public def decodeRawScenario (context : String) (j : Json) : Except DecodeError Raw.Scenario := do
  let o ← asObj context j
  exactFields context ["name", "given", "when", "then", "check"] o
  let name ← strField context "name" j
  let given? ← optStrField context "given" j
  let whenText ← strField context "when" j
  let thenText ← strField context "then" j
  let checkJson ← field context "check" j
  let check ← decodeRawCheck s!"{context}.check" checkJson
  pure { name, given?, whenText, thenText, check }

public def decodeScenario (context : String) (j : Json) : Except DecodeError Scenario := do
  let raw ← decodeRawScenario context j
  match raw.validate context with
  | .ok scenario => pure scenario
  | .error error => .error (.illFormed error.path error.pretty)

public def encodeRequirement (r : Requirement) : Json :=
  Json.mkObj [
    ("id", Json.str r.id.value),
    ("shall", Json.str r.shall.value),
    ("strength", Json.str (encodeStrength r.strength)),
    ("scenarios", Json.arr (r.scenarios.toArray.map encodeScenario))
  ]

public def encodeRawRequirement (r : Raw.Requirement) : Json :=
  Json.mkObj [
    ("id", Json.str r.id),
    ("shall", Json.str r.shall),
    ("strength", Json.str (encodeStrength r.strength)),
    ("scenarios", Json.arr (r.scenarios.map encodeRawScenario))
  ]

public def decodeRawRequirement (context : String) (j : Json) :
    Except DecodeError Raw.Requirement := do
  let o ← asObj context j
  exactFields context ["id", "shall", "strength", "scenarios"] o
  let id ← strField context "id" j
  let shall ← strField context "shall" j
  let strength ← decodeStrength context j
  let scenariosJson ← arrField context "scenarios" j
  let scenarios ← mapArrM s!"{context}.scenarios" scenariosJson decodeRawScenario
  pure { id, shall, strength, scenarios }

public def decodeRequirementAt (context : String) (j : Json) : Except DecodeError Requirement := do
  let raw ← decodeRawRequirement context j
  match raw.validate context with
  | .ok requirement => pure requirement
  | .error error => .error (.illFormed error.path error.pretty)

/-- Decode a top-level requirement. Nested codecs use `decodeRequirementAt` to preserve paths. -/
public def decodeRequirement (j : Json) : Except DecodeError Requirement :=
  decodeRequirementAt "requirement" j

/-- Shape decode plus well-formedness. No silent defaults. -/
public def acceptRequirement (j : Json) : Except DecodeError Requirement :=
  decodeRequirement j

public def acceptRequirementString (s : String) : Except DecodeError Requirement := do
  let j ← parseJson s
  acceptRequirement j

/-- Wire schema for OpenAI-compat `response_format.json_schema`. Hand-written until deriving exists. -/
public def requirementSchema : Json :=
  let checkSchema := Json.mkObj [
    ("oneOf", Json.arr #[
      Json.mkObj [
        ("type", Json.str "object"),
        ("properties", Json.mkObj [
          ("tag", Json.mkObj [("const", Json.str "executable")])
        ]),
        ("required", Json.arr #[Json.str "tag"]),
        ("additionalProperties", Json.bool false)
      ],
      Json.mkObj [
        ("type", Json.str "object"),
        ("properties", Json.mkObj [
          ("tag", Json.mkObj [("const", Json.str "deferred")]),
          ("reason", Json.mkObj [("type", Json.str "string")])
        ]),
        ("required", Json.arr #[Json.str "tag", Json.str "reason"]),
        ("additionalProperties", Json.bool false)
      ]
    ])
  ]
  let scenarioSchema := Json.mkObj [
    ("type", Json.str "object"),
    ("properties", Json.mkObj [
      ("name", Json.mkObj [("type", Json.str "string")]),
      ("given", Json.mkObj [("type", Json.str "string")]),
      ("when", Json.mkObj [("type", Json.str "string")]),
      ("then", Json.mkObj [("type", Json.str "string")]),
      ("check", checkSchema)
    ]),
    ("required", Json.arr #[Json.str "name", Json.str "when", Json.str "then", Json.str "check"]),
    ("additionalProperties", Json.bool false)
  ]
  Json.mkObj [
    ("type", Json.str "object"),
    ("properties", Json.mkObj [
      ("id", Json.mkObj [("type", Json.str "string")]),
      ("shall", Json.mkObj [("type", Json.str "string")]),
      ("strength", Json.mkObj [
        ("type", Json.str "string"),
        ("enum", Json.arr #[Json.str "shall", Json.str "must", Json.str "should"])
      ]),
      ("scenarios", Json.mkObj [
        ("type", Json.str "array"),
        ("minItems", (1 : Nat)),
        ("items", scenarioSchema)
      ])
    ]),
    ("required", Json.arr #[Json.str "id", Json.str "shall", Json.str "strength", Json.str "scenarios"]),
    ("additionalProperties", Json.bool false)
  ]

#guard
  match acceptRequirement (encodeRequirement {
    id := ⟨"r", by native_decide⟩
    shall := ⟨"does a thing", by native_decide⟩
    scenarios := ⟨#[{
      name := ⟨"n", by native_decide⟩
      whenText := ⟨"w", by native_decide⟩
      thenText := ⟨"t", by native_decide⟩
      check := .deferred ⟨"later", by native_decide⟩
    }], by native_decide⟩
  }) with
  | .ok r => r.id.value == "r" && r.strength == .shall
  | .error _ => false

end

end LeanSpec
