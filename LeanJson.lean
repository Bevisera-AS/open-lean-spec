module

public import Lean.Data.Json
public import LeanUtil
public meta import LeanUtil

namespace LeanJson

open Lean
open LeanUtil

public section

public inductive DecodeError where
  | invalidJson (detail : String)
  | expectedObject (context : String)
  | expectedArray (context : String)
  | missingField (context field : String)
  | wrongType (context field expected : String)
  | unknownFields (context : String) (fields : List String)
  | invalidTag (context field value : String)
  | illFormed (context detail : String)
  deriving Repr, BEq

public def DecodeError.pretty : DecodeError → String
  | .invalidJson d => s!"invalid JSON: {d}"
  | .expectedObject ctx => s!"{ctx}: object expected"
  | .expectedArray ctx => s!"{ctx}: array expected"
  | .missingField ctx field => s!"{ctx}: missing field `{field}`"
  | .wrongType ctx field expected => s!"{ctx}.{field}: expected {expected}"
  | .unknownFields ctx fields => s!"{ctx}: unknown fields {joinSep ", " fields}"
  | .invalidTag ctx field value => s!"{ctx}.{field}: unknown tag `{value}`"
  | .illFormed ctx detail => s!"{ctx}: {detail}"

public def parseJson (s : String) : Except DecodeError Json :=
  match Json.parse s with
  | .ok j => .ok j
  | .error e => .error (.invalidJson e)

public def asObj (context : String) (j : Json) :
    Except DecodeError (Std.TreeMap.Raw String Json compare) :=
  match j.getObj? with
  | .ok o => .ok o
  | .error _ => .error (.expectedObject context)

public def exactFields (context : String) (allowed : List String)
    (o : Std.TreeMap.Raw String Json compare) : Except DecodeError Unit :=
  let extras := o.toList.map (·.1) |>.filter (fun k => !allowed.contains k)
  if extras.isEmpty then .ok () else .error (.unknownFields context extras)

public def field (context key : String) (j : Json) : Except DecodeError Json :=
  match j.getObjVal? key with
  | .ok v => .ok v
  | .error _ => .error (.missingField context key)

public def strField (context key : String) (j : Json) : Except DecodeError String := do
  let v ← field context key j
  match v.getStr? with
  | .ok s => pure s
  | .error _ => .error (.wrongType context key "string")

public def optStrField (context key : String) (j : Json) : Except DecodeError (Option String) :=
  match j.getObjVal? key with
  | .error _ => .ok none
  | .ok v =>
    match v.getStr? with
    | .ok s => .ok (some s)
    | .error _ => .error (.wrongType context key "string")

public def optNullableStrField (context key : String) (j : Json) : Except DecodeError (Option String) :=
  match j.getObjVal? key with
  | .error _ => .ok none
  | .ok v =>
    if v.isNull then .ok none
    else
      match v.getStr? with
      | .ok s => .ok (some s)
      | .error _ => .error (.wrongType context key "string or null")

public def arrField (context key : String) (j : Json) : Except DecodeError (Array Json) := do
  let v ← field context key j
  match v.getArr? with
  | .ok a => pure a
  | .error _ => .error (.wrongType context key "array")

public def arrStrField (context key : String) (j : Json) : Except DecodeError (Array String) := do
  let xs ← arrField context key j
  xs.mapM fun item =>
    match item.getStr? with
    | .ok s => pure s
    | .error _ => .error (.wrongType context key "array of strings")

public def natField (context key : String) (j : Json) : Except DecodeError Nat := do
  let v ← field context key j
  match v.getNat? with
  | .ok n => pure n
  | .error _ => .error (.wrongType context key "natural number")

public def mapArrM (context : String) (xs : Array Json)
    (f : String → Json → Except DecodeError α) : Except DecodeError (Array α) :=
  let rec go (i : Nat) : List Json → Except DecodeError (Array α)
    | [] => .ok #[]
    | x :: rest => do
      let v ← f s!"{context}[{i}]" x
      let vs ← go (i + 1) rest
      pure (#[v] ++ vs)
  go 0 xs.toList

end

end LeanJson
