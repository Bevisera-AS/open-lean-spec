module

public import Lean.Data.Json
public import LeanJson
public import LeanSpec.Design
public meta import LeanJson
public meta import LeanSpec.Design

namespace LeanSpec

open Lean
open LeanJson

public section

public def encodeDesignUnit (d : DesignUnit) : Json :=
  Json.mkObj [
    ("id", Json.str d.id.value),
    ("surface", Json.str d.surface.toToken),
    ("target", Json.str d.target.toToken),
    ("interfaces", Json.arr (d.interfaces.toArray.map fun n => Json.str n.value)),
    ("functions", Json.arr (d.functions.map fun n => Json.str n.value)),
    ("tests", Json.arr (d.tests.toArray.map fun n => Json.str n.value)),
    ("theorems", Json.arr (d.theorems.map fun n => Json.str n.value))
  ]

public def decodeRawDesignUnitAt (context : String) (j : Json) :
    Except DecodeError Raw.DesignUnit := do
  let o ← asObj context j
  exactFields context ["id", "surface", "target", "interfaces", "functions", "tests", "theorems"] o
  let id ← strField context "id" j
  -- surface/target are optional; absent fields keep the native/lean4 defaults.
  let surface ← (optStrField context "surface" j).map (·.getD "native")
  let target ← (optStrField context "target" j).map (·.getD "lean4")
  let interfaces ← arrStrField context "interfaces" j
  let functions ← arrStrField context "functions" j
  let tests ← arrStrField context "tests" j
  let theorems ← arrStrField context "theorems" j
  pure { id, surface, target, interfaces, functions, tests, theorems }

public def decodeDesignUnitAt (context : String) (j : Json) : Except DecodeError DesignUnit := do
  let raw ← decodeRawDesignUnitAt context j
  match raw.validate context with
  | .ok d => pure d
  | .error error => .error (.illFormed error.path error.pretty)

public def decodeDesignUnit (j : Json) : Except DecodeError DesignUnit :=
  decodeDesignUnitAt "design" j

public def acceptDesignUnit (j : Json) : Except DecodeError DesignUnit :=
  decodeDesignUnit j

#guard
  let d : DesignUnit := {
    id := ⟨"theme.selection", by native_decide⟩
    interfaces := ⟨#[⟨"Theme", by native_decide⟩], by native_decide⟩
    functions := #[⟨"toggleDark", by native_decide⟩]
    tests := ⟨#[⟨"toggleDarkCheck", by native_decide⟩], by native_decide⟩
    theorems := #[⟨"toggleDarkCheck_of_light", by native_decide⟩]
  }
  match acceptDesignUnit (encodeDesignUnit d) with
  | .ok got => got == d
  | .error _ => false

#guard
  match decodeDesignUnit (Json.mkObj [
    ("id", Json.str "r"),
    ("interfaces", Json.arr #[]),
    ("functions", Json.arr #[]),
    ("tests", Json.arr #[Json.str "t"]),
    ("theorems", Json.arr #[])
  ]) with
  | .error (.illFormed "design.interfaces" _) => true
  | _ => false

end

end LeanSpec
