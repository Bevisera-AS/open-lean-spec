import Lean.Data.Json

/-! The code generator recurses once per node of a big literal, so a large `json%`
(a 360-row schedule) hits "maximum recursion depth in the code generator". A large
`json%` with no `$x` hole is therefore expanded to `Json.parse "<text>"`: still a
`Lean.Json`, same syntax for authors. Small or `$x` literals use the stock macro. -/

namespace Lean.Json
open Lean

private partial def size (s : Syntax) : Nat := s.getArgs.foldl (· + size ·) 1
private partial def hasHole (s : Syntax) : Bool := s.isAntiquot || s.getArgs.any hasHole

private def sci (n : TSyntax `scientific) (neg : Bool) : MacroM String := do
  let some (m, s, e) := n.raw.isScientificLit? | Macro.throwUnsupported
  let v := if s then s!"{m}e-{e}" else toString (m * 10 ^ e)
  pure (if neg then "-" ++ v else v)

private partial def text : TSyntax `json → MacroM String
  | `(json| null) => pure "null"
  | `(json| true) => pure "true"
  | `(json| false) => pure "false"
  | `(json| $s:str) => pure (Json.str s.getString).compress
  | `(json| $n:num) => pure (toString n.getNat)
  | `(json| -$n:num) => pure s!"-{n.getNat}"
  | `(json| $n:scientific) => sci n false
  | `(json| -$n:scientific) => sci n true
  | `(json| [$[$xs],*]) => do pure s!"[{",".intercalate (← xs.toList.mapM text)}]"
  | `(json| {$[$ks:jsonIdent : $vs:json],*}) => do
    let ks ← ks.mapM fun
      | `(jsonIdent| $k:ident) => pure (Json.str k.getId.toString).compress
      | `(jsonIdent| $k:str) => pure (Json.str k.getString).compress
      | _ => Macro.throwUnsupported
    let vs ← vs.mapM text
    pure s!"\{{",".intercalate ((ks.zip vs).toList.map fun (k, v) => k ++ ":" ++ v)}}"
  | _ => Macro.throwUnsupported

macro_rules
  | `(json% $j:json) => do
    if hasHole j.raw || size j.raw < 200 then Macro.throwUnsupported
    let t ← text j
    if let .error e := Json.parse t then Macro.throwError s!"json%: {e}"
    `(((Lean.Json.parse $(quote t)).toOption).getD Lean.Json.null)

end Lean.Json
