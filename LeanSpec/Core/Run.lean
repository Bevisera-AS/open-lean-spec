import Lean.Data.Json

/-! Running a program on an example: structural JSON equality, a bounded process
run, and one-line clipping for failure reports. -/

namespace LeanSpec.Core
open Lean

/-- Structural JSON equality: object key order ignored, numbers by value. -/
partial def jeq : Json → Json → Bool
  | .num a, .num b => a.mantissa * (10 ^ b.exponent : Nat) == b.mantissa * (10 ^ a.exponent : Nat)
  | .arr a, .arr b => a.size == b.size && (a.zip b).all fun (x, y) => jeq x y
  | .obj a, .obj b =>
    a.size == b.size && a.toList.all fun (k, v) =>
      match (Json.obj b).getObjVal? k with | .ok w => jeq v w | .error _ => false
  | a, b => a == b

/-- One-line, <= 200 chars: control characters escaped. -/
def clip (s : String) : String :=
  let e := s.replace "\\" "\\\\" |>.replace "\n" "\\n" |>.replace "\r" "\\r" |>.replace "\t" "\\t"
  if e.length > 200 then (e.take 200).toString ++ "..." else e

/-- Run `sh -c prog` (own process group) with `input` on stdin; stdout, or an error text.
Killed after 10 s. -/
def runProg (prog : String) (input : String) : IO (Except String String) := do
  try
    let cfg : IO.Process.SpawnArgs := { cmd := "sh", args := #["-c", prog], setsid := true }
    let child ← IO.Process.spawn { cfg with stdin := .piped, stdout := .piped, stderr := .null }
    let (stdin, child) ← child.takeStdin
    let reader ← IO.asTask child.stdout.readToEnd
    try stdin.putStr input; stdin.flush catch _ => pure ()
    let t0 ← IO.monoMsNow
    let mut code : Option UInt32 := none
    while (← IO.monoMsNow) - t0 < 10000 && !(code.isSome && (← IO.hasFinished reader)) do
      if code.isNone then code ← child.tryWait
      IO.sleep 10
    match code, (← IO.hasFinished reader) with
    | some c, true =>
      let out ← IO.ofExcept reader.get
      return if c == 0 then .ok out else .error s!"exit {c}: {out}"
    | _, _ =>
      discard <| IO.Process.output { cmd := "sh", args := #["-c", s!"kill -9 -- -{child.pid}"] }
      return .error "timeout (10 s)"
  catch e => return .error s!"crash: {e}"

#guard jeq (json% {"a": 1, "b": [1, 2]}) (json% {"b": [1, 2], "a": 1.0})
#guard !jeq (json% {"a": 1}) (json% {"a": 2})
#guard !jeq (json% {"a": 1}) (json% {"a": 1, "b": null})
#guard !jeq (json% [1, 2]) (json% [2, 1])
#guard clip "a\nb\tc" == "a\\nb\\tc"
#guard (clip (String.ofList (List.replicate 300 'x'))).length == 203

end LeanSpec.Core
