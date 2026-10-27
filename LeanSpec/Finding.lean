module

public import LeanUtil
public import LeanSpec.Validated
public import LeanSpec.Trace
public import LeanSpec.Reflection
public meta import LeanUtil
public meta import LeanSpec.Validated
public meta import LeanSpec.Trace
public meta import LeanSpec.Reflection

/-!
# Findings

A reviewer's finding: one defect in one run, relative to the ground truth. The
bench's audit (`bench/Findings.lean`) is a list of these, checked by
`lake env lean`. A finding becomes a `Reflection` with the run as provenance, so
the reflect phase can record it in the Wiki and the next round can be gated on it.
-/

namespace LeanSpec

public section

/-- What went wrong, relative to the ground-truth requirements. -/
public inductive FindingKind where
  /-- The agent's spec or examples contradict the task. -/
  | specDrift
  /-- The program contradicts the agent's own spec. -/
  | reprDrift
  /-- The program is wrong where the spec is silent or right. -/
  | bug
  /-- A requirement has no test, example or proof. -/
  | testGap
  /-- Works, but fragile: float money, a quadratic hot path, swallowed errors. -/
  | flaw
  deriving Repr, BEq, DecidableEq

public def FindingKind.text : FindingKind → String
  | .specDrift => "specDrift"
  | .reprDrift => "reprDrift"
  | .bug => "bug"
  | .testGap => "testGap"
  | .flaw => "flaw"

/-- Drift, bugs and gaps are ways runs go wrong; a flaw is a regularity worth reusing. -/
public def FindingKind.reflectionKind : FindingKind → ReflectionKind
  | .flaw => .pattern
  | _ => .failureMode

public structure Finding where
  /-- Run id, e.g. `lru-py-lean-haiku-s11`. -/
  run      : String
  /-- Ground-truth requirement id, or `-`. -/
  req      : String
  kind     : FindingKind
  /-- 1 cosmetic · 2 wrong on edge cases · 3 wrong on the main path. -/
  severity : Nat
  /-- `file:line`, a hidden case id, or where in the transcript. -/
  evidence : String
  note     : String
  deriving Repr, BEq

public def Finding.wellFormed (f : Finding) : Bool :=
  LeanUtil.nonemptyText f.run && LeanUtil.nonemptyText f.note &&
    decide (1 ≤ f.severity) && decide (f.severity ≤ 3)

/-- The finding as a reflection: the note is the learning, the run is the
provenance, the kind maps as `FindingKind.reflectionKind`. Fails on a blank run or
note, the same way the Wiki refuses fabricated provenance. -/
public def Finding.toReflection (f : Finding) : Except ValidationError Reflection := do
  let run ← RunId.parse "finding.run" f.run
  let learning ← NonBlank.parse "finding.note" f.note
  let id ← ReflectionId.parse "finding.id" s!"finding:{f.run}:{f.kind.text}:{f.evidence}"
  let derivedFrom ← NonEmptyArray.ofArray "finding.derivedFrom" #[run]
  pure { id, kind := f.kind.reflectionKind, learning, derivedFrom }

public def Finding.converts (f : Finding) : Bool :=
  match f.toReflection with
  | .ok _ => true
  | .error _ => false

private def sample : Finding :=
  ⟨"lru-py-lean-haiku-s11", "R1", .specDrift, 2, "SPEC.md:12", "invented an error case"⟩

#guard sample.wellFormed
#guard sample.converts
#guard !({ sample with note := " " }).converts
#guard !({ sample with run := "" }).converts
#guard !({ sample with severity := 0 }).wellFormed
#guard (match sample.toReflection with
  | .ok r => r.kind == .failureMode && r.derivedFrom.items.size == 1 &&
      r.derivedFrom.items.map (·.value) == #["lru-py-lean-haiku-s11"]
  | .error _ => false)
#guard (match ({ sample with kind := .flaw }).toReflection with
  | .ok r => r.kind == .pattern
  | .error _ => false)

end

end LeanSpec
