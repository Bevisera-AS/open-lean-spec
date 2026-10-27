module

public import LeanSpec.Validated
public import LeanSpec.Codec.Applicative
public meta import LeanSpec.Codec.Applicative
public meta import LeanUtil

namespace LeanSpec

open LeanSpec.Codec

public section

/-- Shared non-blank text check, re-exported for skill callers. -/
public def nonemptyText : String → Bool := LeanUtil.nonemptyText

/-- Dotted skill id. Absolute paths and directory separators are refused. -/
public def safeProcessSkillId (s : String) : Bool := validProcessSkillId s

/-! Untrusted skill wire representation. Validation is required before domain use. -/
namespace Raw

public structure ProcessSkill where
  id : String
  oneLiner : String
  purpose : String
  rules : Array String
  antipatterns : Array String := #[]
  requires : Array String := #[]
  deriving Repr, BEq

end Raw

/-- Workflow / meta skill. Lean is the instruction; this library does not emit SKILL.md. -/
public structure ProcessSkill where
  id : ProcessSkillId
  oneLiner : NonBlank
  purpose : NonBlank
  rules : NonEmptyArray NonBlank
  antipatterns : Array NonBlank := #[]
  requires : Array ProcessSkillId := #[]  -- first-class dependency edges (ids of required skills)
  deriving Repr, BEq

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def ProcessSkill.wellFormed (s : ProcessSkill) : Bool :=
  decide (ValidProcessSkillId s.id.value) &&
    LeanUtil.nonemptyText s.oneLiner.value &&
    LeanUtil.nonemptyText s.purpose.value &&
    decide (0 < s.rules.items.size) &&
    s.rules.toArray.all (fun r => LeanUtil.nonemptyText r.value)

/-- Every domain `ProcessSkill` satisfies the compatibility well-formedness predicate. -/
public theorem ProcessSkill.wellFormed_eq_true (s : ProcessSkill) :
    s.wellFormed = true := by
  simp only [ProcessSkill.wellFormed]
  rw [decide_eq_true s.id.property, s.oneLiner.property, s.purpose.property,
      decide_eq_true s.rules.property]
  simp [show ∀ r : NonBlank, LeanUtil.nonemptyText r.value = true from fun r => r.property]

/-- Projection to the untrusted wire representation. -/
public def ProcessSkill.toRaw (s : ProcessSkill) : Raw.ProcessSkill := {
  id := s.id.value
  oneLiner := s.oneLiner.value
  purpose := s.purpose.value
  rules := s.rules.items.map (·.value)
  antipatterns := s.antipatterns.map (·.value)
  requires := s.requires.map (·.value)
}

namespace Raw.ProcessSkill

/-- The `ProcessSkill` codec, composed from the generic algebra: a product of
`procId`, two `nonBlank`s, a `nonEmpty nonBlank` (rules) and a `list nonBlank`
(antipatterns). `encode` is definitionally `toRaw`. -/
public def codec : Codec Raw.ProcessSkill LeanSpec.ProcessSkill :=
  comap
    (imap
      (prod (label "id" procId) (prod (label "oneLiner" nonBlank) (prod (label "purpose" nonBlank)
        (prod (label "rules" (nonEmpty nonBlank))
          (prod (label "antipatterns" (list nonBlank)) (label "requires" (list procId)))))))
      (fun t => ({ id := t.1, oneLiner := t.2.1, purpose := t.2.2.1,
                   rules := t.2.2.2.1, antipatterns := t.2.2.2.2.1,
                   requires := t.2.2.2.2.2 } : LeanSpec.ProcessSkill))
      (fun s => (s.id, s.oneLiner, s.purpose, s.rules, s.antipatterns, s.requires))
      (fun _ => rfl) (fun _ => rfl))
    (fun raw => (raw.id, raw.oneLiner, raw.purpose, raw.rules, raw.antipatterns, raw.requires))
    (fun t => ({ id := t.1, oneLiner := t.2.1, purpose := t.2.2.1,
                 rules := t.2.2.2.1, antipatterns := t.2.2.2.2.1,
                 requires := t.2.2.2.2.2 } : Raw.ProcessSkill))
    (fun _ => rfl) (fun _ => rfl)

/-- Total validation from the untrusted wire DTO into the proof-carrying domain type. -/
public def validate (path : String) (skill : Raw.ProcessSkill) :
    Except ValidationError LeanSpec.ProcessSkill :=
  codec.decode path skill

/-- Successful validation projects back to the raw process skill. -/
public theorem validate_sound
    {path : String} {raw : Raw.ProcessSkill} {skill : LeanSpec.ProcessSkill}
    (h : raw.validate path = .ok skill) :
    skill.toRaw = raw := by
  have henc : codec.encode skill = skill.toRaw := rfl
  rw [← henc]; exact codec.sound h

/-- A domain process skill validates back to itself. -/
public theorem validate_complete (skill : LeanSpec.ProcessSkill) (path : String) :
    skill.toRaw.validate path = .ok skill := by
  have henc : codec.encode skill = skill.toRaw := rfl
  show codec.decode path skill.toRaw = .ok skill
  rw [← henc]; exact codec.complete skill

end Raw.ProcessSkill

public def joinSep : String → List String → String := LeanUtil.joinSep

public def duplicateIds (ids : Array String) : Array String :=
  let rec go (seen dups : Array String) : List String → Array String
    | [] => dups
    | id :: rest =>
        if seen.contains id then
          go seen (if dups.contains id then dups else dups.push id) rest
        else
          go (seen.push id) dups rest
  go #[] #[] ids.toList

end

end LeanSpec
