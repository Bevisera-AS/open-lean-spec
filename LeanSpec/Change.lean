module

public import LeanSpec.Types
public import LeanSpec.Codec.Applicative
public import LeanUtil
public meta import LeanSpec.Codec.Applicative

namespace LeanSpec

open LeanSpec.Codec

public section

/-! Untrusted wire representation. Validation is required before domain use. -/
namespace Raw

public inductive Delta where
  | added (r : Requirement)
  | modified (id : String) (r : Requirement)
  | removed (id : String) (reason : String) (migration : String)
  | renamed (frm to : String)
  deriving Repr, BEq

public structure Change where
  id : String
  why : String
  deltas : Array Delta
  deriving Repr, BEq

end Raw

/-- A rename whose source and target identifiers are distinct by construction. -/
public structure Rename where
  frm : RequirementId
  to : RequirementId
  property : frm.value ≠ to.value
  deriving Repr

/-- Equality deliberately ignores proof terms; two renames compare by identifiers. -/
public instance : BEq Rename where
  beq left right := left.frm == right.frm && left.to == right.to

namespace Rename

public theorem ext {left right : Rename}
    (hFrm : left.frm = right.frm) (hTo : left.to = right.to) : left = right := by
  cases left with
  | mk leftFrm leftTo leftProperty =>
    cases right with
    | mk rightFrm rightTo rightProperty =>
      cases hFrm
      cases hTo
      rfl

public def parse (path frm to : String) : Except ValidationError Rename :=
  match RequirementId.parse s!"{path}.from" frm with
  | .error e => .error e
  | .ok frmId =>
    match RequirementId.parse s!"{path}.to" to with
    | .error e => .error e
    | .ok toId =>
      if h : frmId.value ≠ toId.value then
        .ok ⟨frmId, toId, h⟩
      else
        .error { path, issue := .sameRename, rejected := some to }

/-- Successful parsing preserves the identifiers and their inequality. -/
public theorem parse_sound
    {path frm to : String} {move : Rename}
    (h : parse path frm to = .ok move) :
    move.frm.value = frm ∧ move.to.value = to ∧ frm ≠ to := by
  simp [parse] at h
  split at h
  · contradiction
  · next frmId hFrm =>
    split at h
    · contradiction
    · next toId hTo =>
      split at h
      · contradiction
      · next hNe =>
        cases h
        have ⟨hFrmVal, _⟩ := RequirementId.parse_sound hFrm
        have ⟨hToVal, _⟩ := RequirementId.parse_sound hTo
        refine ⟨hFrmVal, hToVal, ?_⟩
        simpa [hFrmVal, hToVal] using hNe

/-- A domain rename parses back to itself. -/
public theorem parse_complete (move : Rename) (path : String) :
    parse path move.frm.value move.to.value = .ok move := by
  simp [parse, RequirementId.parse_complete]
  rw [dif_neg move.property]

end Rename

/-- OpenSpec-shaped delta. `modified` is a full replacement; the wire `id` must match
`requirement.id` at the validation boundary. -/
public inductive Delta where
  | added (r : Requirement)
  | modified (r : Requirement)
  | removed (id : RequirementId) (reason : NonBlank) (migration : NonBlank)
  | renamed (move : Rename)
  deriving Repr, BEq

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def Delta.wellFormed : Delta → Bool
  | .added r => r.wellFormed
  | .modified r => r.wellFormed
  | .removed _ reason migration =>
      LeanUtil.nonemptyText reason.value && LeanUtil.nonemptyText migration.value
  | .renamed move => decide (move.frm.value ≠ move.to.value)

/-- Every domain `Delta` satisfies the compatibility well-formedness predicate. -/
public theorem Delta.wellFormed_eq_true (delta : Delta) : delta.wellFormed = true := by
  cases delta with
  | added r => exact Requirement.wellFormed_eq_true r
  | modified r => exact Requirement.wellFormed_eq_true r
  | removed _ reason migration =>
    simp only [Delta.wellFormed]
    rw [reason.property, migration.property]
    rfl
  | renamed move =>
    simp only [Delta.wellFormed]
    exact decide_eq_true move.property

/-- Projection to the untrusted wire representation. -/
public def Delta.toRaw : Delta → Raw.Delta
  | .added r => .added r.toRaw
  | .modified r => .modified r.id.value r.toRaw
  | .removed id reason migration => .removed id.value reason.value migration.value
  | .renamed move => .renamed move.frm.value move.to.value

public structure Change where
  id : NonBlank
  why : NonBlank
  deltas : NonEmptyArray Delta
  deriving Repr, BEq

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def Change.wellFormed (c : Change) : Bool :=
  LeanUtil.nonemptyText c.id.value &&
    LeanUtil.nonemptyText c.why.value &&
    decide (0 < c.deltas.items.size) &&
    c.deltas.toArray.all Delta.wellFormed

/-- Every domain `Change` satisfies the compatibility well-formedness predicate. -/
public theorem Change.wellFormed_eq_true (c : Change) : c.wellFormed = true := by
  simp only [Change.wellFormed]
  rw [c.id.property, c.why.property, decide_eq_true c.deltas.property]
  simp [Delta.wellFormed_eq_true]

/-- Projection to the untrusted wire representation. -/
public def Change.toRaw (c : Change) : Raw.Change := {
  id := c.id.value
  why := c.why.value
  deltas := c.deltas.items.map Delta.toRaw
}

/-- A modified delta that drops scenarios is the OpenSpec archive pitfall.
Domain `Requirement` cannot inhabit an empty scenario list, so this is always false. -/
public def Delta.isPartialModified : Delta → Bool
  | .modified r => r.scenarios.toArray.isEmpty
  | _ => false

/-- Domain deltas cannot be partial modifications. Empty scenarios fail at `Requirement`. -/
public theorem Delta.isPartialModified_eq_false (delta : Delta) :
    delta.isPartialModified = false := by
  cases delta with
  | added _ => rfl
  | modified r =>
    simpa [Delta.isPartialModified] using NonEmptyArray.toArray_not_isEmpty r.scenarios
  | removed _ _ _ => rfl
  | renamed _ => rfl

namespace Raw.Delta

/-- Total validation from the untrusted wire DTO into the proof-carrying domain type. -/
public def validate (path : String) : Raw.Delta → Except ValidationError LeanSpec.Delta
  | .added r =>
    match r.validate s!"{path}.requirement" with
    | .error e => .error e
    | .ok requirement => .ok (.added requirement)
  | .modified id r =>
    match RequirementId.parse s!"{path}.id" id with
    | .error e => .error e
    | .ok parsedId =>
      match r.validate s!"{path}.requirement" with
      | .error e => .error e
      | .ok requirement =>
        if parsedId == requirement.id then
          .ok (.modified requirement)
        else
          .error { path := s!"{path}.id", issue := .idMismatch, rejected := some id }
  | .removed id reason migration =>
    match RequirementId.parse s!"{path}.id" id with
    | .error e => .error e
    | .ok parsedId =>
      match NonBlank.parse s!"{path}.reason" reason with
      | .error e => .error e
      | .ok parsedReason =>
        match NonBlank.parse s!"{path}.migration" migration with
        | .error e => .error e
        | .ok parsedMigration =>
          .ok (.removed parsedId parsedReason parsedMigration)
  | .renamed frm to =>
    match Rename.parse path frm to with
    | .error e => .error e
    | .ok move => .ok (.renamed move)

/-- Successful validation projects back to the raw delta. -/
public theorem validate_sound
    {path : String} {raw : Raw.Delta} {delta : LeanSpec.Delta}
    (h : raw.validate path = .ok delta) :
    delta.toRaw = raw := by
  cases raw with
  | added r =>
    simp [validate] at h
    split at h
    · contradiction
    · next requirement hReq =>
      cases h
      have hReqVal := Raw.Requirement.validate_sound hReq
      simp [Delta.toRaw, hReqVal]
  | modified id r =>
    simp [validate] at h
    split at h
    · contradiction
    · next parsedId hId =>
      split at h
      · contradiction
      · next requirement hReq =>
        split at h
        · next hEq =>
          cases h
          have ⟨hIdVal, _⟩ := RequirementId.parse_sound hId
          have hReqVal := Raw.Requirement.validate_sound hReq
          cases hEq
          simp [Delta.toRaw, hReqVal, hIdVal]
        · contradiction
  | removed id reason migration =>
    simp [validate] at h
    split at h
    · contradiction
    · next parsedId hId =>
      split at h
      · contradiction
      · next parsedReason hReason =>
        split at h
        · contradiction
        · next parsedMigration hMigration =>
          cases h
          have ⟨hIdVal, _⟩ := RequirementId.parse_sound hId
          have ⟨hReasonVal, _⟩ := NonBlank.parse_sound hReason
          have ⟨hMigrationVal, _⟩ := NonBlank.parse_sound hMigration
          simp [Delta.toRaw, hIdVal, hReasonVal, hMigrationVal]
  | renamed frm to =>
    simp [validate] at h
    split at h
    · contradiction
    · next move hMove =>
      cases h
      have ⟨hFrm, hTo, _⟩ := Rename.parse_sound hMove
      simp [Delta.toRaw, hFrm, hTo]

/-- A domain delta validates back to itself. -/
public theorem validate_complete (delta : LeanSpec.Delta) (path : String) :
    delta.toRaw.validate path = .ok delta := by
  cases delta with
  | added r =>
    simp [Delta.toRaw, validate, Raw.Requirement.validate_complete]
  | modified r =>
    simp [Delta.toRaw, validate, RequirementId.parse_complete, Raw.Requirement.validate_complete]
  | removed id reason migration =>
    simp [Delta.toRaw, validate, RequirementId.parse_complete, NonBlank.parse_complete]
  | renamed move =>
    simp [Delta.toRaw, validate, Rename.parse_complete]

/-- `Delta` is a sum type (with a cross-field `modified` check), so its bespoke
validator stays. This wraps it as a `Codec` value so `Change` can compose it
(`nonEmpty codec`). -/
@[expose] public def codec : Codec Raw.Delta LeanSpec.Delta where
  decode := validate
  encode := LeanSpec.Delta.toRaw
  sound := fun h => validate_sound h
  complete := fun {_} d => validate_complete d _

end Raw.Delta

namespace Raw.Change

/-- The `Change` codec: a product of `nonBlank` (id/why) and `nonEmpty Raw.Delta.codec`
(deltas — the wrapped delta codec). `Raw.Delta.codec.encode` is definitionally
`Delta.toRaw`, so `encode` is definitionally `toRaw`. -/
public def codec : Codec Raw.Change LeanSpec.Change :=
  comap
    (imap
      (prod (label "id" nonBlank) (prod (label "why" nonBlank) (label "deltas" (nonEmpty Raw.Delta.codec))))
      (fun t => ({ id := t.1, why := t.2.1, deltas := t.2.2 } : LeanSpec.Change))
      (fun c => (c.id, c.why, c.deltas))
      (fun _ => rfl) (fun _ => rfl))
    (fun raw => (raw.id, raw.why, raw.deltas))
    (fun t => ({ id := t.1, why := t.2.1, deltas := t.2.2 } : Raw.Change))
    (fun _ => rfl) (fun _ => rfl)

/-- Total validation from the untrusted wire DTO into the proof-carrying domain type. -/
public def validate (path : String) (change : Raw.Change) :
    Except ValidationError LeanSpec.Change :=
  codec.decode path change

/-- Successful validation projects back to the raw change. -/
public theorem validate_sound
    {path : String} {raw : Raw.Change} {change : LeanSpec.Change}
    (h : raw.validate path = .ok change) : change.toRaw = raw := by
  have henc : codec.encode change = change.toRaw := rfl
  rw [← henc]; exact codec.sound h

/-- A domain change validates back to itself. -/
public theorem validate_complete (change : LeanSpec.Change) (path : String) :
    change.toRaw.validate path = .ok change := by
  have henc : codec.encode change = change.toRaw := rfl
  show codec.decode path change.toRaw = .ok change
  rw [← henc]; exact codec.complete change

end Raw.Change

end

end LeanSpec
