module

public import LeanSpec.Types
public import LeanSpec.Codec.Applicative
public meta import LeanSpec.Types
public meta import LeanSpec.Codec.Applicative

namespace LeanSpec

open LeanSpec.Codec

public section

/-! Untrusted skillset wire representation. Validation is required before domain use. -/
namespace Raw

public structure Skillset where
  id : String
  pasteToken : String
  mission : String
  roleSkill : String
  boot : Array String
  reads : Array String := #[]
  deriving Repr, BEq

end Raw

public abbrev RoleInBoot (roleSkill : ProcessSkillId) (boot : NonEmptyArray ProcessSkillId) : Prop :=
  boot.toArray.any (fun id => id == roleSkill) = true

public instance (roleSkill : ProcessSkillId) (boot : NonEmptyArray ProcessSkillId) :
    Decidable (RoleInBoot roleSkill boot) :=
  by
    change Decidable (boot.toArray.any (fun id => id == roleSkill) = true)
    infer_instance

/-- Agent boot plan. The mechanism belongs in this library; company roles do not.
Identity, mission, nonempty boot, and role-in-boot are by construction.
Catalog membership of those skills stays a graph check. -/
public structure Skillset where
  id : ProcessSkillId
  pasteToken : NonBlank
  mission : NonBlank
  roleSkill : ProcessSkillId
  boot : NonEmptyArray ProcessSkillId
  reads : Array NonBlank := #[]
  roleInBoot : RoleInBoot roleSkill boot
  deriving Repr

/-- Equality deliberately ignores proof terms; two skillsets compare by payload. -/
public instance : BEq Skillset where
  beq left right :=
    left.id == right.id &&
      left.pasteToken == right.pasteToken &&
      left.mission == right.mission &&
      left.roleSkill == right.roleSkill &&
      left.boot == right.boot &&
      left.reads == right.reads

public theorem Skillset.ext {left right : Skillset}
    (hId : left.id = right.id) (hTok : left.pasteToken = right.pasteToken)
    (hMission : left.mission = right.mission) (hRole : left.roleSkill = right.roleSkill)
    (hBoot : left.boot = right.boot) (hReads : left.reads = right.reads) :
    left = right := by
  cases left with
  | mk id pasteToken mission roleSkill boot reads roleInBoot =>
    cases right with
    | mk id' pasteToken' mission' roleSkill' boot' reads' roleInBoot' =>
      cases hId
      cases hTok
      cases hMission
      cases hRole
      cases hBoot
      cases hReads
      rfl

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def Skillset.wellFormed (ss : Skillset) : Bool :=
  decide (ValidProcessSkillId ss.id.value) &&
    LeanUtil.nonemptyText ss.pasteToken.value &&
    LeanUtil.nonemptyText ss.mission.value &&
    decide (ValidProcessSkillId ss.roleSkill.value) &&
    decide (0 < ss.boot.items.size) &&
    ss.boot.toArray.all (fun id => validProcessSkillId id.value) &&
    ss.boot.toArray.any (fun id => id == ss.roleSkill)

/-- Every domain `Skillset` satisfies the compatibility well-formedness predicate. -/
public theorem Skillset.wellFormed_eq_true (ss : Skillset) : ss.wellFormed = true := by
  simp only [Skillset.wellFormed]
  rw [decide_eq_true ss.id.property, ss.pasteToken.property, ss.mission.property,
      decide_eq_true ss.roleSkill.property, decide_eq_true ss.boot.property, ss.roleInBoot]
  simp [show ∀ id : ProcessSkillId, validProcessSkillId id.value = true from fun id => id.property]

/-- Projection to the untrusted wire representation. -/
public def Skillset.toRaw (ss : Skillset) : Raw.Skillset := {
  id := ss.id.value
  pasteToken := ss.pasteToken.value
  mission := ss.mission.value
  roleSkill := ss.roleSkill.value
  boot := ss.boot.items.map (·.value)
  reads := ss.reads.map (·.value)
}

namespace Raw.Skillset

/-- The `Skillset` codec: a product of the field codecs, adapted to `Raw.Skillset`
(`comap`) and refined by the `roleInBoot` constraint (`refine`). `encode` is
definitionally `toRaw`. -/
public def codec : Codec Raw.Skillset LeanSpec.Skillset :=
  refine
    (comap
      (prod (label "id" procId) (prod (label "pasteToken" nonBlank) (prod (label "mission" nonBlank)
        (prod (label "roleSkill" procId) (prod (label "boot" (nonEmpty procId)) (label "reads" (list nonBlank)))))))
      (fun raw => (raw.id, raw.pasteToken, raw.mission, raw.roleSkill, raw.boot, raw.reads))
      (fun t => ({ id := t.1, pasteToken := t.2.1, mission := t.2.2.1, roleSkill := t.2.2.2.1,
                   boot := t.2.2.2.2.1, reads := t.2.2.2.2.2 } : Raw.Skillset))
      (fun _ => rfl) (fun _ => rfl))
    (fun d => decide (RoleInBoot d.2.2.2.1 d.2.2.2.2.1))
    (fun p raw => { path := s!"{p}.roleSkill", issue := .roleNotInBoot, rejected := some raw.roleSkill })
    (fun d h => ({ id := d.1, pasteToken := d.2.1, mission := d.2.2.1, roleSkill := d.2.2.2.1,
                   boot := d.2.2.2.2.1, reads := d.2.2.2.2.2,
                   roleInBoot := of_decide_eq_true h } : LeanSpec.Skillset))
    (fun s => (s.id, s.pasteToken, s.mission, s.roleSkill, s.boot, s.reads))
    (fun _ _ => rfl)
    (fun s => by simp only [decide_eq_true_eq]; exact s.roleInBoot)
    (fun _ => Skillset.ext rfl rfl rfl rfl rfl rfl)

/-- Total validation from the untrusted wire DTO into the proof-carrying domain type. -/
public def validate (path : String) (skillset : Raw.Skillset) :
    Except ValidationError LeanSpec.Skillset :=
  codec.decode path skillset

/-- Successful validation projects back to the raw skillset. -/
public theorem validate_sound
    {path : String} {raw : Raw.Skillset} {skillset : LeanSpec.Skillset}
    (h : raw.validate path = .ok skillset) : skillset.toRaw = raw := by
  have henc : codec.encode skillset = skillset.toRaw := rfl
  rw [← henc]; exact codec.sound h

/-- A domain skillset validates back to itself. -/
public theorem validate_complete (skillset : LeanSpec.Skillset) (path : String) :
    skillset.toRaw.validate path = .ok skillset := by
  have henc : codec.encode skillset = skillset.toRaw := rfl
  show codec.decode path skillset.toRaw = .ok skillset
  rw [← henc]; exact codec.complete skillset

end Raw.Skillset

public def skillIdRegistered (skills : Array ProcessSkill) (id : ProcessSkillId) : Bool :=
  skills.any (fun s => s.id == id)

public def bootRegistered (skills : Array ProcessSkill) (ss : Skillset) : Bool :=
  skillIdRegistered skills ss.roleSkill &&
    ss.boot.toArray.all (fun b => skillIdRegistered skills b)

public abbrev UniqueSkillIds (skills : Array ProcessSkill) : Prop :=
  (skills.map (·.id.value)).toList.Nodup

public abbrev UniqueSkillsetIds (skillsets : Array Skillset) : Prop :=
  (skillsets.map (·.id.value)).toList.Nodup

public abbrev UniquePasteTokens (skillsets : Array Skillset) : Prop :=
  (skillsets.map (·.pasteToken.value)).toList.Nodup

public abbrev AllBootsRegistered (skills : Array ProcessSkill) (skillsets : Array Skillset) : Prop :=
  skillsets.all (fun ss => bootRegistered skills ss) = true

/-! ### Dependency-graph invariants for `requires`

Every required id must resolve to a registered skill, and the `id → requires`
graph must be acyclic. Both are decidable; acyclicity is a fuelled Kahn-style
reduction (repeatedly drop nodes all of whose required ids have already been
dropped), acyclic iff every node is eventually removable within `skills.size`
rounds. -/

/-- Every `requires` id of every skill resolves to a registered skill. Modelled on
`AllBootsRegistered` (an `.all … = true` fold) so `Decidable` is `infer_instance`. -/
public abbrev AllRequiresRegistered (skills : Array ProcessSkill) : Prop :=
  skills.all (fun s => s.requires.all (fun r => skillIdRegistered skills r)) = true

/-- One Kahn round: drop from `remaining` every id all of whose required ids are
NOT in `remaining` (i.e. already removed or external). Returns the survivors. -/
private def kahnStep (skills : Array ProcessSkill) (remaining : Array String) : Array String :=
  remaining.filter (fun id =>
    match skills.find? (fun s => s.id.value == id) with
    | some s => s.requires.any (fun r => remaining.contains r.value)
    | none => false)

/-- Fuelled acyclicity: reduce the remaining set `fuel` times; acyclic iff it
empties. Fuel is seeded with `skills.size`, enough rounds to peel any DAG. -/
private def kahnReduce (skills : Array ProcessSkill) : Nat → Array String → Bool
  | 0, remaining => remaining.isEmpty
  | fuel + 1, remaining =>
    if remaining.isEmpty then true
    else
      let next := kahnStep skills remaining
      if next.size == remaining.size then false  -- no progress ⇒ a cycle remains
      else kahnReduce skills fuel next

/-- The `id → requires` graph over `skills` is acyclic. -/
public def requiresAcyclic (skills : Array ProcessSkill) : Bool :=
  kahnReduce skills skills.size (skills.map (·.id.value))

public abbrev RequiresAcyclic (skills : Array ProcessSkill) : Prop :=
  requiresAcyclic skills = true

public instance (skills : Array ProcessSkill) : Decidable (UniqueSkillIds skills) :=
  inferInstance

public instance (skillsets : Array Skillset) : Decidable (UniqueSkillsetIds skillsets) :=
  inferInstance

public instance (skillsets : Array Skillset) : Decidable (UniquePasteTokens skillsets) :=
  inferInstance

public instance (skills : Array ProcessSkill) (skillsets : Array Skillset) :
    Decidable (AllBootsRegistered skills skillsets) :=
  by
    change Decidable (skillsets.all (fun ss => bootRegistered skills ss) = true)
    infer_instance

public instance (skills : Array ProcessSkill) : Decidable (AllRequiresRegistered skills) :=
  by
    change Decidable (skills.all (fun s => s.requires.all (fun r => skillIdRegistered skills r)) = true)
    infer_instance

public instance (skills : Array ProcessSkill) : Decidable (RequiresAcyclic skills) :=
  by
    change Decidable (requiresAcyclic skills = true)
    infer_instance

/-- Catalog of process skills and skillsets. Duplicate ids and unregistered boot
skills cannot inhabit the type. -/
public structure Catalog where
  skills : Array ProcessSkill
  skillsets : Array Skillset
  uniqueSkills : UniqueSkillIds skills
  uniqueSkillsets : UniqueSkillsetIds skillsets
  uniqueTokens : UniquePasteTokens skillsets
  registered : AllBootsRegistered skills skillsets
  requiresRegistered : AllRequiresRegistered skills
  requiresAcyclic : RequiresAcyclic skills
  deriving Repr

/-- Equality deliberately ignores proof terms; two catalogs compare by payload. -/
public instance : BEq Catalog where
  beq left right := left.skills == right.skills && left.skillsets == right.skillsets

namespace Catalog

public theorem ext {left right : Catalog}
    (hs : left.skills = right.skills) (hss : left.skillsets = right.skillsets) :
    left = right := by
  cases left with
  | mk skills skillsets _ _ _ _ _ _ =>
    cases right with
    | mk skills' skillsets' _ _ _ _ _ _ =>
      cases hs
      cases hss
      rfl

private def firstDuplicate (ids : Array String) : Option String :=
  (duplicateIds ids)[0]?

private def firstUnregistered (skills : Array ProcessSkill) (skillsets : Array Skillset) :
    Option String :=
  let rec inBoot : List ProcessSkillId → Option String
    | [] => none
    | b :: rest =>
      if skillIdRegistered skills b then inBoot rest else some b.value
  let rec inSets : List Skillset → Option String
    | [] => none
    | ss :: rest =>
      if !skillIdRegistered skills ss.roleSkill then some ss.roleSkill.value
      else
        match inBoot ss.boot.toArray.toList with
        | some id => some id
        | none => inSets rest
  inSets skillsets.toList

/-- Validate an untrusted skills/skillsets pair. Duplicates and unregistered boots fail here. -/
public def of (path : String) (skills : Array ProcessSkill) (skillsets : Array Skillset) :
    Except ValidationError Catalog :=
  if h1 : UniqueSkillIds skills then
    if h2 : UniqueSkillsetIds skillsets then
      if h3 : UniquePasteTokens skillsets then
        if h4 : AllBootsRegistered skills skillsets then
          if h5 : AllRequiresRegistered skills then
            if h6 : RequiresAcyclic skills then
              .ok ⟨skills, skillsets, h1, h2, h3, h4, h5, h6⟩
            else
              .error {
                path := s!"{path}.skills.requires"
                issue := .requiresCycle
                rejected := none
              }
          else
            .error {
              path := s!"{path}.skills.requires"
              issue := .unregisteredSkill
              rejected := none
            }
        else
          .error {
            path := s!"{path}.skillsets"
            issue := .unregisteredSkill
            rejected := firstUnregistered skills skillsets
          }
      else
        .error {
          path := s!"{path}.skillsets.pasteToken"
          issue := .duplicateIds
          rejected := firstDuplicate (skillsets.map (·.pasteToken.value))
        }
    else
      .error {
        path := s!"{path}.skillsets"
        issue := .duplicateIds
        rejected := firstDuplicate (skillsets.map (·.id.value))
      }
  else
    .error {
      path := s!"{path}.skills"
      issue := .duplicateIds
      rejected := firstDuplicate (skills.map (·.id.value))
    }

/-- Successful construction preserves the arrays and the uniqueness/registration facts. -/
public theorem of_sound
    {path : String} {skills : Array ProcessSkill} {skillsets : Array Skillset}
    {catalog : Catalog}
    (h : of path skills skillsets = .ok catalog) :
    catalog.skills = skills ∧ catalog.skillsets = skillsets ∧
      UniqueSkillIds skills ∧ UniqueSkillsetIds skillsets ∧
      UniquePasteTokens skillsets ∧ AllBootsRegistered skills skillsets := by
  unfold of at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · split at h
            · cases h
              exact ⟨rfl, rfl, ‹UniqueSkillIds skills›, ‹UniqueSkillsetIds skillsets›,
                ‹UniquePasteTokens skillsets›, ‹AllBootsRegistered skills skillsets›⟩
            · contradiction
          · contradiction
        · contradiction
      · contradiction
    · contradiction
  · contradiction

/-- A catalog reconstructs from its skills and skillsets. -/
public theorem of_complete (catalog : Catalog) (path : String) :
    of path catalog.skills catalog.skillsets = .ok catalog := by
  unfold of
  split
  · next h1 =>
    split
    · next h2 =>
      split
      · next h3 =>
        split
        · next h4 =>
          split
          · next h5 =>
            split
            · next h6 =>
              exact congrArg Except.ok (Catalog.ext rfl rfl)
            · next h6 => exact absurd catalog.requiresAcyclic h6
          · next h5 => exact absurd catalog.requiresRegistered h5
        · next h4 => exact absurd catalog.registered h4
      · next h3 => exact absurd catalog.uniqueTokens h3
    · next h2 => exact absurd catalog.uniqueSkillsets h2
  · next h1 => exact absurd catalog.uniqueSkills h1

end Catalog

public def Catalog.findSkill? (c : Catalog) (id : String) : Option ProcessSkill :=
  c.skills.find? (fun s => s.id.value == id)

public def Catalog.findSkillset? (c : Catalog) (id : String) : Option Skillset :=
  c.skillsets.find? fun ss =>
    ss.id.value == id || ss.pasteToken.value == id

public def Catalog.hasSkill (c : Catalog) (id : String) : Bool :=
  (c.findSkill? id).isSome

/-- Inhabitants cannot be ill-formed. Duplicate and registration diagnostics
live on `Catalog.of` failures. -/
@[expose] public def Catalog.errors (_c : Catalog) : Array String := #[]

public theorem Catalog.errors_empty (c : Catalog) : c.errors = #[] :=
  rfl

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def Catalog.wellFormed (c : Catalog) : Bool :=
  decide (UniqueSkillIds c.skills) &&
    decide (UniqueSkillsetIds c.skillsets) &&
    decide (UniquePasteTokens c.skillsets) &&
    c.skills.all ProcessSkill.wellFormed &&
    c.skillsets.all Skillset.wellFormed &&
    decide (AllBootsRegistered c.skills c.skillsets) &&
    decide (AllRequiresRegistered c.skills) &&
    decide (RequiresAcyclic c.skills)

/-- Every domain `Catalog` satisfies the compatibility well-formedness predicate. -/
public theorem Catalog.wellFormed_eq_true (c : Catalog) : c.wellFormed = true := by
  simp only [Catalog.wellFormed]
  rw [decide_eq_true c.uniqueSkills, decide_eq_true c.uniqueSkillsets,
    decide_eq_true c.uniqueTokens, decide_eq_true c.registered,
    decide_eq_true c.requiresRegistered, decide_eq_true c.requiresAcyclic]
  simp [ProcessSkill.wellFormed_eq_true, Skillset.wellFormed_eq_true]

/-- Set equality of ids. Both directions; size alone is not enough. -/
public def sameIdSet (a b : Array String) : Bool :=
  a.size == b.size &&
    a.all (fun x => b.contains x) &&
    b.all (fun x => a.contains x)

#guard sameIdSet #["a", "b"] #["b", "a"]
#guard !sameIdSet #["a"] #["a", "b"]
#guard !sameIdSet #["a", "a"] #["a", "b"]

end

end LeanSpec
