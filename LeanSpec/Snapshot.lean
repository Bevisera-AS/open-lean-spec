module

public import LeanSpec.Change
public import LeanSpec.Design
public meta import LeanSpec.Change
public meta import LeanSpec.Design

namespace LeanSpec

public section

/-- Current accepted behaviour. Candidate changes stay outside until archive.
Requirement identifiers are unique by construction. -/
public abbrev UniqueRequirementIds (requirements : Array Requirement) : Prop :=
  (requirements.map (·.id.value)).toList.Nodup

public instance (requirements : Array Requirement) : Decidable (UniqueRequirementIds requirements) :=
  inferInstance

/-- One store: Requirement labels plus optional DesignUnits linked by id.
An empty `designs` array is valid (legacy snapshots). Do not grow a second store file. -/
public structure SpecSnapshot where
  requirements : Array Requirement
  uniqueIds : UniqueRequirementIds requirements
  designs : Array DesignUnit := #[]
  uniqueDesignIds : UniqueDesignIds designs := by native_decide
  designsLinked : DesignsLinked requirements designs := by native_decide
  deriving Repr

/-- Equality deliberately ignores proof terms; two snapshots compare by payload. -/
public instance : BEq SpecSnapshot where
  beq left right := left.requirements == right.requirements && left.designs == right.designs

namespace SpecSnapshot

public theorem ext {left right : SpecSnapshot}
    (hReq : left.requirements = right.requirements) (hDes : left.designs = right.designs) :
    left = right := by
  cases left with
  | mk leftReqs leftUnique leftDes leftUniqueDes leftLinked =>
    cases right with
    | mk rightReqs rightUnique rightDes rightUniqueDes rightLinked =>
      cases hReq
      cases hDes
      rfl

/-- Validate requirements and designs in one snapshot. Unlinked or duplicate design ids fail. -/
public def ofDesigned (path : String) (requirements : Array Requirement)
    (designs : Array DesignUnit) : Except ValidationError SpecSnapshot :=
  if h : UniqueRequirementIds requirements then
    if hD : UniqueDesignIds designs then
      if hL : DesignsLinked requirements designs then
        .ok ⟨requirements, h, designs, hD, hL⟩
      else
        let missing :=
          designs.filter fun d => !(requirements.map (·.id.value)).contains d.id.value
        .error {
          path := s!"{path}.designs"
          issue := .unlinkedDesign
          rejected := missing[0]?.map (·.id.value)
        }
    else
      let dups := duplicateIds (DesignUnit.ids designs)
      .error { path := s!"{path}.designs", issue := .duplicateIds, rejected := dups[0]? }
  else
    let dups := duplicateIds (requirements.map (·.id.value))
    .error { path, issue := .duplicateIds, rejected := dups[0]? }

/-- Validate an untrusted requirement list with no designs. Duplicate ids fail here. -/
public def of (path : String) (requirements : Array Requirement) :
    Except ValidationError SpecSnapshot :=
  ofDesigned path requirements #[]

/-- Successful construction preserves the requirement list and uniqueness. -/
public theorem of_sound
    {path : String} {requirements : Array Requirement} {snapshot : SpecSnapshot}
    (h : of path requirements = .ok snapshot) :
    snapshot.requirements = requirements ∧ UniqueRequirementIds requirements ∧
      snapshot.designs = (#[] : Array DesignUnit) := by
  unfold of ofDesigned at h
  split at h
  · split at h
    · split at h
      · cases h
        exact ⟨rfl, ‹UniqueRequirementIds requirements›, rfl⟩
      · contradiction
    · contradiction
  · contradiction

/-- Successful designed construction preserves both arrays. -/
public theorem ofDesigned_sound
    {path : String} {requirements : Array Requirement} {designs : Array DesignUnit}
    {snapshot : SpecSnapshot}
    (h : ofDesigned path requirements designs = .ok snapshot) :
    snapshot.requirements = requirements ∧ snapshot.designs = designs ∧
      UniqueRequirementIds requirements ∧ UniqueDesignIds designs ∧
      DesignsLinked requirements designs := by
  unfold ofDesigned at h
  split at h
  · split at h
    · split at h
      · cases h
        exact ⟨rfl, rfl, ‹UniqueRequirementIds requirements›, ‹UniqueDesignIds designs›,
          ‹DesignsLinked requirements designs›⟩
      · contradiction
    · contradiction
  · contradiction

/-- A snapshot reconstructs from its requirements and designs. -/
public theorem of_complete (snapshot : SpecSnapshot) (path : String) :
    ofDesigned path snapshot.requirements snapshot.designs = .ok snapshot := by
  unfold ofDesigned
  split
  · next h =>
    split
    · next hD =>
      split
      · next hL =>
        exact congrArg Except.ok (SpecSnapshot.ext rfl rfl)
      · next hL =>
        exact absurd snapshot.designsLinked hL
    · next hD =>
      exact absurd snapshot.uniqueDesignIds hD
  · next h =>
    exact absurd snapshot.uniqueIds h

public def empty : SpecSnapshot :=
  ⟨#[], by native_decide, #[], by native_decide, by native_decide⟩

end SpecSnapshot

public def SpecSnapshot.find? (s : SpecSnapshot) (id : String) : Option Requirement :=
  s.requirements.find? (·.id.value == id)

public def SpecSnapshot.findDesign? (s : SpecSnapshot) (id : String) : Option DesignUnit :=
  s.designs.find? (·.id.value == id)

public def SpecSnapshot.ids (s : SpecSnapshot) : Array String :=
  s.requirements.map (·.id.value)

public def SpecSnapshot.has (s : SpecSnapshot) (id : String) : Bool :=
  s.ids.contains id

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def SpecSnapshot.wellFormed (s : SpecSnapshot) : Bool :=
  decide (UniqueRequirementIds s.requirements) &&
    s.requirements.all Requirement.wellFormed &&
    decide (UniqueDesignIds s.designs) &&
    s.designs.all DesignUnit.wellFormed &&
    decide (DesignsLinked s.requirements s.designs)

/-- Every domain `SpecSnapshot` satisfies the compatibility well-formedness predicate. -/
public theorem SpecSnapshot.wellFormed_eq_true (s : SpecSnapshot) :
    s.wellFormed = true := by
  simp only [SpecSnapshot.wellFormed]
  rw [decide_eq_true s.uniqueIds, decide_eq_true s.uniqueDesignIds,
    decide_eq_true s.designsLinked]
  simp [Requirement.wellFormed_eq_true, DesignUnit.wellFormed_eq_true]

private theorem SpecSnapshot.not_has_not_mem {s : SpecSnapshot} {id : String}
    (h : s.has id = false) : id ∉ s.ids.toList := by
  simp [SpecSnapshot.has] at h
  exact fun hList => h (Array.mem_toList_iff.mp hList)

private theorem SpecSnapshot.mem_ids_of_mem {s : SpecSnapshot} {r : Requirement}
    (h : r ∈ s.requirements.toList) : r.id.value ∈ s.ids.toList := by
  simp [SpecSnapshot.ids]
  exact ⟨r, Array.mem_toList_iff.mp h, rfl⟩

/-- Pushing a fresh id preserves uniqueness. -/
private theorem SpecSnapshot.unique_push (s : SpecSnapshot) (r : Requirement)
    (hFresh : s.has r.id.value = false) :
    UniqueRequirementIds (s.requirements.push r) := by
  simp [UniqueRequirementIds, Array.map_push, Array.toList_push]
  rw [List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · simpa [SpecSnapshot.ids, UniqueRequirementIds] using s.uniqueIds
  · intro a ha b hb
    have hb' : b = r.id.value := by simp_all
    subst hb'
    intro hEq
    exact SpecSnapshot.not_has_not_mem hFresh (by simpa [SpecSnapshot.ids, hEq] using ha)

/-- Replacing a requirement in place does not change the id list. -/
private theorem SpecSnapshot.map_replace_ids (s : SpecSnapshot) (r : Requirement) :
    (s.requirements.map fun x => if x.id == r.id then r else x).map (·.id.value) =
      s.ids := by
  simp [SpecSnapshot.ids, Array.map_map]
  intro x _hx
  split
  · next hEq => simp [hEq]
  · rfl

/-- In-place replacement preserves uniqueness. -/
private theorem SpecSnapshot.unique_replace (s : SpecSnapshot) (r : Requirement) :
    UniqueRequirementIds (s.requirements.map fun x => if x.id == r.id then r else x) := by
  unfold UniqueRequirementIds
  rw [SpecSnapshot.map_replace_ids]
  simpa [SpecSnapshot.ids, UniqueRequirementIds] using s.uniqueIds

/-- Filtering preserves uniqueness. -/
private theorem SpecSnapshot.unique_filter (s : SpecSnapshot) (id : RequirementId) :
    UniqueRequirementIds (s.requirements.filter fun x => x.id != id) := by
  unfold UniqueRequirementIds
  simp [Array.toList_map]
  exact List.Nodup.sublist
    ((@List.filter_sublist Requirement (fun x => x.id != id)
        s.requirements.toList).map (fun x : Requirement => x.id.value))
    (by simpa [UniqueRequirementIds, Array.toList_map] using s.uniqueIds)

/-- Renaming a present id to a fresh id preserves uniqueness. -/
private theorem SpecSnapshot.unique_rename (s : SpecSnapshot) (move : Rename)
    (_hFrom : s.has move.frm.value = true) (hTo : s.has move.to.value = false) :
    UniqueRequirementIds
      (s.requirements.map fun x => if x.id == move.frm then { x with id := move.to } else x) := by
  have hToFresh := SpecSnapshot.not_has_not_mem hTo
  unfold UniqueRequirementIds
  simp [Array.toList_map]
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have hOrig : List.Pairwise (fun a b => a.id.value ≠ b.id.value) s.requirements.toList := by
    have h := s.uniqueIds
    simpa [UniqueRequirementIds, Array.toList_map, List.nodup_iff_pairwise_ne,
      List.pairwise_map] using h
  refine hOrig.imp_of_mem ?_
  intro a b ha hb hNe
  have haId := SpecSnapshot.mem_ids_of_mem ha
  have hbId := SpecSnapshot.mem_ids_of_mem hb
  intro hEq
  simp only [Function.comp_apply] at hEq
  split at hEq <;> split at hEq <;> rename_i haFrm hbFrm
  · exact hNe (by simp [haFrm, hbFrm])
  · exact hToFresh (hEq ▸ hbId)
  · exact hToFresh (hEq.symm ▸ haId)
  · exact hNe hEq

/-- Linking depends only on requirement ids, not on requirement bodies. -/
private theorem SpecSnapshot.designIdsLinked_of_id_list
    {reqs reqs' : Array Requirement} {designs : Array DesignUnit}
    (h : reqs.map (·.id.value) = reqs'.map (·.id.value)) :
    designIdsLinked reqs designs = designIdsLinked reqs' designs := by
  unfold designIdsLinked
  rw [h]

/-- Pushing a requirement keeps existing designs linked (ids are a superset). -/
private theorem SpecSnapshot.linked_push (s : SpecSnapshot) (r : Requirement) :
    DesignsLinked (s.requirements.push r) s.designs := by
  have h := s.designsLinked
  unfold DesignsLinked designIdsLinked at h ⊢
  rw [Array.map_push, Array.toList_push]
  refine List.all_eq_true.mpr ?_
  intro id hid
  have hOld := List.all_eq_true.mp h id hid
  simp only [List.contains_append, hOld, Bool.true_or]

/-- In-place replace keeps the requirement-id list, so designs stay linked. -/
private theorem SpecSnapshot.linked_replace (s : SpecSnapshot) (r : Requirement) :
    DesignsLinked (s.requirements.map fun x => if x.id == r.id then r else x) s.designs := by
  have hIds := SpecSnapshot.map_replace_ids s r
  have hEq :
      (s.requirements.map fun x => if x.id == r.id then r else x).map (·.id.value) =
        s.requirements.map (·.id.value) := by
    simpa [SpecSnapshot.ids] using hIds
  unfold DesignsLinked
  rw [SpecSnapshot.designIdsLinked_of_id_list hEq]
  exact s.designsLinked

/-- Syncing designs against current requirement ids is always linked. -/
private theorem SpecSnapshot.linked_sync (requirements : Array Requirement)
    (designs : Array DesignUnit) :
    DesignsLinked requirements (DesignUnit.sync requirements designs) := by
  unfold DesignsLinked designIdsLinked DesignUnit.sync DesignUnit.ids
  refine List.all_eq_true.mpr ?_
  intro id hid
  simp [Array.toList_map] at hid
  obtain ⟨d, ⟨_, hReq⟩, rfl⟩ := hid
  simpa [List.contains_iff_mem, Array.toList_map] using hReq

/-- Filtering designs preserves uniqueness of remaining ids. -/
private theorem SpecSnapshot.unique_sync (requirements : Array Requirement)
    (designs : Array DesignUnit) (h : UniqueDesignIds designs) :
    UniqueDesignIds (DesignUnit.sync requirements designs) := by
  unfold UniqueDesignIds DesignUnit.ids DesignUnit.sync
  have hNodup : (designs.map (·.id.value)).toList.Nodup := by
    simpa [UniqueDesignIds, DesignUnit.ids] using h
  have hSub :
      ((designs.filter fun d =>
          (requirements.map (·.id.value)).toList.contains d.id.value).map
        (·.id.value)).toList.Sublist
        (designs.map (·.id.value)).toList := by
    have hFilt :
        (designs.filter fun d =>
            (requirements.map (·.id.value)).toList.contains d.id.value).toList
          = designs.toList.filter fun d =>
              (requirements.map (·.id.value)).toList.contains d.id.value := by
      simp
    simpa [Array.toList_map, hFilt] using
      (List.filter_sublist (l := designs.toList)).map (fun d : DesignUnit => d.id.value)
  exact List.Nodup.sublist hSub hNodup

/-- Renaming a design id that matches `frm` preserves uniqueness when `to` is a fresh requirement id. -/
private theorem SpecSnapshot.unique_rename_designs (s : SpecSnapshot) (move : Rename)
    (hTo : s.has move.to.value = false) :
    UniqueDesignIds
      (s.designs.map fun d => if d.id == move.frm then { d with id := move.to } else d) := by
  have hToFresh := SpecSnapshot.not_has_not_mem hTo
  unfold UniqueDesignIds DesignUnit.ids
  simp [Array.toList_map]
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have hOrig : List.Pairwise (fun a b => a.id.value ≠ b.id.value) s.designs.toList := by
    have h := s.uniqueDesignIds
    simpa [UniqueDesignIds, DesignUnit.ids, Array.toList_map, List.nodup_iff_pairwise_ne,
      List.pairwise_map] using h
  refine hOrig.imp_of_mem ?_
  intro a b ha hb hNe
  intro hEq
  simp only [Function.comp_apply] at hEq
  have designIdInReqs (d : DesignUnit) (hd : d ∈ s.designs.toList) :
      d.id.value ∈ s.ids.toList := by
    have hAll := s.designsLinked
    unfold DesignsLinked designIdsLinked DesignUnit.ids at hAll
    have hid : d.id.value ∈ (s.designs.map (·.id.value)).toList := by
      simp [Array.toList_map]
      exact ⟨d, Array.mem_toList_iff.mp hd, rfl⟩
    have hCont := List.all_eq_true.mp hAll d.id.value (by simpa using hid)
    simpa [SpecSnapshot.ids, List.contains_iff_mem] using hCont
  split at hEq <;> split at hEq <;> rename_i haFrm hbFrm
  · exact hNe (by simp [haFrm, hbFrm])
  · exact hToFresh (hEq ▸ designIdInReqs b hb)
  · exact hToFresh (hEq.symm ▸ designIdInReqs a ha)
  · exact hNe hEq

/-- Caller-supplied archive decision. The CLI `--human` flag sets `accepted`.
This is not a verified identity, build receipt, or capability. -/
public inductive ArchiveDecision where
  | accepted
  | declined
  deriving Repr, BEq, DecidableEq

public inductive ArchiveError where
  | noHumanAccept
  | missingId (id : String)
  | duplicateId (id : String)
  deriving Repr, BEq

public def SpecSnapshot.applyDelta (s : SpecSnapshot) (d : Delta) : Except ArchiveError SpecSnapshot :=
  match d with
  | .added r =>
    if h : s.has r.id.value then
      .error (.duplicateId r.id.value)
    else
      .ok ⟨s.requirements.push r, SpecSnapshot.unique_push s r (eq_false_of_ne_true h),
        s.designs, s.uniqueDesignIds, SpecSnapshot.linked_push s r⟩
  | .modified r =>
    if _h : s.has r.id.value then
      .ok ⟨s.requirements.map fun x => if x.id == r.id then r else x,
        SpecSnapshot.unique_replace s r, s.designs, s.uniqueDesignIds,
        SpecSnapshot.linked_replace s r⟩
    else
      .error (.missingId r.id.value)
  | .removed id _reason _migration =>
    if _h : s.has id.value then
      let nextReqs := s.requirements.filter fun x => x.id != id
      let nextDesigns := DesignUnit.sync nextReqs s.designs
      .ok ⟨nextReqs, SpecSnapshot.unique_filter s id, nextDesigns,
        SpecSnapshot.unique_sync nextReqs s.designs s.uniqueDesignIds,
        SpecSnapshot.linked_sync nextReqs s.designs⟩
    else
      .error (.missingId id.value)
  | .renamed move =>
    if hFrom : s.has move.frm.value then
      if hTo : s.has move.to.value then
        .error (.duplicateId move.to.value)
      else
        let nextReqs :=
          s.requirements.map fun x =>
            if x.id == move.frm then { x with id := move.to } else x
        let renamedDesigns :=
          s.designs.map fun d =>
            if d.id == move.frm then { d with id := move.to } else d
        let nextDesigns := DesignUnit.sync nextReqs renamedDesigns
        .ok ⟨nextReqs, SpecSnapshot.unique_rename s move hFrom (eq_false_of_ne_true hTo),
          nextDesigns,
          SpecSnapshot.unique_sync nextReqs renamedDesigns
            (SpecSnapshot.unique_rename_designs s move (eq_false_of_ne_true hTo)),
          SpecSnapshot.linked_sync nextReqs renamedDesigns⟩
    else
      .error (.missingId move.frm.value)

/-- Successful add stores a fresh id at the end. -/
public theorem SpecSnapshot.applyDelta_added
    {s : SpecSnapshot} {r : Requirement} {next : SpecSnapshot}
    (h : s.applyDelta (.added r) = .ok next) :
    s.has r.id.value = false ∧ next.requirements = s.requirements.push r := by
  simp [SpecSnapshot.applyDelta] at h
  split at h
  · contradiction
  · next hNe =>
    cases h
    exact ⟨eq_false_of_ne_true hNe, rfl⟩

/-- Successful modify replaces the requirement with that id. -/
public theorem SpecSnapshot.applyDelta_modified
    {s : SpecSnapshot} {r : Requirement} {next : SpecSnapshot}
    (h : s.applyDelta (.modified r) = .ok next) :
    s.has r.id.value = true ∧
      next.requirements = s.requirements.map fun x => if x.id = r.id then r else x := by
  simp [SpecSnapshot.applyDelta] at h
  split at h
  · next hHas =>
    cases h
    exact ⟨hHas, rfl⟩
  · contradiction

/-- Successful remove drops that id. -/
public theorem SpecSnapshot.applyDelta_removed
    {s : SpecSnapshot} {id : RequirementId} {reason migration : NonBlank}
    {next : SpecSnapshot}
    (h : s.applyDelta (.removed id reason migration) = .ok next) :
    s.has id.value = true ∧
      next.requirements = s.requirements.filter fun x => x.id != id := by
  simp [SpecSnapshot.applyDelta] at h
  split at h
  · next hHas =>
    cases h
    exact ⟨hHas, rfl⟩
  · contradiction

/-- Successful rename moves `frm` to a fresh `to`. -/
public theorem SpecSnapshot.applyDelta_renamed
    {s : SpecSnapshot} {move : Rename} {next : SpecSnapshot}
    (h : s.applyDelta (.renamed move) = .ok next) :
    s.has move.frm.value = true ∧ s.has move.to.value = false ∧
      next.requirements =
        s.requirements.map fun x =>
          if x.id = move.frm then { x with id := move.to } else x := by
  simp [SpecSnapshot.applyDelta] at h
  split at h
  · next hFrom =>
    split at h
    · contradiction
    · next hTo =>
      cases h
      exact ⟨hFrom, eq_false_of_ne_true hTo, rfl⟩
  · contradiction

public def SpecSnapshot.applyDeltas (s : SpecSnapshot) (deltas : Array Delta) :
    Except ArchiveError SpecSnapshot :=
  deltas.foldl (init := Except.ok s) fun acc d =>
    match acc with
    | .error e => .error e
    | .ok snap => snap.applyDelta d

public def ArchiveError.pretty : ArchiveError → String
  | .noHumanAccept => "noHumanAccept"
  | .missingId id => s!"missingId {id}"
  | .duplicateId id => s!"duplicateId {id}"

/-- Dry-run a change against current spec. Does not write.
Partial modified and ill-formed domain changes cannot inhabit `Change`. -/
public inductive ChangeCheckError where
  | apply (err : ArchiveError)
  deriving Repr, BEq

public def ChangeCheckError.pretty : ChangeCheckError → String
  | .apply e => e.pretty

/-- A change that has already been shown to apply to `s`. The result snapshot is stored
so archive does not re-run applicability checks. -/
public structure ApplicableChange (s : SpecSnapshot) where
  change : Change
  result : SpecSnapshot
  applied : s.applyDeltas change.deltas.toArray = .ok result

/-- Equality deliberately ignores proof terms; two applicable changes compare by payload. -/
public instance {s : SpecSnapshot} : BEq (ApplicableChange s) where
  beq left right := left.change == right.change && left.result == right.result

namespace ApplicableChange

/-- Validate an untrusted `Change` against `s`. Missing/duplicate ids fail here, not at archive. -/
public def of (s : SpecSnapshot) (c : Change) : Except ChangeCheckError (ApplicableChange s) :=
  match h : s.applyDeltas c.deltas.toArray with
  | .error e => .error (.apply e)
  | .ok next => .ok ⟨c, next, h⟩

/-- Successful construction stores the applied snapshot. -/
public theorem of_sound
    {s : SpecSnapshot} {c : Change} {ac : ApplicableChange s}
    (_h : of s c = .ok ac) :
    s.applyDeltas ac.change.deltas.toArray = .ok ac.result :=
  ac.applied

/-- Construction stores the change that was checked. -/
public theorem of_change
    {s : SpecSnapshot} {c : Change} {ac : ApplicableChange s}
    (h : of s c = .ok ac) :
    ac.change = c := by
  unfold of at h
  split at h
  · contradiction
  · next _next _hApp =>
    cases h
    rfl

/-- The applied snapshot. Missing and duplicate ids were refused at `of`. -/
public def apply {s : SpecSnapshot} (c : ApplicableChange s) : SpecSnapshot :=
  c.result

/-- Governed merge. Only the human gate remains; applicability is in the type. -/
@[expose] public def archive {s : SpecSnapshot} (c : ApplicableChange s) (gate : ArchiveDecision) :
    Except ArchiveError SpecSnapshot :=
  match gate with
  | .declined => .error .noHumanAccept
  | .accepted => .ok (apply c)

public theorem archive_declined {s : SpecSnapshot} (c : ApplicableChange s) :
    archive c .declined = .error .noHumanAccept :=
  rfl

public theorem archive_accepted {s : SpecSnapshot} (c : ApplicableChange s) :
    archive c .accepted = .ok (apply c) :=
  rfl

end ApplicableChange

/-- Compatibility wrapper: validate, then archive. Prefer `ApplicableChange.of` at new call sites.
`declined` does not produce a snapshot; file IO is `archiveChangeFile`. -/
@[expose] public def SpecSnapshot.archive (s : SpecSnapshot) (c : Change) (gate : ArchiveDecision) :
    Except ArchiveError SpecSnapshot :=
  match gate with
  | .declined => .error .noHumanAccept
  | .accepted =>
    match ApplicableChange.of s c with
    | .error (.apply e) => .error e
    | .ok ac => .ok (ApplicableChange.apply ac)

/-- A declined gate never returns a snapshot. The file writer must not run. -/
public theorem SpecSnapshot.archive_declined (s : SpecSnapshot) (c : Change) :
    s.archive c .declined = .error .noHumanAccept :=
  rfl

public def SpecSnapshot.checkChange (s : SpecSnapshot) (c : Change) :
    Except ChangeCheckError Unit :=
  match ApplicableChange.of s c with
  | .error e => .error e
  | .ok _ => .ok ()

public def formatSnapshot (s : SpecSnapshot) : String :=
  joinSep "\n" (s.requirements.toList.map fun r =>
    let label := s!"{r.id.value}\t{r.shall.value}"
    match s.findDesign? r.id.value with
    | none => label
    | some d =>
      let ifaces := joinSep ", " (d.interfaces.toArray.toList.map (·.value))
      let tests := joinSep ", " (d.tests.toArray.toList.map (·.value))
      label ++ s!"\n  interfaces: {ifaces}\n  tests: {tests}")

/-- Attach or replace a DesignUnit for a requirement already in the snapshot. -/
public def SpecSnapshot.attachDesign (s : SpecSnapshot) (d : DesignUnit) :
    Except ValidationError SpecSnapshot :=
  if s.has d.id.value then
    let designs :=
      if s.designs.any (fun x => x.id == d.id) then
        s.designs.map fun x => if x.id == d.id then d else x
      else
        s.designs.push d
    SpecSnapshot.ofDesigned "snapshot" s.requirements designs
  else
    .error {
      path := "snapshot.designs"
      issue := .unlinkedDesign
      rejected := some d.id.value
    }

end

end LeanSpec
