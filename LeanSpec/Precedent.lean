module

public import LeanSpec.Snapshot
public import LeanSpec.Codec.Applicative
public meta import LeanSpec.Snapshot
public meta import LeanSpec.Codec.Applicative

/-!
# Precedents: the `supersedes` 2-morphism, recorded on a change

A `Delta` says *what* changed (added / modified / removed / renamed). A
`Supersedes` records *why one requirement defeats another* — the precedent link
modelled as a relation **between** determinations, not folded into the
determination itself.

`Supersedes` follows the house pattern exactly: a fail-closed domain type
(`source ≠ target` by construction), an untrusted `Raw` twin, a total `validate`,
and `validate_sound` / `validate_complete` round-trips — modelled on `Rename`.

Coherence is checked against the *live* snapshot, not baked in: a recorded
precedent is coherent only when its `target` still exists in the snapshot and its
`source` is a requirement this change introduces. That mirrors the GovernanceAgent
coherence check — evaluated on demand against current state.
-/

namespace LeanSpec

open LeanSpec.Codec

public section

/-! Untrusted wire representation. Validation is required before domain use. -/
namespace Raw

public structure Supersedes where
  source : String
  target : String
  rationale : String
  deriving Repr, BEq

end Raw

/-- A precedent link: `source` supersedes `target`, with a rationale. Source and
target are distinct requirement ids by construction (nothing supersedes itself). -/
public structure Supersedes where
  source : RequirementId
  target : RequirementId
  rationale : NonBlank
  property : source.value ≠ target.value
  deriving Repr

/-- Equality ignores the proof term; two precedents compare by their payload. -/
public instance : BEq Supersedes where
  beq l r := l.source == r.source && l.target == r.target && l.rationale == r.rationale

namespace Supersedes

public theorem ext {l r : Supersedes}
    (hs : l.source = r.source) (ht : l.target = r.target) (hr : l.rationale = r.rationale) :
    l = r := by
  cases l with
  | mk ls lt lr lp =>
    cases r with
    | mk rs rt rr rp =>
      cases hs; cases ht; cases hr; rfl

/-- Projection to the untrusted wire representation. -/
public def toRaw (rel : Supersedes) : Raw.Supersedes :=
  { source := rel.source.value, target := rel.target.value, rationale := rel.rationale.value }

/-- The `Supersedes` codec, composed from the generic algebra
(`LeanSpec/Codec/Applicative`): a product of two `reqId`s and a `nonBlank`, adapted
to `Raw.Supersedes` (`comap`) and refined by the `source ≠ target` constraint
(`refine`). Its `decode`/`encode`/round-trips are *inherited* — no per-field `split`
chain. `encode` is definitionally `toRaw`, so `validate_sound`/`_complete` are direct
corollaries. -/
public def codec : Codec Raw.Supersedes Supersedes :=
  refine
    (comap (prod (label "source" reqId) (prod (label "target" reqId) (label "rationale" nonBlank)))
      (fun r => (r.source, r.target, r.rationale))
      (fun t => { source := t.1, target := t.2.1, rationale := t.2.2 })
      (fun _ => rfl) (fun _ => rfl))
    (fun d => d.1.value != d.2.1.value)
    -- reuse `.sameRename`: a self-superseding precedent is as meaningless as a
    -- self-rename.
    (fun p r => { path := p, issue := .sameRename, rejected := some r.target })
    (fun d h => ⟨d.1, d.2.1, d.2.2, by simpa using h⟩)
    (fun s => (s.source, s.target, s.rationale))
    (fun _ _ => rfl)
    (fun s => by simpa using s.property)
    (fun _ => Supersedes.ext rfl rfl rfl)

/-- Total validation from the untrusted wire DTO into the fail-closed domain type. -/
public def validate (path : String) (raw : Raw.Supersedes) :
    Except ValidationError Supersedes :=
  codec.decode path raw

/-- Successful validation projects back to the raw precedent. -/
public theorem validate_sound
    {path : String} {raw : Raw.Supersedes} {rel : Supersedes}
    (h : validate path raw = .ok rel) : rel.toRaw = raw := by
  have henc : codec.encode rel = rel.toRaw := rfl
  rw [← henc]; exact codec.sound h

/-- A domain precedent validates back to itself. -/
public theorem validate_complete (rel : Supersedes) (path : String) :
    validate path rel.toRaw = .ok rel := by
  have henc : codec.encode rel = rel.toRaw := rfl
  show codec.decode path rel.toRaw = .ok rel
  rw [← henc]; exact codec.complete rel

end Supersedes

/-- Requirement ids this change introduces (added or modified). A precedent's
`source` must be one of these — you may only supersede *from* something you ship. -/
public def Change.introducedIds (c : Change) : Array String :=
  c.deltas.items.filterMap fun d =>
    match d with
    | .added r => some r.id.value
    | .modified r => some r.id.value
    | _ => none

/-- A precedent is coherent against a snapshot when its target still exists there
and its source is introduced by the change. Kept in terms of the `requirements`
projection so it evaluates without depending on unexposed helpers. -/
@[expose] public def Supersedes.coherentIn (s : SpecSnapshot) (introduced : Array String)
    (rel : Supersedes) : Bool :=
  (s.requirements.map (·.id.value)).contains rel.target.value &&
    introduced.contains rel.source.value

/-- A coherent precedent's target is among the snapshot's requirement ids. -/
public theorem Supersedes.coherentIn_target_present
    {s : SpecSnapshot} {introduced : Array String} {rel : Supersedes}
    (h : rel.coherentIn s introduced = true) :
    (s.requirements.map (·.id.value)).contains rel.target.value = true := by
  simp only [Supersedes.coherentIn] at h
  cases ht : (s.requirements.map (·.id.value)).contains rel.target.value with
  | true => rfl
  | false => rw [ht] at h; simp at h

/-- A change together with the precedents it records. -/
public structure PrecedentedChange where
  change : Change
  precedents : Array Supersedes := #[]
  deriving Repr

/-- Every recorded precedent is coherent against the snapshot being archived onto. -/
public def PrecedentedChange.coherentIn (s : SpecSnapshot) (pc : PrecedentedChange) : Bool :=
  pc.precedents.all (Supersedes.coherentIn s pc.change.introducedIds)

/-- Refusal reasons for a precedent-aware archive. `incoherent` is the new gate;
`archive` forwards the ordinary archive refusal (e.g. no human accept). -/
public inductive PrecedentArchiveError where
  | incoherent
  | archive (e : ArchiveError)
  deriving Repr, BEq

/-- Archive a change *with* its recorded precedents. Incoherent precedents are
refused before the human gate is even consulted; otherwise this delegates to the
ordinary `SpecSnapshot.archive`. Coherence is thus a precondition of a successful
precedent-archive — proven by `archiveWithPrecedents_ok_coherent`. -/
public def SpecSnapshot.archiveWithPrecedents
    (s : SpecSnapshot) (pc : PrecedentedChange) (gate : ArchiveDecision) :
    Except PrecedentArchiveError SpecSnapshot :=
  if pc.coherentIn s then
    match s.archive pc.change gate with
    | .ok s' => .ok s'
    | .error e => .error (.archive e)
  else
    .error .incoherent

/-- An incoherent precedent set is refused, whatever the human gate says. -/
public theorem archiveWithPrecedents_incoherent
    {s : SpecSnapshot} {pc : PrecedentedChange} {gate : ArchiveDecision}
    (h : pc.coherentIn s = false) :
    s.archiveWithPrecedents pc gate = .error .incoherent := by
  simp [SpecSnapshot.archiveWithPrecedents, h]

/-- A successful precedent-archive proves every recorded precedent was coherent. -/
public theorem archiveWithPrecedents_ok_coherent
    {s : SpecSnapshot} {pc : PrecedentedChange} {gate : ArchiveDecision} {s' : SpecSnapshot}
    (h : s.archiveWithPrecedents pc gate = .ok s') : pc.coherentIn s = true := by
  unfold SpecSnapshot.archiveWithPrecedents at h
  split at h
  · next hc => exact hc
  · simp at h

/-! ## Wire form: `PrecedentedChange` as an untrusted DTO -/

namespace Raw

public structure PrecedentedChange where
  change : Raw.Change
  precedents : Array Raw.Supersedes := #[]
  deriving Repr, BEq

end Raw

/-- Projection to the untrusted wire representation. -/
public def PrecedentedChange.toRaw (pc : PrecedentedChange) : Raw.PrecedentedChange :=
  { change := pc.change.toRaw, precedents := pc.precedents.map Supersedes.toRaw }

namespace Raw.PrecedentedChange

private def validatePrecedentsList (path : String) (i : Nat) :
    List Raw.Supersedes → Except ValidationError (List LeanSpec.Supersedes)
  | [] => .ok []
  | sup :: rest =>
    match Supersedes.validate s!"{path}[{i}]" sup with
    | .error e => .error e
    | .ok validated =>
      match validatePrecedentsList path (i + 1) rest with
      | .error e => .error e
      | .ok restValidated => .ok (validated :: restValidated)

private def validatePrecedents (path : String) (raws : Array Raw.Supersedes) :
    Except ValidationError (Array LeanSpec.Supersedes) :=
  match validatePrecedentsList path 0 raws.toList with
  | .error e => .error e
  | .ok xs => .ok xs.toArray

private theorem validatePrecedentsList_sound
    {path : String} (i : Nat) {raws : List Raw.Supersedes} {rels : List LeanSpec.Supersedes}
    (h : validatePrecedentsList path i raws = .ok rels) :
    rels.map Supersedes.toRaw = raws := by
  induction raws generalizing i rels with
  | nil => cases h; rfl
  | cons sup rest ih =>
    simp [validatePrecedentsList] at h
    split at h
    · contradiction
    · next validated hVal =>
      split at h
      · contradiction
      · next restValidated hRest =>
        cases h
        have hHead := Supersedes.validate_sound hVal
        have hTail := ih (i := i + 1) hRest
        simp [hHead, hTail]

private theorem validatePrecedentsList_complete
    (path : String) (i : Nat) (rels : List LeanSpec.Supersedes) :
    validatePrecedentsList path i (rels.map Supersedes.toRaw) = .ok rels := by
  induction rels generalizing i with
  | nil => rfl
  | cons rel rest ih =>
    simp [validatePrecedentsList, Supersedes.validate_complete, ih]

private theorem validatePrecedents_sound
    {path : String} {raws : Array Raw.Supersedes} {rels : Array LeanSpec.Supersedes}
    (h : validatePrecedents path raws = .ok rels) :
    rels.map Supersedes.toRaw = raws := by
  simp [validatePrecedents] at h
  split at h
  · contradiction
  · next xs hList =>
    cases h
    have hMapped := validatePrecedentsList_sound (i := 0) hList
    have hToList : (xs.toArray.map Supersedes.toRaw).toList = raws.toList := by
      simp [Array.toArray_toList, hMapped]
    exact Array.toList_inj.mp hToList

private theorem validatePrecedents_complete
    (path : String) (rels : Array LeanSpec.Supersedes) :
    validatePrecedents path (rels.map Supersedes.toRaw) = .ok rels := by
  simp [validatePrecedents, validatePrecedentsList_complete, Array.toList_map,
    Array.toArray_toList]

/-- Total validation from the untrusted wire DTO into the domain type. -/
public def validate (path : String) (pc : Raw.PrecedentedChange) :
    Except ValidationError LeanSpec.PrecedentedChange :=
  match Raw.Change.validate s!"{path}.change" pc.change with
  | .error e => .error e
  | .ok change =>
    match validatePrecedents s!"{path}.precedents" pc.precedents with
    | .error e => .error e
    | .ok precedents => .ok { change, precedents }

/-- Successful validation projects back to the raw precedented change. -/
public theorem validate_sound
    {path : String} {raw : Raw.PrecedentedChange} {pc : LeanSpec.PrecedentedChange}
    (h : validate path raw = .ok pc) : pc.toRaw = raw := by
  simp [validate] at h
  split at h
  · contradiction
  · next change hChange =>
    split at h
    · contradiction
    · next precedents hPrec =>
      cases h
      have hChangeVal := Raw.Change.validate_sound hChange
      have hPrecVal := validatePrecedents_sound hPrec
      simp [PrecedentedChange.toRaw, hChangeVal, hPrecVal]

/-- A domain precedented change validates back to itself. -/
public theorem validate_complete (pc : LeanSpec.PrecedentedChange) (path : String) :
    validate path pc.toRaw = .ok pc := by
  simp [validate, PrecedentedChange.toRaw, Raw.Change.validate_complete,
    validatePrecedents_complete]

end Raw.PrecedentedChange

end

/-! ## Worked examples (executable `#guard`s) -/

private def exScenario : Scenario :=
  { name := ⟨"shown", by native_decide⟩
    whenText := ⟨"the page loads", by native_decide⟩
    thenText := ⟨"the summary is displayed", by native_decide⟩
    check := .executable }

private def exReq (id : RequirementId) (shall : NonBlank) : Requirement :=
  { id, shall, scenarios := ⟨#[exScenario], by decide⟩ }

private def reqOverview : Requirement :=
  exReq ⟨"cap.overview", by native_decide⟩ ⟨"Show a summary dashboard", by native_decide⟩
private def reqDetail : Requirement :=
  exReq ⟨"cap.detail", by native_decide⟩ ⟨"Show a per-row detail table", by native_decide⟩

private def snap : SpecSnapshot :=
  ⟨#[reqOverview, reqDetail], by native_decide, #[], by native_decide, by native_decide⟩

-- A change that tightens the overview requirement (introduces `cap.overview`).
private def chg : Change :=
  { id := ⟨"tighten-overview", by native_decide⟩
    why := ⟨"Overview subsumes the standalone detail table", by native_decide⟩
    deltas := ⟨#[.modified reqOverview], by decide⟩ }

#guard chg.introducedIds == #["cap.overview"]

-- Coherent: overview (introduced here) supersedes detail (present in the snapshot).
private def supOk : Supersedes :=
  ⟨⟨"cap.overview", by native_decide⟩, ⟨"cap.detail", by native_decide⟩,
    ⟨"the dashboard replaces the detail table", by native_decide⟩, by native_decide⟩

#guard ({ change := chg, precedents := #[supOk] } : PrecedentedChange).coherentIn snap

-- Incoherent: target does not exist in the snapshot.
private def supMissingTarget : Supersedes :=
  ⟨⟨"cap.overview", by native_decide⟩, ⟨"cap.ghost", by native_decide⟩,
    ⟨"defeats a requirement that is not there", by native_decide⟩, by native_decide⟩

#guard !({ change := chg, precedents := #[supMissingTarget] } : PrecedentedChange).coherentIn snap

-- Incoherent: source is present but not introduced by this change.
private def supForeignSource : Supersedes :=
  ⟨⟨"cap.detail", by native_decide⟩, ⟨"cap.overview", by native_decide⟩,
    ⟨"source is not shipped by this change", by native_decide⟩, by native_decide⟩

#guard !({ change := chg, precedents := #[supForeignSource] } : PrecedentedChange).coherentIn snap

-- The archive gate refuses an incoherent precedent set (short-circuits before
-- the ordinary archive runs).
private def isIncoherent : Except PrecedentArchiveError SpecSnapshot → Bool
  | .error .incoherent => true
  | _ => false

#guard isIncoherent
  (snap.archiveWithPrecedents { change := chg, precedents := #[supMissingTarget] } .accepted)

end LeanSpec
