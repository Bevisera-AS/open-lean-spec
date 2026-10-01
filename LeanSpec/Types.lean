module

public import LeanSpec.Validated
public import LeanSpec.Codec.Applicative
public meta import LeanSpec.Codec.Applicative
public meta import LeanUtil

namespace LeanSpec

open LeanSpec.Codec

public section

/-- RFC 2119-style strength. `should` is non-normative for archive gates. -/
public inductive Strength where
  | shall
  | must
  | should
  deriving Repr, BEq, DecidableEq

public def nonemptyText : String → Bool := LeanUtil.nonemptyText

/-! Untrusted wire representation. Validation is required before domain use. -/
namespace Raw

public inductive CheckStatus where
  | executable
  | deferred (reason : String)
  deriving Repr, BEq, DecidableEq

public structure Scenario where
  name : String
  given? : Option String := none
  whenText : String
  thenText : String
  check : CheckStatus
  deriving Repr, BEq

public structure Requirement where
  id : String
  shall : String
  strength : Strength := .shall
  scenarios : Array Scenario
  deriving Repr, BEq

end Raw

/-- `.executable` is a claim that a named checker (`#guard` or test) exists.
It is not that checker's kernel derivation. A verification statement treats it
as an open obligation unless the requirement's design names a kernel theorem.
Theme evidence is `LeanSpec.Demo.Theme.toggleDarkCheck_of_light`. A deferred
reason is non-blank by construction. -/
public inductive CheckStatus where
  | executable
  | deferred (reason : NonBlank)
  deriving Repr, BEq, DecidableEq

public def CheckStatus.wellFormed : CheckStatus → Bool
  | .executable => true
  | .deferred reason => nonemptyText reason.value

public theorem CheckStatus.wellFormed_eq_true (check : CheckStatus) :
    check.wellFormed = true := by
  cases check with
  | executable => rfl
  | deferred reason => exact reason.property

/-- Projection to the untrusted wire representation. -/
public def CheckStatus.toRaw : CheckStatus → Raw.CheckStatus
  | .executable => .executable
  | .deferred reason => .deferred reason.value

public structure Scenario where
  name : NonBlank
  given? : Option NonBlank := none
  whenText : NonBlank
  thenText : NonBlank
  check : CheckStatus
  deriving Repr, BEq, DecidableEq

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def Scenario.wellFormed (s : Scenario) : Bool :=
  nonemptyText s.name.value &&
    (match s.given? with
     | none => true
     | some given => nonemptyText given.value) &&
    nonemptyText s.whenText.value &&
    nonemptyText s.thenText.value &&
    s.check.wellFormed

/-- Every domain `Scenario` satisfies the compatibility well-formedness predicate. -/
public theorem Scenario.wellFormed_eq_true (scenario : Scenario) :
    scenario.wellFormed = true := by
  cases scenario with
  | mk name given? whenText thenText check =>
    cases given? with
    | none =>
      simp [Scenario.wellFormed, CheckStatus.wellFormed_eq_true]
      exact ⟨⟨name.property, whenText.property⟩, thenText.property⟩
    | some given =>
      simp [Scenario.wellFormed, CheckStatus.wellFormed_eq_true]
      exact ⟨⟨⟨name.property, given.property⟩, whenText.property⟩, thenText.property⟩

/-- Projection to the untrusted wire representation. -/
public def Scenario.toRaw (s : Scenario) : Raw.Scenario := {
  name := s.name.value
  given? := s.given?.map (·.value)
  whenText := s.whenText.value
  thenText := s.thenText.value
  check := s.check.toRaw
}

namespace Raw.CheckStatus

/-- The `CheckStatus` codec (a sum type, so hand-written rather than a product
composition): `encode` is `toRaw`, `decode` validates a deferred reason. Used as a
field codec by `Scenario`. -/
@[expose] public def codec : Codec Raw.CheckStatus LeanSpec.CheckStatus where
  decode p raw :=
    match raw with
    | .executable => .ok .executable
    | .deferred reason =>
      match NonBlank.parse s!"{p}.reason" reason with
      | .error e => .error e
      | .ok parsed => .ok (.deferred parsed)
  encode c := c.toRaw
  sound := by
    intro p raw d h
    cases raw with
    | executable => cases h; rfl
    | deferred reason =>
      replace h : (match NonBlank.parse s!"{p}.reason" reason with
        | Except.error e => Except.error e
        | Except.ok parsed => Except.ok (LeanSpec.CheckStatus.deferred parsed)) = Except.ok d := h
      split at h
      · contradiction
      · next parsed hParse =>
        cases h
        have ⟨hVal, _⟩ := NonBlank.parse_sound hParse
        simp [CheckStatus.toRaw, hVal]
  complete := by
    intro p c
    cases c with
    | executable => rfl
    | deferred r =>
      show (match NonBlank.parse s!"{p}.reason" r.value with
            | Except.error e => Except.error e
            | Except.ok parsed => Except.ok (LeanSpec.CheckStatus.deferred parsed)) = Except.ok (.deferred r)
      rw [NonBlank.parse_complete]

/-- Validate a raw check status, rejecting blank deferred reasons. -/
public def validate (path : String) (raw : Raw.CheckStatus) :
    Except ValidationError LeanSpec.CheckStatus :=
  codec.decode path raw

/-- Successful validation projects back to the raw check status. -/
public theorem validate_sound
    {path : String} {raw : Raw.CheckStatus} {check : LeanSpec.CheckStatus}
    (h : raw.validate path = .ok check) :
    check.toRaw = raw :=
  codec.sound h

/-- A domain check status validates back to itself. -/
public theorem validate_complete (check : LeanSpec.CheckStatus) (path : String) :
    check.toRaw.validate path = .ok check :=
  codec.complete check

end Raw.CheckStatus

namespace Raw.Scenario

/-- The `Scenario` codec: a product of `nonBlank` (name/when/then), `optional
nonBlank` (given?), and the `Raw.CheckStatus.codec` field codec (check). `encode` is
definitionally `toRaw`. -/
public def codec : Codec Raw.Scenario LeanSpec.Scenario :=
  comap
    (imap
      (prod (label "name" nonBlank) (prod (label "given" (optional nonBlank))
        (prod (label "when" nonBlank) (prod (label "then" nonBlank) (label "check" Raw.CheckStatus.codec)))))
      (fun t => ({ name := t.1, given? := t.2.1, whenText := t.2.2.1,
                   thenText := t.2.2.2.1, check := t.2.2.2.2 } : LeanSpec.Scenario))
      (fun s => (s.name, s.given?, s.whenText, s.thenText, s.check))
      (fun _ => rfl) (fun _ => rfl))
    (fun raw => (raw.name, raw.given?, raw.whenText, raw.thenText, raw.check))
    (fun t => ({ name := t.1, given? := t.2.1, whenText := t.2.2.1,
                 thenText := t.2.2.2.1, check := t.2.2.2.2 } : Raw.Scenario))
    (fun _ => rfl) (fun _ => rfl)

/-- The codec's `encode` is `toRaw` (needs a case on `given?`, so it is a lemma
rather than definitional). Exposed so nested codecs (`Requirement`) can `funext` it. -/
public theorem encode_eq (scenario : LeanSpec.Scenario) : codec.encode scenario = scenario.toRaw := by
  obtain ⟨n, g, w, t, c⟩ := scenario; cases g <;> rfl

/-- Total validation from the untrusted wire DTO into the proof-carrying domain type. -/
public def validate (path : String) (scenario : Raw.Scenario) :
    Except ValidationError LeanSpec.Scenario :=
  codec.decode path scenario

/-- Successful validation projects back to the raw scenario. -/
public theorem validate_sound
    {path : String} {raw : Raw.Scenario} {scenario : LeanSpec.Scenario}
    (h : raw.validate path = .ok scenario) : scenario.toRaw = raw := by
  rw [← encode_eq scenario]; exact codec.sound h

/-- A domain scenario validates back to itself. -/
public theorem validate_complete (scenario : LeanSpec.Scenario) (path : String) :
    scenario.toRaw.validate path = .ok scenario := by
  show codec.decode path scenario.toRaw = .ok scenario
  rw [← encode_eq scenario]; exact codec.complete scenario

end Raw.Scenario

public structure Requirement where
  id : RequirementId
  shall : NonBlank
  strength : Strength := .shall
  scenarios : NonEmptyArray Scenario
  deriving Repr, BEq

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def Requirement.wellFormed (r : Requirement) : Bool :=
  decide (ValidRequirementId r.id.value) &&
    nonemptyText r.shall.value &&
    decide (0 < r.scenarios.items.size) &&
    r.scenarios.toArray.all Scenario.wellFormed

/-- Every domain `Requirement` satisfies the compatibility well-formedness predicate. -/
public theorem Requirement.wellFormed_eq_true (r : Requirement) :
    r.wellFormed = true := by
  unfold Requirement.wellFormed nonemptyText
  rw [decide_eq_true r.id.property, r.shall.property, decide_eq_true r.scenarios.property]
  simp [Scenario.wellFormed_eq_true]

/-- Projection to the untrusted wire representation. -/
public def Requirement.toRaw (r : Requirement) : Raw.Requirement := {
  id := r.id.value
  shall := r.shall.value
  strength := r.strength
  scenarios := r.scenarios.items.map Scenario.toRaw
}

public def Requirement.hasDeferredChecks (r : Requirement) : Bool :=
  r.scenarios.toArray.any fun s =>
    match s.check with
    | .deferred _ => true
    | .executable => false

namespace Raw.Requirement

/-- The `Requirement` codec: a product of `reqId`, `nonBlank`, `passthrough`
(strength), and `nonEmpty Raw.Scenario.codec` (scenarios — the nested scenario
codec). -/
public def codec : Codec Raw.Requirement LeanSpec.Requirement :=
  comap
    (imap
      (prod (label "id" reqId) (prod (label "shall" nonBlank)
        (prod passthrough (label "scenarios" (nonEmpty Raw.Scenario.codec)))))
      (fun t => ({ id := t.1, shall := t.2.1, strength := t.2.2.1, scenarios := t.2.2.2 } : LeanSpec.Requirement))
      (fun r => (r.id, r.shall, r.strength, r.scenarios))
      (fun _ => rfl) (fun _ => rfl))
    (fun raw => (raw.id, raw.shall, raw.strength, raw.scenarios))
    (fun t => ({ id := t.1, shall := t.2.1, strength := t.2.2.1, scenarios := t.2.2.2 } : Raw.Requirement))
    (fun _ => rfl) (fun _ => rfl)

/-- `encode` is `toRaw` — the scenario field needs `funext` of the nested scenario
`encode_eq`, so this is a lemma. Exposed for `Change`/`Delta`. -/
public theorem encode_eq (r : LeanSpec.Requirement) : codec.encode r = r.toRaw := by
  obtain ⟨id, shall, strength, scenarios⟩ := r
  show (⟨id.value, shall.value, strength, scenarios.items.map Raw.Scenario.codec.encode⟩ : Raw.Requirement)
       = ⟨id.value, shall.value, strength, scenarios.items.map Scenario.toRaw⟩
  rw [funext Raw.Scenario.encode_eq]

/-- Total validation from the untrusted wire DTO into the proof-carrying domain type. -/
public def validate (path : String) (requirement : Raw.Requirement) :
    Except ValidationError LeanSpec.Requirement :=
  codec.decode path requirement

/-- Successful validation projects back to the raw requirement. -/
public theorem validate_sound
    {path : String} {raw : Raw.Requirement} {requirement : LeanSpec.Requirement}
    (h : raw.validate path = .ok requirement) : requirement.toRaw = raw := by
  rw [← encode_eq requirement]; exact codec.sound h

/-- A domain requirement validates back to itself. -/
public theorem validate_complete (requirement : LeanSpec.Requirement) (path : String) :
    requirement.toRaw.validate path = .ok requirement := by
  show codec.decode path requirement.toRaw = .ok requirement
  rw [← encode_eq requirement]; exact codec.complete requirement

end Raw.Requirement

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
