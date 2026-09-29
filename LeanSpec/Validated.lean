module

public import LeanUtil

namespace LeanSpec

public section

/-- The kind of failure produced while constructing a validated primitive. -/
public inductive ValidationIssue where
  | blank
  | invalidRequirementId
  | emptyArray
  | idMismatch
  | sameRename
  | invalidProcessSkillId
  | duplicateIds
  | roleNotInBoot
  | unregisteredSkill
  | unlinkedDesign
  | disallowedTarget
  | requiresCycle
  deriving Repr, BEq, DecidableEq

/-- A validation failure with a caller-supplied path and the rejected value when useful. -/
public structure ValidationError where
  path : String
  issue : ValidationIssue
  rejected : Option String := none
  deriving Repr, BEq

public def ValidationIssue.description : ValidationIssue → String
  | .blank => "must contain a non-whitespace character"
  | .invalidRequirementId => "must be a valid requirement identifier"
  | .emptyArray => "must contain at least one element"
  | .idMismatch => "modified id must match requirement id"
  | .sameRename => "rename from and to must differ"
  | .invalidProcessSkillId => "must be a valid process skill identifier"
  | .duplicateIds => "identifiers must be unique"
  | .roleNotInBoot => "roleSkill must appear in boot"
  | .unregisteredSkill => "skill is not registered in the catalog"
  | .unlinkedDesign => "design id must name a requirement in the same snapshot"
  | .disallowedTarget => "target language is not allowed for this surface"
  | .requiresCycle => "skill dependency graph must be acyclic"

public def ValidationError.pretty (error : ValidationError) : String :=
  let rejected := error.rejected.map (fun value => s!"; rejected {repr value}") |>.getD ""
  s!"{error.path}: {error.issue.description}{rejected}"

/-- Inversion for a successful `Except.bind`. Used to lift `parse_sound` through validators. -/
public theorem exceptBind_eq_ok
    {ε α β : Type _} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : Except.bind x f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Inversion for a successful `Except.map`. -/
public theorem exceptMap_eq_ok
    {ε α β : Type _} {x : Except ε α} {f : α → β} {b : β}
    (h : f <$> x = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  simp only [Functor.map] at h
  cases x with
  | error _ => simp [Except.map] at h
  | ok a =>
    simp [Except.map] at h
    exact ⟨a, rfl, h⟩

/-- A string containing at least one non-whitespace character. -/
public structure NonBlank where
  value : String
  property : LeanUtil.nonemptyText value = true
  deriving Repr

/-- Equality deliberately ignores proof terms; two validated strings compare by text. -/
public instance : BEq NonBlank where
  beq left right := left.value == right.value

namespace NonBlank

/-- Proof fields are irrelevant: equal underlying strings determine equal validated values. -/
public theorem ext {left right : NonBlank} (h : left.value = right.value) : left = right := by
  cases left with
  | mk leftValue leftProperty =>
    cases right with
    | mk rightValue rightProperty =>
      cases h
      rfl

public instance : LawfulBEq NonBlank where
  rfl {a} := BEq.refl a.value
  eq_of_beq h := ext (eq_of_beq h)

public instance : DecidableEq NonBlank := instDecidableEqOfLawfulBEq

/-- Validate untrusted text. `path` identifies the field for diagnostics. -/
public def parse (path value : String) : Except ValidationError NonBlank :=
  if h : LeanUtil.nonemptyText value = true then
    .ok ⟨value, h⟩
  else
    .error { path, issue := .blank, rejected := some value }

/-- Successful parsing preserves the input and establishes non-blankness. -/
public theorem parse_sound
    {path value : String} {result : NonBlank}
    (h : parse path value = .ok result) :
    result.value = value ∧ LeanUtil.nonemptyText value = true := by
  unfold parse at h
  split at h
  · cases h
    exact ⟨rfl, ‹LeanUtil.nonemptyText value = true›⟩
  · contradiction

/-- Parsing a validated value's payload recovers that value. -/
public theorem parse_complete {path : String} (result : NonBlank) :
    parse path result.value = .ok result := by
  unfold parse
  split
  · next h =>
    exact congrArg Except.ok (NonBlank.ext rfl)
  · next h =>
    exact absurd result.property h

end NonBlank

/-- ASCII letters are used so requirement IDs have a stable cross-platform grammar. -/
public def isAsciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

public def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- A requirement-ID segment starts with a letter and then uses letters, digits, `-`, or `_`. -/
public def validRequirementIdSegment : List Char → Bool
  | [] => false
  | first :: rest =>
      isAsciiLetter first &&
        rest.all fun c => isAsciiLetter c || isAsciiDigit c || c == '-' || c == '_'

/--
Requirement IDs are one or more nonempty dot-separated segments. Each segment starts with an
ASCII letter and continues with ASCII letters, digits, `-`, or `_`.
-/
public abbrev ValidRequirementId (value : String) : Prop :=
  (value.splitOn ".").all (fun segment => validRequirementIdSegment segment.toList) = true

public instance (value : String) : Decidable (ValidRequirementId value) :=
  by
    change Decidable (
      (value.splitOn ".").all (fun segment => validRequirementIdSegment segment.toList) = true)
    infer_instance

/-- A requirement identifier carrying evidence that it follows `ValidRequirementId`. -/
public structure RequirementId where
  value : String
  property : ValidRequirementId value
  deriving Repr

/-- Equality deliberately ignores proof terms; two identifiers compare by text. -/
public instance : BEq RequirementId where
  beq left right := left.value == right.value

namespace RequirementId

/-- Proof fields are irrelevant: equal underlying strings determine equal identifiers. -/
public theorem ext {left right : RequirementId} (h : left.value = right.value) :
    left = right := by
  cases left with
  | mk leftValue leftProperty =>
    cases right with
    | mk rightValue rightProperty =>
      cases h
      rfl

public instance : LawfulBEq RequirementId where
  rfl {a} := BEq.refl a.value
  eq_of_beq h := ext (eq_of_beq h)

public instance : DecidableEq RequirementId := instDecidableEqOfLawfulBEq

/-- Validate an untrusted requirement identifier. -/
public def parse (path value : String) : Except ValidationError RequirementId :=
  if h : ValidRequirementId value then
    .ok ⟨value, h⟩
  else
    .error { path, issue := .invalidRequirementId, rejected := some value }

/-- Successful parsing preserves the input and establishes the requirement-ID grammar. -/
public theorem parse_sound
    {path value : String} {result : RequirementId}
    (h : parse path value = .ok result) :
    result.value = value ∧ ValidRequirementId value := by
  unfold parse at h
  split at h
  · cases h
    exact ⟨rfl, ‹ValidRequirementId value›⟩
  · contradiction

/-- Parsing a validated identifier's payload recovers that identifier. -/
public theorem parse_complete {path : String} (result : RequirementId) :
    parse path result.value = .ok result := by
  unfold parse
  split
  · next h =>
    exact congrArg Except.ok (RequirementId.ext rfl)
  · next h =>
    exact absurd result.property h

end RequirementId

/-- Dotted skill id. Absolute paths, leading dots/dashes, and directory separators are refused. -/
public def validProcessSkillId (s : String) : Bool :=
  LeanUtil.nonemptyText s &&
    !s.startsWith "." &&
    !s.startsWith "-" &&
    s.all fun c => c.isAlphanum || c == '.' || c == '-'

public abbrev ValidProcessSkillId (value : String) : Prop :=
  validProcessSkillId value = true

public instance (value : String) : Decidable (ValidProcessSkillId value) :=
  by
    change Decidable (validProcessSkillId value = true)
    infer_instance

/-- A process-skill identifier carrying evidence that it follows `ValidProcessSkillId`. -/
public structure ProcessSkillId where
  value : String
  property : ValidProcessSkillId value
  deriving Repr

/-- Equality deliberately ignores proof terms; two identifiers compare by text. -/
public instance : BEq ProcessSkillId where
  beq left right := left.value == right.value

namespace ProcessSkillId

/-- Proof fields are irrelevant: equal underlying strings determine equal identifiers. -/
public theorem ext {left right : ProcessSkillId} (h : left.value = right.value) :
    left = right := by
  cases left with
  | mk leftValue leftProperty =>
    cases right with
    | mk rightValue rightProperty =>
      cases h
      rfl

public instance : LawfulBEq ProcessSkillId where
  rfl {a} := BEq.refl a.value
  eq_of_beq h := ext (eq_of_beq h)

public instance : DecidableEq ProcessSkillId := instDecidableEqOfLawfulBEq

/-- Validate an untrusted process-skill identifier. -/
public def parse (path value : String) : Except ValidationError ProcessSkillId :=
  if h : ValidProcessSkillId value then
    .ok ⟨value, h⟩
  else
    .error { path, issue := .invalidProcessSkillId, rejected := some value }

/-- Successful parsing preserves the input and establishes the skill-ID grammar. -/
public theorem parse_sound
    {path value : String} {result : ProcessSkillId}
    (h : parse path value = .ok result) :
    result.value = value ∧ ValidProcessSkillId value := by
  unfold parse at h
  split at h
  · cases h
    exact ⟨rfl, ‹ValidProcessSkillId value›⟩
  · contradiction

/-- Parsing a validated skill identifier's payload recovers that identifier. -/
public theorem parse_complete {path : String} (result : ProcessSkillId) :
    parse path result.value = .ok result := by
  unfold parse
  split
  · next h =>
    exact congrArg Except.ok (ProcessSkillId.ext rfl)
  · next h =>
    exact absurd result.property h

end ProcessSkillId

/-- An array carrying evidence that it contains at least one element. -/
public structure NonEmptyArray (α : Type u) where
  items : Array α
  property : 0 < items.size
  deriving Repr

/-- Equality deliberately ignores proof terms; two collections compare by items. -/
public instance [BEq α] : BEq (NonEmptyArray α) where
  beq left right := left.items == right.items

namespace NonEmptyArray

/-- Proof fields are irrelevant: equal underlying arrays determine equal collections. -/
public theorem ext {left right : NonEmptyArray α} (h : left.items = right.items) :
    left = right := by
  cases left with
  | mk leftItems leftProperty =>
    cases right with
    | mk rightItems rightProperty =>
      cases h
      rfl

public instance [BEq α] [LawfulBEq α] : LawfulBEq (NonEmptyArray α) where
  rfl {a} := BEq.refl a.items
  eq_of_beq h := ext (eq_of_beq h)

/-- Validate an untrusted array. `path` identifies the collection for diagnostics. -/
public def ofArray (path : String) (items : Array α) : Except ValidationError (NonEmptyArray α) :=
  if h : 0 < items.size then
    .ok ⟨items, h⟩
  else
    .error { path, issue := .emptyArray }

/-- Successful construction preserves the array and establishes non-emptiness. -/
public theorem ofArray_sound
    {path : String} {items : Array α} {result : NonEmptyArray α}
    (h : ofArray path items = .ok result) :
    result.items = items ∧ 0 < items.size := by
  unfold ofArray at h
  split at h
  · cases h
    exact ⟨rfl, ‹0 < items.size›⟩
  · contradiction

/-- Constructing from a nonempty array's items recovers that array. -/
public theorem ofArray_complete {path : String} (result : NonEmptyArray α) :
    ofArray path result.items = .ok result := by
  unfold ofArray
  split
  · next h =>
    exact congrArg Except.ok (NonEmptyArray.ext rfl)
  · next h =>
    exact absurd result.property h

public def head (items : NonEmptyArray α) : α :=
  items.items[0]'items.property

public def toArray (items : NonEmptyArray α) : Array α := items.items

public theorem toArray_not_isEmpty (items : NonEmptyArray α) : items.toArray.isEmpty = false := by
  simp [toArray]
  intro h
  have hsz : items.items.size = 0 := by simp [h]
  exact Nat.ne_of_gt items.property hsz

public def size (items : NonEmptyArray α) : Nat := items.items.size

/-- Pushing preserves non-emptiness. -/
public def push (items : NonEmptyArray α) (value : α) : NonEmptyArray α :=
  ⟨items.items.push value, by
    rw [Array.size_push]
    exact Nat.zero_lt_succ _⟩

end NonEmptyArray

/-! ## Generic indexed list parser

`parseNonBlankList`, `parseProcessSkillIdList`, and `Reflection`'s `parseRunRefList`
are the *same* recursion over a per-element parser. `parseList` is that shape once,
with its round-trip (`parseList_sound`/`parseList_complete`) proved once and every
list parser reduced to a thin delegation. The element parser is passed together with
its `value` projection and element-level round-trip facts. -/

/-- Apply `elem` to each raw element in order, threading the indexed field path.
Generic over the element wire type `R` (usually `String`, but any raw type for the
codec `list`). -/
public def parseList {R E : Type} (elem : String → R → Except ValidationError E)
    (path : String) (i : Nat) : List R → Except ValidationError (List E)
  | [] => .ok []
  | value :: rest =>
    match elem s!"{path}[{i}]" value with
    | .error e => .error e
    | .ok parsed =>
      match parseList elem path (i + 1) rest with
      | .error e => .error e
      | .ok restParsed => .ok (parsed :: restParsed)

/-- **Soundness, once.** If every element parser projects back (`elem_sound`), the
whole list projects back to the raw strings. -/
public theorem parseList_sound {R E : Type} (enc : E → R)
    (elem : String → R → Except ValidationError E)
    (elem_sound : ∀ {p : String} {r : R} {e : E}, elem p r = .ok e → enc e = r)
    {path : String} (i : Nat) {raws : List R} {parsed : List E}
    (h : parseList elem path i raws = .ok parsed) :
    parsed.map enc = raws := by
  induction raws generalizing i parsed with
  | nil => cases h; rfl
  | cons value rest ih =>
    simp [parseList] at h
    split at h
    · contradiction
    · next e hParse =>
      split at h
      · contradiction
      · next restParsed hRest =>
        cases h
        have hVal := elem_sound hParse
        have hTail := ih (i := i + 1) hRest
        simp [hVal, hTail]

/-- **Completeness, once.** If every element re-parses from its projection
(`elem_complete`), a domain list re-parses from its projections. -/
public theorem parseList_complete {R E : Type} (enc : E → R)
    (elem : String → R → Except ValidationError E)
    (elem_complete : ∀ {p : String} (e : E), elem p (enc e) = .ok e)
    (path : String) (i : Nat) (parsed : List E) :
    parseList elem path i (parsed.map enc) = .ok parsed := by
  induction parsed generalizing i with
  | nil => rfl
  | cons e rest ih =>
    simp [parseList, elem_complete, ih]

/-- Parse a list of non-blank strings — `parseList` at `NonBlank.parse`. -/
public def parseNonBlankList (path : String) (i : Nat) :
    List String → Except ValidationError (List NonBlank) :=
  parseList NonBlank.parse path i

public theorem parseNonBlankList_sound
    {path : String} (i : Nat) {raws : List String} {parsed : List NonBlank}
    (h : parseNonBlankList path i raws = .ok parsed) :
    parsed.map (·.value) = raws :=
  parseList_sound (·.value) NonBlank.parse (fun hp => (NonBlank.parse_sound hp).1) i h

public theorem parseNonBlankList_complete
    (path : String) (i : Nat) (parsed : List NonBlank) :
    parseNonBlankList path i (parsed.map (·.value)) = .ok parsed := by
  unfold parseNonBlankList
  exact parseList_complete (fun n => n.value) NonBlank.parse
    (fun e => NonBlank.parse_complete e) path i parsed

/-- Parse a list of process-skill identifiers — `parseList` at `ProcessSkillId.parse`. -/
public def parseProcessSkillIdList (path : String) (i : Nat) :
    List String → Except ValidationError (List ProcessSkillId) :=
  parseList ProcessSkillId.parse path i

public theorem parseProcessSkillIdList_sound
    {path : String} (i : Nat) {raws : List String} {parsed : List ProcessSkillId}
    (h : parseProcessSkillIdList path i raws = .ok parsed) :
    parsed.map (·.value) = raws :=
  parseList_sound (·.value) ProcessSkillId.parse (fun hp => (ProcessSkillId.parse_sound hp).1) i h

public theorem parseProcessSkillIdList_complete
    (path : String) (i : Nat) (parsed : List ProcessSkillId) :
    parseProcessSkillIdList path i (parsed.map (·.value)) = .ok parsed := by
  unfold parseProcessSkillIdList
  exact parseList_complete (fun n => n.value) ProcessSkillId.parse
    (fun e => ProcessSkillId.parse_complete e) path i parsed

end

end LeanSpec
