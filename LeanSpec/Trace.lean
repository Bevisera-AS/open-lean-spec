module

public import LeanSpec.Types
public meta import LeanSpec.Types

namespace LeanSpec

public section

/-- A run identifier: the unique handle of one agent execution. A newtype over
non-blank text (same grammar as `NonBlank`), distinct at the type level so a run id
cannot be silently confused with a reflection id, requirement id, or free text.
`.value`/`.property` mirror `NonBlank`, so callers that projected a `NonBlank`
continue to work. -/
public structure RunId where
  value : String
  property : LeanUtil.nonemptyText value = true
  deriving Repr

/-- Equality ignores the proof; two run ids compare by text. -/
public instance : BEq RunId where
  beq l r := l.value == r.value

namespace RunId

public theorem ext {l r : RunId} (h : l.value = r.value) : l = r := by
  cases l with
  | mk lv lp => cases r with | mk rv rp => cases h; rfl

public instance : LawfulBEq RunId where
  rfl {a} := BEq.refl a.value
  eq_of_beq h := ext (eq_of_beq h)

public instance : DecidableEq RunId := instDecidableEqOfLawfulBEq

/-- Validate untrusted text as a run id. -/
public def parse (path value : String) : Except ValidationError RunId :=
  if h : LeanUtil.nonemptyText value = true then .ok ⟨value, h⟩
  else .error { path, issue := .blank, rejected := some value }

public theorem parse_sound {path value : String} {result : RunId}
    (h : parse path value = .ok result) :
    result.value = value ∧ LeanUtil.nonemptyText value = true := by
  unfold parse at h; split at h
  · cases h; exact ⟨rfl, ‹LeanUtil.nonemptyText value = true›⟩
  · contradiction

public theorem parse_complete {path : String} (result : RunId) :
    parse path result.value = .ok result := by
  unfold parse; split
  · next h => exact congrArg Except.ok (RunId.ext rfl)
  · next h => exact absurd result.property h

end RunId

/-- Classification of a single step in an agent reasoning trace. -/
public inductive TraceKind where
  | reasoning                        -- internal chain-of-thought
  | toolCall                         -- external action (file write, search, etc.)
  | decision                         -- choice made with rationale
  | observation                      -- something noticed in code/data/output
  deriving Repr, BEq, DecidableEq

/-- A single reasoning step in an agent run. Proof-carrying: blank fields
cannot inhabit the type. `cites` links steps to requirement ids. -/
public structure TraceStep where
  timestamp : NonBlank               -- ISO 8601
  kind      : TraceKind
  content   : NonBlank               -- what was thought/done
  cites     : Array RequirementId    -- which specs this step relates to (may be empty)
  deriving Repr, BEq

/-- Compatibility predicate. Inspects proof-carrying fields. -/
public def TraceStep.wellFormed (s : TraceStep) : Bool :=
  LeanUtil.nonemptyText s.timestamp.value &&
    LeanUtil.nonemptyText s.content.value

/-- Every domain `TraceStep` satisfies the compatibility well-formedness predicate. -/
public theorem TraceStep.wellFormed_eq_true (s : TraceStep) : s.wellFormed = true := by
  simp only [TraceStep.wellFormed]
  rw [s.timestamp.property, s.content.property]
  rfl

/-- How an agent run concluded. -/
public inductive TraceOutcome where
  | completed (artifacts : Array NonBlank)   -- files/declarations produced
  | stopped   (reason : NonBlank)            -- interrupted or timed out
  | refused   (reason : NonBlank)            -- agent declined the task
  deriving Repr, BEq

/-- A complete agent run trace, tied to a change or requirement.
`runId` is unique per execution; `changeId` links to a spec change when applicable. -/
public structure AgentTrace where
  runId    : RunId
  changeId : Option RequirementId    -- which change/requirement this implements
  model    : NonBlank                -- which model was used
  steps    : NonEmptyArray TraceStep
  outcome  : TraceOutcome
  deriving Repr, BEq

/-- Compatibility predicate. -/
public def AgentTrace.wellFormed (t : AgentTrace) : Bool :=
  LeanUtil.nonemptyText t.runId.value &&
    LeanUtil.nonemptyText t.model.value &&
    decide (0 < t.steps.items.size) &&
    t.steps.toArray.all TraceStep.wellFormed

/-- Every domain `AgentTrace` satisfies the compatibility well-formedness predicate. -/
public theorem AgentTrace.wellFormed_eq_true (t : AgentTrace) : t.wellFormed = true := by
  simp only [AgentTrace.wellFormed]
  rw [t.runId.property, t.model.property, decide_eq_true t.steps.property]
  simp [TraceStep.wellFormed_eq_true]

/-- Where a durable learning should be promoted. -/
public inductive PromotionTarget where
  | skill       -- update or create a ProcessSkill
  | requirement -- feed back into a Requirement scenario
  | steering    -- add to a steering/conventions file
  | noAction    -- nothing durable was learned
  deriving Repr, BEq, DecidableEq

-- `Reflection` — the consolidated agent-experience node — lives in
-- `LeanSpec/Reflection.lean`, strengthened per the WikiSkill note (many-run
-- `derivedFrom`, a knowledge `kind`, and the full Raw/validate house).
-- `PromotionTarget` stays here because it is the valve *out* of the trace layer.

-- Basic smoke tests

#guard (TraceKind.reasoning != TraceKind.toolCall)
#guard (TraceKind.decision != TraceKind.observation)

#guard
  let step : TraceStep := {
    timestamp := ⟨"2025-01-15T10:30:00Z", by native_decide⟩
    kind := .reasoning
    content := ⟨"Reading the snapshot to understand current state", by native_decide⟩
    cites := #[⟨"demo.requirement", by native_decide⟩]
  }
  step.wellFormed

#guard
  let trace : AgentTrace := {
    runId := ⟨"run-001", by native_decide⟩
    changeId := some ⟨"demo.requirement", by native_decide⟩
    model := ⟨"claude-sonnet-4-20250514", by native_decide⟩
    steps := ⟨#[{
      timestamp := ⟨"2025-01-15T10:30:00Z", by native_decide⟩
      kind := .decision
      content := ⟨"Chose to add a new scenario for the edge case", by native_decide⟩
      cites := #[⟨"demo.requirement", by native_decide⟩]
    }], by native_decide⟩
    outcome := .completed #[⟨"LeanSpec/Demo/SpecSyntax.lean", by native_decide⟩]
  }
  trace.wellFormed

end

end LeanSpec
