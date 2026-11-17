import LeanSpec.Logic.Core

/-!
# The package layering, as a spec of the five packages

A reflection after the lean-kb split (2026-10-29), in the library's own terms. The goal:
lean-spec teaches a model to write specs as code; lean-agent is an agent; lean-kb is
typed memory; lean-spec-agent combines them into one typed workflow, where contracts are
lean-specs, memory is typed Lean and skills are typed Lean; business-kb is a domain that
consumes the combination.

Memory has two parallel planes, an agent plane and a human-knowledge plane, on one ladder
(lean-kb's `Assurance`). On the agent plane an agent records freely, however odd the
consolidation; nothing climbs without lean-kb's `promote` and a `Gate` a person holds. So
"memory is typed" means the ladder is typed, not that every log line is.

Learning is a discipline, not a side effect: review, then reflect, is the one way experience
enters the agent plane, and a reflection proposes; it never edits a human artifact. Every
rung is traceable down to the agent trace it came from, by the trace's content digest,
not only by its name.

`Sig` is the package graph and who owns which type. The requirements say what the goal
asks of the graph. `today` is the graph the lakefiles and AGENTS.md files describe on
2026-10-29, and it is a counter-model: five rows refute it. `proposal` is one graph that
satisfies every row; it is a model, nothing has moved.

Phase: propose. The product is the set of lakefiles, not a Lean value, so the bar is
`evidenced`; every row is `model` until the lakefiles change.
-/

namespace LeanSpec.Spec.Layering

open LeanSpec.Logic

spec_bar evidenced

inductive Pkg where
  | leanSpec | leanKb | leanAgent | leanSpecAgent | businessKb
  deriving DecidableEq, Repr

/-- The agent plane (reflections, the discovery log, the evolution graph) and the
human-knowledge plane (observations, reviews, activation receipts). -/
inductive Plane where
  | agent | human
  deriving DecidableEq, Repr

structure Sig where
  /-- `require` in the lakefile, direct only. -/
  requires : Pkg → Pkg → Bool
  /-- The package that defines the typed skill (`ProcessSkill`, `Skillset`). -/
  skillHome : Pkg
  definesSkillType : Pkg → Bool
  /-- The package that defines typed memory (`Kb`, and the `Wiki` instance). -/
  memoryHome : Pkg
  /-- The package that holds the workflow (propose, review, apply, archive, reflect). -/
  workflowHome : Pkg
  /-- The package writes durable memory on this plane. -/
  writes : Pkg → Plane → Bool
  /-- Recording at the bottom rung needs a person's approval. -/
  recordGated : Pkg → Plane → Bool
  /-- Anything that climbs goes through the memory core's `promote` with a `Gate`. -/
  promotesViaCore : Pkg → Plane → Bool
  /-- The package defines a review/reflect discipline (a `process.reflect` skill). -/
  definesReflect : Pkg → Bool
  /-- Its reflect discipline lets an agent change a skill, requirement or steering itself. -/
  reflectEditsHumanArtifact : Pkg → Bool
  /-- The package writes agent traces (transcripts, run receipts). -/
  writesTraces : Pkg → Bool
  /-- Every trace it writes carries a content digest computed in Lean, never empty. -/
  digestInLean : Pkg → Bool
  /-- What it writes on this plane cites its traces by content digest, not only by run id. -/
  citesDigest : Pkg → Plane → Bool

/-- Within two `require` steps; the graph is no deeper. -/
def reaches (S : Sig) (p q : Pkg) : Prop :=
  S.requires p q = true ∨ ∃ r, S.requires p r = true ∧ S.requires r q = true

/-- A workspace that requires lean-spec to write specs fetches nothing else. -/
@[requirement must]
def specLibraryStandsAlone (S : Sig) : Prop :=
  ∀ q, S.requires .leanSpec q = false

/-- The agent knows no spec, memory or skill package. -/
@[requirement must]
def agentStandsAlone (S : Sig) : Prop :=
  ∀ q, S.requires .leanAgent q = false

/-- The memory core rests on Lean alone. -/
@[requirement must]
def memoryCoreStandsAlone (S : Sig) : Prop :=
  ∀ q, S.requires .leanKb q = false

/-- Specs and the agent meet in one place: a package that requires both is lean-spec-agent. -/
@[requirement must]
def oneCombiner (S : Sig) : Prop :=
  ∀ p, S.requires p .leanSpec = true → S.requires p .leanAgent = true → p = .leanSpecAgent

/-- One skill type, defined once. -/
@[requirement must]
def oneSkillType (S : Sig) : Prop :=
  ∀ p, S.definesSkillType p = true ↔ p = S.skillHome

/-- The combiner reaches the skill type, and a domain does not own it. -/
@[requirement must]
def skillsReachable (S : Sig) : Prop :=
  S.skillHome ≠ .businessKb ∧ reaches S .leanSpecAgent S.skillHome

/-- The workflow is the combination, so the combiner holds it. -/
@[requirement must]
def workflowInCombiner (S : Sig) : Prop :=
  S.workflowHome = .leanSpecAgent

/-- Both planes are kept: agent experience does not replace preserved human knowledge. -/
@[requirement must]
def planesParallel (S : Sig) : Prop :=
  (∃ p, S.writes p .agent = true) ∧ (∃ p, S.writes p .human = true)

/-- An agent records on its plane without asking, however odd the consolidation. -/
@[requirement must]
def agentRecordsFreely (S : Sig) : Prop :=
  ∀ p, S.writes p .agent = true → S.recordGated p .agent = false

/-- One ladder: on every plane, what climbs climbs through the core's `promote`. -/
@[requirement must]
def promotionThroughCore (S : Sig) : Prop :=
  ∀ p pl, S.writes p pl = true → S.promotesViaCore p pl = true

/-- Every writer of memory reaches the memory type. -/
@[requirement must]
def memoryReachable (S : Sig) : Prop :=
  ∀ p pl, S.writes p pl = true → p = S.memoryHome ∨ reaches S p S.memoryHome

/-- One review/reflect discipline, held with the workflow it ends. -/
@[requirement must]
def oneReflectDiscipline (S : Sig) : Prop :=
  ∀ p, S.definesReflect p = true ↔ p = S.workflowHome

/-- Reflection proposes; only a person's gate changes a human artifact. -/
@[requirement must]
def reflectNeverPromotes (S : Sig) : Prop :=
  ∀ p, S.reflectEditsHumanArtifact p = false

/-- Every agent trace is content-addressed, by a digest the kernel's language computes. -/
@[requirement must]
def tracesDigestedInLean (S : Sig) : Prop :=
  ∀ p, S.writesTraces p = true → S.digestInLean p = true

/-- Every rung on every plane traces to its runs by content, so a cited run is the run. -/
@[requirement must]
def provenanceToTrace (S : Sig) : Prop :=
  ∀ p pl, S.writes p pl = true → S.citesDigest p pl = true

-- ─── Today: the graph on 2026-10-29 ──────────────────────────────────────────

/-- lean-spec requires lean-kb for its process and Kb libraries; lean-spec-agent requires
lean-spec and lean-agent; business-kb requires lean-spec, lean-kb and lean-agent. -/
def requiresToday : Pkg → Pkg → Bool
  | .leanSpec, .leanKb => true
  | .leanSpecAgent, .leanSpec => true
  | .leanSpecAgent, .leanAgent => true
  | .businessKb, .leanSpec => true
  | .businessKb, .leanKb => true
  | .businessKb, .leanAgent => true
  | _, _ => false

/-- `LeanSpec.ProcessSkill` and business-kb's `Skills.Defs` are two skill types; the
workflow is `LeanSpec.Workflow`. On the agent plane lean-spec-agent writes the `Wiki`, a
`Kb.Store` instance (`KbAdapter`), and business-kb's agents write `DISCOVERY_LOG.md`,
distilled into `Skills.Evolution`, whose `GateResult` is its own gate and not lean-kb's
`promote`. On the human plane business-kb's `GraphKb` climbs through `promote`. Nobody
needs approval to record.

Two reflect disciplines: lean-spec's `process.reflect` (the Wiki, never a prose file) and
business-kb's `process.reflectDiscipline` (the log, and "if the home is clear, update the
existing skill", an agent edit that skips the gate `Memory.reflect` enforces in code).
lean-agent's transcripts carry a SHA-256 digest in pure Lean, verified on decode;
business-kb's `RunReceipt` shells out to `shasum` and accepts an empty digest. A `Wiki`
reflection cites `derivedFrom` run ids; business-kb's `EvolutionRun` and `GraphKb`'s
activation receipt carry a digest. -/
def today : Sig where
  requires := requiresToday
  skillHome := .leanSpec
  definesSkillType p := p == .leanSpec || p == .businessKb
  memoryHome := .leanKb
  workflowHome := .leanSpec
  writes p pl := (p == .leanSpecAgent && pl == .agent) || p == .businessKb
  recordGated _ _ := false
  promotesViaCore p pl := !(p == .businessKb && pl == .agent)
  definesReflect p := p == .leanSpec || p == .businessKb
  reflectEditsHumanArtifact p := p == .businessKb
  writesTraces p := p == .leanAgent || p == .businessKb
  digestInLean p := p == .leanAgent
  citesDigest p _ := p == .businessKb

@[refutes] theorem today_specLibrary : ¬ specLibraryStandsAlone today :=
  fun h => absurd (h .leanKb) (by decide)

@[refutes] theorem today_oneCombiner : ¬ oneCombiner today :=
  fun h => absurd (h .businessKb rfl rfl) (by decide)

@[refutes] theorem today_oneSkillType : ¬ oneSkillType today :=
  fun h => absurd ((h .businessKb).1 rfl) (by decide)

@[refutes] theorem today_workflow : ¬ workflowInCombiner today := by
  intro h; cases h

@[refutes] theorem today_promotion : ¬ promotionThroughCore today :=
  fun h => absurd (h .businessKb .agent rfl) (by decide)

@[refutes] theorem today_oneReflect : ¬ oneReflectDiscipline today :=
  fun h => absurd ((h .businessKb).1 rfl) (by decide)

@[refutes] theorem today_reflectPromotes : ¬ reflectNeverPromotes today :=
  fun h => absurd (h .businessKb) (by decide)

@[refutes] theorem today_traces : ¬ tracesDigestedInLean today :=
  fun h => absurd (h .businessKb rfl) (by decide)

@[refutes] theorem today_provenance : ¬ provenanceToTrace today :=
  fun h => absurd (h .leanSpecAgent .agent rfl) (by decide)

-- ─── The proposal: a model that satisfies every row ───────────────────────────

/-- lean-spec keeps Core and Logic only. `LeanSpecProcess` and `LeanSpecKb` (workflow,
reflection, finding, the `Wiki` instance) move to lean-spec-agent; `ProcessSkill` and
`Skillset` move to lean-kb beside `Validated`, which they already rest on. business-kb
requires lean-spec-agent instead of lean-spec and lean-agent separately. -/
def requiresProposal : Pkg → Pkg → Bool
  | .leanSpecAgent, .leanSpec => true
  | .leanSpecAgent, .leanAgent => true
  | .leanSpecAgent, .leanKb => true
  | .businessKb, .leanSpecAgent => true
  | .businessKb, .leanKb => true
  | _, _ => false

/-- business-kb's skills are values of lean-kb's skill type. Its discovery log stays a
free log; what the evolution graph distils from it enters a `Kb` store at `provisional`,
and an accepted `GateResult` is a `promote` with a `Gate`, as the human plane already is.

One `process.reflect`, in lean-spec-agent with the workflow: review, then reflect into the
agent plane (the Wiki or the free log, both bottom rungs), and a proposed home is a
proposal for the gate. business-kb adds domain rules through a skillset, not a second
discipline. Every trace is a lean-agent transcript with its Lean digest (`RunReceipt` uses
`LeanAgent.Sha256`), and a reflection's `derivedFrom` holds run id and digest. -/
def proposal : Sig where
  requires := requiresProposal
  skillHome := .leanKb
  definesSkillType p := p == .leanKb
  memoryHome := .leanKb
  workflowHome := .leanSpecAgent
  writes p pl := (p == .leanSpecAgent && pl == .agent) || p == .businessKb
  recordGated _ _ := false
  promotesViaCore _ _ := true
  definesReflect p := p == .leanSpecAgent
  reflectEditsHumanArtifact _ := false
  writesTraces p := p == .leanAgent || p == .businessKb
  digestInLean _ := true
  citesDigest _ _ := true

@[satisfies] theorem proposal_specLibrary : specLibraryStandsAlone proposal := by
  intro q; cases q <;> rfl

@[satisfies] theorem proposal_agent : agentStandsAlone proposal := by
  intro q; cases q <;> rfl

@[satisfies] theorem proposal_memoryCore : memoryCoreStandsAlone proposal := by
  intro q; cases q <;> rfl

@[satisfies] theorem proposal_oneCombiner : oneCombiner proposal := by
  intro p; cases p <;> decide

@[satisfies] theorem proposal_oneSkillType : oneSkillType proposal := by
  intro p; cases p <;> decide

@[satisfies] theorem proposal_skillsReachable : skillsReachable proposal :=
  ⟨by decide, Or.inl rfl⟩

@[satisfies] theorem proposal_workflow : workflowInCombiner proposal := rfl

@[satisfies] theorem proposal_planesParallel : planesParallel proposal :=
  ⟨⟨.businessKb, rfl⟩, ⟨.businessKb, rfl⟩⟩

@[satisfies] theorem proposal_agentRecordsFreely : agentRecordsFreely proposal :=
  fun _ _ => rfl

@[satisfies] theorem proposal_promotion : promotionThroughCore proposal :=
  fun _ _ _ => rfl

@[satisfies] theorem proposal_oneReflect : oneReflectDiscipline proposal := by
  intro p; cases p <;> decide

@[satisfies] theorem proposal_reflectNeverPromotes : reflectNeverPromotes proposal :=
  fun _ => rfl

@[satisfies] theorem proposal_traces : tracesDigestedInLean proposal :=
  fun _ _ => rfl

@[satisfies] theorem proposal_provenance : provenanceToTrace proposal :=
  fun _ _ _ => rfl

@[satisfies] theorem proposal_memoryReachable : memoryReachable proposal := by
  intro p pl hp
  cases p <;> cases pl
  all_goals first
    | exact absurd hp (by decide)
    | exact Or.inr (Or.inl rfl)

-- ─── Counter-models for the rows today satisfies ─────────────────────────────

/-- The agent imports the spec library to run the spec loop itself. -/
def specAwareAgent : Sig := { proposal with
  requires := fun p q => (p == .leanAgent && q == .leanSpec) || requiresProposal p q }

/-- The memory core borrows the requirement type. -/
def kbOnSpec : Sig := { proposal with
  requires := fun p q => (p == .leanKb && q == .leanSpec) || requiresProposal p q }

/-- One skill type, owned by the domain. -/
def domainSkills : Sig := { proposal with
  skillHome := .businessKb, definesSkillType := (· == .businessKb) }

/-- Memory typed in a package the combiner does not require. -/
def strandedMemory : Sig := { proposal with memoryHome := .businessKb }

/-- The agent plane only: experience replaces the preserved human knowledge. -/
def agentOnly : Sig := { proposal with writes := fun _ pl => pl == .agent }

/-- Every line an agent records waits for review first; odd consolidations never land. -/
def strict : Sig := { proposal with recordGated := fun _ _ => true }

@[refutes] theorem agentOnly_fails : ¬ planesParallel agentOnly := by
  rintro ⟨_, ⟨p, hp⟩⟩
  exact absurd hp (by cases p <;> decide)

@[refutes] theorem strict_fails : ¬ agentRecordsFreely strict :=
  fun h => absurd (h .businessKb rfl) (by decide)

@[refutes] theorem specAwareAgent_fails : ¬ agentStandsAlone specAwareAgent :=
  fun h => absurd (h .leanSpec) (by decide)

@[refutes] theorem kbOnSpec_fails : ¬ memoryCoreStandsAlone kbOnSpec :=
  fun h => absurd (h .leanSpec) (by decide)

@[refutes] theorem domainSkills_fails : ¬ skillsReachable domainSkills :=
  fun h => h.1 rfl

@[refutes] theorem strandedMemory_fails : ¬ memoryReachable strandedMemory := by
  intro h
  rcases h .leanSpecAgent .agent rfl with e | e | ⟨r, hr, hq⟩
  · exact absurd e (by decide)
  · exact absurd e (by decide)
  · cases r <;> simp_all [strandedMemory, proposal, requiresProposal]

-- ─── The statement: the review record ────────────────────────────────────────

spec_statement statement for LeanSpec.Spec.Layering

-- Propose phase: every row is `model`, refuted by `today` or by a named counter-model,
-- so no row is vacuous. A model-only row meets `evidenced`, so the mark is issued while
-- no lakefile has moved; the mark is about `proposal`, and that is the open question
-- this spec leaves for review.
#guard statement.rows.size == 15
#guard statement.rows.all (·.bar == .evidenced)
#guard statement.rows.all (·.status == "model")
#guard statement.rows.all fun r => !r.gaps.contains .vacuous
#guard statement.verified
#guard statement.mark == "lean-spec-verified at evidenced"

end LeanSpec.Spec.Layering
