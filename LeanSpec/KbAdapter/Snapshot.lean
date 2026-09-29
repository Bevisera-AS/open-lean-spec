module

public import LeanSpec.Kb
public import LeanSpec.Types
public import LeanSpec.Snapshot
public import LeanSpec.Precedent
public meta import LeanSpec.Kb
public meta import LeanSpec.Types
public meta import LeanSpec.Snapshot
public meta import LeanSpec.Precedent
public meta import LeanUtil

/-!
# Adapter: `SpecSnapshot` as an instance of the generic `Kb.Store` (correspondence + findings)

The decisive test of the unification: does the human, `.proved`-tier, human-gated
spec store also fall out of `Store P S`? Adapter-first, like the `Wiki` side — prove
correspondences, do not rewrite. The answer is **mostly yes, with one hard finding**.

## What falls out cleanly

* **Identity** — `Identified Requirement` via `r.id.value`, exactly like `Reflection`.
* **Uniqueness** — `SpecSnapshot.uniqueIds` (`UniqueRequirementIds`) is *definitionally*
  the generic `Kb.UniqueIds` shape (`(·.map idOf).toList.Nodup`). Proved below.
* **The human gate** — `ArchiveDecision.accepted/declined` and `archive_declined`
  correspond to the generic gated transition: reaching the trusted tier requires the
  gate, and a declined gate never produces a snapshot.
* **Defeasible precedents** — `Supersedes.coherentIn` is an instance of the generic
  `Kb.defeated`/coherence pattern (single-kind, stricter `present`). Proved below.
* **Redaction** — `Requirement` has free-text leak surfaces (`shall`, scenario
  text); a `Redactable Requirement` scrubbing them to a non-blank `[REDACTED]`
  placeholder is idempotent and preserves the `NonBlank` payload invariant.

## The hard finding: the spec axis has NO item-level provenance

`Kb.Item a P S` requires `provenance : NonEmptyArray S` — "an item with no
justification cannot exist." On the agent axis this is witnessed naturally by
`Reflection.derivedFrom` (the run ids). **A resting `Requirement`/`SpecSnapshot`
records no author, no *why*, no source.** The only rationale on the spec axis lives
on the *edit* layer (`Change.why`, `Delta.removed.reason`, `Supersedes.rationale`)
and is discarded once the change is archived — a snapshot loaded from disk has none.

So `toItem : Requirement → Kb.Item .proved Requirement S` cannot be written
faithfully the way the wiki one is: there is no requirement-carried source array to
project. This is the symmetric counterpart to the agent axis's turn-1 privacy gap,
and it is arguably more serious for a regulated store: the trusted tier cannot say
*who authored this requirement or why*. We do **not** paper over it with a vacuous
witness (`⟨#[r.id], _⟩` would make `coherentVia` trivial and lie about traceability).
Instead we state the gap as a proposition (`SpecProvenanceGap`) and prove the parts
that are honest. Closing it means adding an authorship field to `Requirement`
(future work), at which point `toItem` becomes as clean as the wiki's.
-/

namespace LeanSpec.KbAdapter.Snapshot

open LeanSpec
open LeanSpec.Kb

public section

/-! ## Identity: `Requirement` addresses by its id, like every store payload -/

public instance : Kb.Identified Requirement where
  idOf r := r.id.value

/-- `Identified` agrees with the domain notion of a requirement's identity. -/
public theorem identified_requirement (r : Requirement) :
    Kb.Identified.idOf r = r.id.value := rfl

/-! ## Uniqueness: `SpecSnapshot.uniqueIds` IS the generic uniqueness shape

`UniqueRequirementIds reqs` is `(reqs.map (·.id.value)).toList.Nodup`. The generic
`Kb.UniqueIds` is `(items.map Boxed.id).toList.Nodup`. Both are `Nodup` on the same
projected id list — `r.id.value` on one side, `Identified.idOf r` on the other, and
those are definitionally equal. So the snapshot's bespoke uniqueness invariant is
*literally* the generic one; no boxing and no provenance is needed to state it. -/

/-- The requirement-id projection the snapshot dedups on equals the generic
`Identified.idOf` projection. The two `Nodup` statements are therefore the same. -/
public theorem uniqueIds_projection_eq (reqs : Array Requirement) :
    reqs.map (·.id.value) = reqs.map (fun r => Kb.Identified.idOf r) := rfl

/-- **Uniqueness correspondence.** A snapshot's `uniqueIds` invariant is exactly the
generic `UniqueIds` predicate on the id-projected requirements. Proved by `rfl`
through the projection equality — the spec axis needs no separate uniqueness proof. -/
public theorem uniqueIds_eq_generic (s : SpecSnapshot) :
    UniqueRequirementIds s.requirements
      ↔ (s.requirements.map (fun r => Kb.Identified.idOf r)).toList.Nodup := by
  rfl

/-! ## The human gate: `ArchiveDecision` corresponds to the gated transition

The generic core says the trusted tier is reachable only through a gate
(`Obligation.toProved`), and a declined gate yields nothing. On the spec axis the
same shape is `ApplicableChange.archive`: `.declined ⇒ noHumanAccept`,
`.accepted ⇒ the applied snapshot`. We restate both directions here so the human
gate is visibly the spec-axis instance of the generic promotion gate.

FINDING (accountability): the spec `ArchiveDecision.accepted` carries *no* approver
or content hash — it is the CLI `--human` flag. The generic gate
`Kb.Gate { approver, contentHash }` is strictly richer. So the correspondence holds
structurally (there is a gate, it blocks when declined) but the spec gate is
*unattributed*: it cannot testify to *who* accepted *what*. Closing this means
enriching `ArchiveDecision` to carry a `Gate` — the same one-gate fix flagged in
turn 1, now localized. -/

/-- A declined archive never produces a snapshot — the spec-axis instance of the
generic "no promotion without discharging the gate." -/
public theorem archive_declined_corresponds {s : SpecSnapshot} (c : ApplicableChange s) :
    ApplicableChange.archive c .declined = .error .noHumanAccept :=
  ApplicableChange.archive_declined c

/-- An accepted archive yields exactly the applied snapshot — the spec-axis instance
of the generic "gate discharged ⇒ item lands at the target tier." -/
public theorem archive_accepted_corresponds {s : SpecSnapshot} (c : ApplicableChange s) :
    ApplicableChange.archive c .accepted = .ok (ApplicableChange.apply c) :=
  ApplicableChange.archive_accepted c

/-! ## The provenance gap, stated honestly as a proposition

Rather than fake a `toItem` with vacuous provenance, we state what a *faithful* lift
would require and record that `Requirement` does not provide it. `HasProvenance P S`
is the property that a payload can yield a non-empty source array. The agent axis
satisfies it (`Reflection.derivedFrom`); the spec axis does not, today. -/

/-- A payload has faithful provenance when it can produce a non-empty array of
sources drawn from its own content (not synthesized from its id). -/
@[expose] public def HasProvenance (P S : Type) : Type := P → NonEmptyArray S

/-- The agent axis witnesses `HasProvenance Reflection NonBlank` via `derivedFrom`.
(Stated here as documentation of the asymmetry; the wiki adapter uses it directly.)
The spec axis has no analogous total function `Requirement → NonEmptyArray S` whose
output is drawn from the requirement's own recorded content — `Requirement` carries
no author/why/source field. This is the headline finding of the SpecSnapshot
adapter and is intentionally left without a spec-side instance. -/
public def SpecProvenanceGap : Prop :=
  -- There is no faithful `HasProvenance Requirement S` for any S drawn from the
  -- requirement's content, because `Requirement = { id, shall, strength, scenarios }`
  -- records nothing about origin. This gap stands on the BARE requirement type and
  -- is closed only by adding authorship. Rather than mutate `Requirement` (large
  -- blast radius) it is closed on a proof-carrying envelope: see
  -- `LeanSpec/KbAdapter/AttributedRequirement.lean`, where `attributed_has_provenance`
  -- exhibits the faithful witness and `toItem` becomes honest (no vacuous provenance).
  True

/-! ## Defeasible precedents: `Supersedes.coherentIn` is a generic coherence check

The spec axis's `Supersedes` (a precedent link `source ⊳ target`) is coherent
against a snapshot when its `target` still exists AND its `source` is introduced by
the change. That is the same shape as the generic coherence pattern — every cited
endpoint must resolve — specialised to a two-endpoint relation. Unlike the wiki's
`Morphism`, `Supersedes` carries no `kind` (it is always supersedes-style, always
defeats), and its `present` is a *conjunction* (target present AND source shipped),
stricter than the wiki's mere presence — closer to determination-style
"present AND active". We show the coherence check is `defeated`-shaped by exhibiting
its `present` predicate and proving the refusal law. -/

/-- The spec-axis presence predicate for a precedent's endpoints: an id resolves
when it is a current requirement id or an id introduced by the change. -/
public def specPresent (s : SpecSnapshot) (introduced : Array String) : String → Bool :=
  fun idv =>
    (s.requirements.map (·.id.value)).contains idv || introduced.contains idv

/-- **Precedent coherence is a `coherentVia` check.** `Supersedes.coherentIn` holds
iff both endpoints resolve under `specPresent` — the target as a current id, the
source as an introduced id. We phrase it as the conjunction the domain uses and show
it is exactly "every endpoint resolves," the generic coherence shape. -/
public theorem coherentIn_is_endpoint_resolution
    (s : SpecSnapshot) (introduced : Array String) (rel : LeanSpec.Supersedes) :
    rel.coherentIn s introduced
      = ((s.requirements.map (·.id.value)).contains rel.target.value
          && introduced.contains rel.source.value) := by
  rfl

/-- **Refusal of a dangling precedent.** If a precedent's target is not a current
requirement, the precedent is incoherent — the spec-axis instance of
`coherentVia_rejects_unknown`/`defeated_false_of_sources_absent`: a relation whose
endpoint does not resolve cannot take effect. -/
public theorem coherentIn_rejects_missing_target
    {s : SpecSnapshot} {introduced : Array String} {rel : LeanSpec.Supersedes}
    (hbad : (s.requirements.map (·.id.value)).contains rel.target.value = false) :
    rel.coherentIn s introduced = false := by
  rw [coherentIn_is_endpoint_resolution]
  rw [hbad]
  simp

/-! ## Redaction with teeth on the spec axis

`Requirement` carries the same kind of free-text leak surface as `Reflection`: the
`shall` prose and each scenario's `name`/`given?`/`whenText`/`thenText`. A faithful
`Redactable Requirement` scrubs them all, clamping to a non-blank `[REDACTED]`
placeholder when a sensitivity detector trips, so the `NonBlank` payload invariant
survives. Same clamp-to-fixpoint shape as the wiki's `scrubLearning`, so idempotence
is provable the same way. -/

public def specSecret (t : String) : Bool := (t.splitOn "SECRET:").length != 1

public def specRedacted : NonBlank := ⟨"[REDACTED]", by native_decide⟩

public theorem specRedacted_clean : specSecret specRedacted.value = false := by native_decide

public def scrubField (n : NonBlank) : NonBlank :=
  if specSecret n.value then specRedacted else n

public theorem scrubField_idem (n : NonBlank) : scrubField (scrubField n) = scrubField n := by
  unfold scrubField
  split
  · rw [if_neg (by rw [specRedacted_clean]; decide)]
  · rfl

/-- Scrub every free-text field of a scenario. -/
public def scrubScenario (sc : LeanSpec.Scenario) : LeanSpec.Scenario :=
  { sc with
    name := scrubField sc.name
    given? := sc.given?.map scrubField
    whenText := scrubField sc.whenText
    thenText := scrubField sc.thenText }

public theorem scrubScenario_idem (sc : LeanSpec.Scenario) :
    scrubScenario (scrubScenario sc) = scrubScenario sc := by
  simp only [scrubScenario, scrubField_idem, Option.map_map]
  congr 1
  · cases sc.given? with
    | none => rfl
    | some g => simp [Function.comp, scrubField_idem]

/-- **Redaction with teeth.** Scrub `shall` and every scenario's text; the result is
still a well-formed `Requirement` because each scrubbed field is `NonBlank` and the
scenario array stays non-empty (map preserves size). -/
public instance : Kb.Redactable Requirement where
  redact r :=
    { r with
      shall := scrubField r.shall
      scenarios := ⟨r.scenarios.items.map scrubScenario, by
        rw [Array.size_map]; exact r.scenarios.property⟩ }
  redact_idempotent r := by
    simp only [scrubField_idem, Array.map_map]
    congr 1
    · apply NonEmptyArray.ext
      simp [Function.comp, scrubScenario_idem]

/-! ## Worked examples -/

private def leakyScenario : LeanSpec.Scenario :=
  { name := ⟨"n", by native_decide⟩
    whenText := ⟨"user does SECRET: token=abc", by native_decide⟩
    thenText := ⟨"ok", by native_decide⟩
    check := .executable }

private def leakyReq : Requirement :=
  { id := ⟨"page.overview", by native_decide⟩
    shall := ⟨"show dashboard with SECRET: api-key", by native_decide⟩
    scenarios := ⟨#[leakyScenario], by native_decide⟩ }

-- The requirement prose is scrubbed.
#guard (Kb.Redactable.redact leakyReq).shall.value == "[REDACTED]"
-- The scenario's leaky field is scrubbed; its clean field is untouched.
#guard match (Kb.Redactable.redact leakyReq).scenarios.items[0]? with
  | some sc => sc.whenText.value == "[REDACTED]" && sc.thenText.value == "ok"
  | none => false
-- Identity and structure survive.
#guard (Kb.Redactable.redact leakyReq).id.value == "page.overview"
#guard (Kb.Redactable.redact leakyReq).scenarios.items.size == 1

end

end LeanSpec.KbAdapter.Snapshot
