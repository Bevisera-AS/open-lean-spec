module

public import LeanSpec.Kb
public import LeanSpec.Types
public import LeanSpec.KbAdapter.Snapshot
public meta import LeanSpec.Kb
public meta import LeanSpec.Types
public meta import LeanSpec.KbAdapter.Snapshot
public meta import LeanUtil

/-!
# Closing `SpecProvenanceGap`: an attributed requirement carries its provenance

The `SpecSnapshot` adapter found that a bare `Requirement` records no author, why,
or source, so the generic non-empty `provenance` law had no faithful witness. This
module closes that gap **without touching `Requirement`, `SpecSnapshot`, the sugar
syntax, the codecs, or any existing test** — the blast radius of adding a mandatory
field to `Requirement` would be large and would force fake authorship onto legacy
data.

Instead we follow the codebase's own layering habit (`ApplicableChange` wraps
`Change`; `PrecedentedChange` wraps it again): attribution is a *proof-carrying
envelope*, not a mutation of the base type. `AttributedRequirement` is a
`Requirement` together with a `NonEmptyArray AuthorRef` — non-empty **by
construction**, so:

* the gap is closed *on this type*: you cannot build an `AttributedRequirement`
  without naming at least one author/source;
* the trusted-tier lift `attrToItem : AttributedRequirement → Item .proved …` is now
  **faithful** — provenance is drawn from the value's own content, no vacuous
  `⟨#[r.id], _⟩` witness;
* everything that speaks bare `Requirement` keeps working unchanged; only code that
  wants the trusted, attributed tier opts in.

`SpecProvenanceGap` is discharged for `AttributedRequirement`
(`attributed_has_provenance`), and the accountability follow-up — enriching the
archive gate with an attributed `Kb.Gate` — is the natural next companion.
-/

namespace LeanSpec.KbAdapter

open LeanSpec
open LeanSpec.Kb

public section

/-- Who or what authored/justified a requirement: an author id, a change id, a
citation. A `NonBlank` string, mirroring the agent axis's run ids (`derivedFrom`).
A dedicated newtype keeps it from being confused with a requirement id at call
sites while staying serialization-transparent. -/
public structure AuthorRef where
  value : NonBlank
  deriving Repr

public instance : BEq AuthorRef where
  beq l r := l.value == r.value

/-- A requirement together with faithful, non-empty provenance. The gap the
`SpecSnapshot` adapter found is closed here by construction: an attributed
requirement with no author cannot exist. -/
public structure AttributedRequirement where
  req        : Requirement
  provenance : NonEmptyArray AuthorRef
  deriving Repr

public instance : BEq AttributedRequirement where
  beq l r := l.req == r.req && l.provenance.items == r.provenance.items

/-- Identity is the underlying requirement's id — the envelope does not change what
the item *is*, only what we know about its origin. -/
public instance : Kb.Identified AttributedRequirement where
  idOf a := a.req.id.value

public theorem attributed_id (a : AttributedRequirement) :
    Kb.Identified.idOf a = a.req.id.value := rfl

/-! ## Faithful provenance — the gap closed

`HasProvenance` (from the Snapshot adapter) asks for a total function producing a
non-empty source array *drawn from the value's own content*. For a bare
`Requirement` there is none. For `AttributedRequirement` it is just the
`provenance` field. -/

/-- The faithful provenance witness the bare requirement could not provide. -/
public def attributedProvenance : Snapshot.HasProvenance AttributedRequirement AuthorRef :=
  fun a => a.provenance

/-- **`SpecProvenanceGap` is closed for the attributed type.** There now exists a
faithful `HasProvenance AttributedRequirement AuthorRef` whose output is the value's
own recorded provenance — not synthesized from its id. -/
public theorem attributed_has_provenance :
    Nonempty (Snapshot.HasProvenance AttributedRequirement AuthorRef) :=
  ⟨attributedProvenance⟩

/-! ## Redaction — inherited from the requirement scrubber

The envelope adds no new free text; provenance (author/change refs) is treated as
non-sensitive, like run ids on the agent axis. So redaction delegates to the
`Requirement` scrubber proved idempotent in the Snapshot adapter. -/

public instance : Kb.Redactable AttributedRequirement where
  redact a := { a with req := Kb.Redactable.redact a.req }
  redact_idempotent a := by
    simp only [Kb.Redactable.redact_idempotent]

/-! ## The faithful trusted-tier lift

Now `attrToItem` can be written the way the wiki's could — provenance projected from
the value's own content, boxed at `.proved`. No `sorry`, no vacuous witness. -/

@[expose] public def attrToItem (a : AttributedRequirement) :
    Kb.Item .proved AttributedRequirement AuthorRef :=
  { payload := a, provenance := a.provenance }

/-- The lifted item's id is the requirement's id. -/
public theorem attrToItem_id (a : AttributedRequirement) : (attrToItem a).id = a.req.id.value := by
  simp only [attrToItem, Kb.Item.id, Kb.Identified.idOf]

/-- The lifted item's provenance is exactly the attributed provenance — faithful,
non-empty, drawn from the value itself. -/
public theorem attrToItem_provenance (a : AttributedRequirement) :
    (attrToItem a).provenance = a.provenance := by
  simp only [attrToItem]

/-- The lifted item sits at the `.proved` tier, the spec store's assurance level. -/
public theorem attrToItem_proved (a : AttributedRequirement) :
    (Kb.admit (attrToItem a)).assurance = .proved := rfl

/-! ## Worked examples -/

private def ar : AttributedRequirement :=
  { req :=
      { id := ⟨"page.overview", by native_decide⟩
        shall := ⟨"show a summary dashboard", by native_decide⟩
        scenarios := ⟨#[{
          name := ⟨"load", by native_decide⟩
          whenText := ⟨"the page loads", by native_decide⟩
          thenText := ⟨"averages are shown", by native_decide⟩
          check := .executable }], by native_decide⟩ }
    provenance := ⟨#[⟨⟨"author:alice", by native_decide⟩⟩,
                    ⟨⟨"change:chg-launch", by native_decide⟩⟩], by native_decide⟩ }

-- Identity flows from the underlying requirement.
#guard (attrToItem ar).id == "page.overview"
-- Provenance is faithful and non-empty (two sources).
#guard (attrToItem ar).provenance.items.size == 2
#guard (attrToItem ar).provenance.items.map (·.value.value) == #["author:alice", "change:chg-launch"]
-- The item sits at the trusted tier.
#guard (Kb.admit (attrToItem ar)).assurance == Assurance.proved

end

end LeanSpec.KbAdapter