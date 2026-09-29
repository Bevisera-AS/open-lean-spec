module

public import LeanSpec.Kb
public import LeanSpec.Snapshot
public import LeanSpec.KbAdapter.Snapshot
public meta import LeanSpec.Kb
public meta import LeanSpec.Snapshot
public meta import LeanSpec.KbAdapter.Snapshot
public meta import LeanUtil

/-!
# Attributing the archive gate: recording *who* accepted *what*

The `SpecSnapshot` adapter's second finding: `ArchiveDecision.accepted` is a bare
boolean (the CLI `--human` flag). It blocks when declined, but it cannot testify to
*who* accepted the change or *what* content they saw. The generic core already has
the richer shape — `Obligation.toProved` carries a `Kb.Gate { approver, contentHash }`,
and `Kb.toProved_carries_gate` proves every promotion to the trusted tier records
both. This module brings that accountability to the spec axis.

As with `AttributedRequirement`, we do **not** mutate `ArchiveDecision` (it flows
through the CLI, `Query`, codecs, and tests — large blast radius). Attribution is a
proof-carrying envelope: `AttributedDecision` is `declined` or
`accepted (gate : Kb.Gate)`. `attributedArchive` projects to the existing
`ApplicableChange.archive`, so behaviour is *identical* to today — but a successful
archive now carries the gate, and we prove it:

* `attributedArchive_declined` — declined never produces a snapshot (unchanged).
* `attributedArchive_ok_carries_gate` — **the accountability theorem**: a successful
  attributed archive was authorised by a specific `Gate`, so the caller can log
  `(approver, contentHash)` at exactly this transition. This is the spec-axis
  instance of `Kb.toProved_carries_gate`, and it closes the turn-1 gate finding.

The projection theorem `attributedArchive_eq_archive` witnesses that this is a
faithful envelope: attributing the gate changes nothing about *which* snapshot is
produced, only that the acceptance is now attributed.
-/

namespace LeanSpec.KbAdapter

open LeanSpec
open LeanSpec.Kb

public section

/-- An archive decision that, when it accepts, records the attributed gate that
authorised it. `declined` needs nothing; `accepted` carries who + what. Envelope
over the bare `ArchiveDecision`, mirroring `AttributedRequirement` over
`Requirement`. -/
public inductive AttributedDecision where
  | declined
  | accepted (gate : Kb.Gate)
  deriving Repr

/-- Project an attributed decision to the plain gate the existing archive consumes.
Accepting-with-a-gate is still just accepting; the gate is retained on the envelope,
not in the projection. -/
@[expose] public def AttributedDecision.toPlain : AttributedDecision → ArchiveDecision
  | .declined => .declined
  | .accepted _ => .accepted

/-- Archive a change under an attributed decision. Delegates to the existing
`ApplicableChange.archive` via the projection, so the produced snapshot is exactly
what today's gate produces. -/
@[expose] public def attributedArchive {s : SpecSnapshot} (c : ApplicableChange s)
    (d : AttributedDecision) : Except ArchiveError SpecSnapshot :=
  ApplicableChange.archive c d.toPlain

/-- **Faithful envelope.** Attributing the gate does not change which snapshot the
archive yields — it is the ordinary archive under the projected decision. -/
public theorem attributedArchive_eq_archive {s : SpecSnapshot} (c : ApplicableChange s)
    (d : AttributedDecision) :
    attributedArchive c d = ApplicableChange.archive c d.toPlain := rfl

/-- A declined attributed archive never produces a snapshot — unchanged from the
bare gate. -/
public theorem attributedArchive_declined {s : SpecSnapshot} (c : ApplicableChange s) :
    attributedArchive c .declined = .error .noHumanAccept := by
  simp only [attributedArchive, AttributedDecision.toPlain]
  exact ApplicableChange.archive_declined c

/-- An accepted attributed archive yields exactly the applied snapshot. -/
public theorem attributedArchive_accepted {s : SpecSnapshot} (c : ApplicableChange s)
    (g : Kb.Gate) :
    attributedArchive c (.accepted g) = .ok (ApplicableChange.apply c) := by
  simp only [attributedArchive, AttributedDecision.toPlain]
  exact ApplicableChange.archive_accepted c

/-- **The accountability theorem.** A successful attributed archive was authorised
by a specific decision, and that decision is an `accepted g` carrying an attributed
gate — so the caller can testify to *who* (`g.approver`) accepted *what*
(`g.contentHash`). This is the spec-axis instance of `Kb.toProved_carries_gate`:
reaching the trusted tier records its authorisation. A declined decision provably
cannot reach here. -/
public theorem attributedArchive_ok_carries_gate {s : SpecSnapshot} (c : ApplicableChange s)
    {d : AttributedDecision} {s' : SpecSnapshot}
    (h : attributedArchive c d = .ok s') :
    ∃ g : Kb.Gate, d = .accepted g := by
  cases d with
  | declined =>
    -- declined yields `.error`, contradicting `= .ok s'`
    rw [attributedArchive_declined] at h
    exact absurd h (by simp)
  | accepted g => exact ⟨g, rfl⟩

/-- Corollary: the approver and content hash of a successful archive are available
for the audit log. Extracts the gate the acceptance carried. -/
public def AttributedDecision.gate? : AttributedDecision → Option Kb.Gate
  | .declined => none
  | .accepted g => some g

/-- A successful attributed archive has a recorded gate (its `approver`/`contentHash`
are loggable). -/
public theorem attributedArchive_ok_has_gate {s : SpecSnapshot} (c : ApplicableChange s)
    {d : AttributedDecision} {s' : SpecSnapshot}
    (h : attributedArchive c d = .ok s') :
    d.gate?.isSome = true := by
  obtain ⟨g, rfl⟩ := attributedArchive_ok_carries_gate c h
  rfl

/-! ## Worked examples -/

private def theGate : Kb.Gate :=
  { approver := ⟨"alice", by native_decide⟩
    contentHash := ⟨"sha256:abcd1234", by native_decide⟩ }

-- Declined projects to a plain decline and produces no snapshot.
#guard (AttributedDecision.declined.toPlain == ArchiveDecision.declined)
-- Accepted-with-gate projects to a plain accept.
#guard ((AttributedDecision.accepted theGate).toPlain == ArchiveDecision.accepted)
-- The gate is retrievable for the audit log from an accepted decision.
#guard match (AttributedDecision.accepted theGate).gate? with
  | some g => g.approver.value == "alice" && g.contentHash.value == "sha256:abcd1234"
  | none => false
-- Declined carries no gate.
#guard (AttributedDecision.declined.gate?).isNone

end

end LeanSpec.KbAdapter