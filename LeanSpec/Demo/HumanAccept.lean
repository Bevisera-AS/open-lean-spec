module

public import LeanSpec.Snapshot
public meta import LeanSpec.Snapshot

namespace LeanSpec.Demo.HumanAccept

open LeanSpec

public section

/-- Fresh SHALL: archive needs an explicit decision flag, not theme selection. -/
public def archiveRequiresHuman : Requirement := {
  id := ⟨"archive.requiresHuman", by decide +kernel⟩
  shall := ⟨"Archive merges a change only after ArchiveDecision.accepted; declined leaves the snapshot unchanged. The decision is a caller flag, not a verified identity.", by decide +kernel⟩
  scenarios := ⟨#[{
    name := ⟨"declined writes nothing", by decide +kernel⟩
    whenText := ⟨"archive is called with ArchiveDecision.declined", by decide +kernel⟩
    thenText := ⟨"the snapshot requirements are unchanged", by decide +kernel⟩
    check := .executable
  }], by decide +kernel⟩
}

public def humanAcceptChange : Change := {
  id := ⟨"add-archive-requires-human", by decide +kernel⟩
  why := ⟨"State the human archive gate as a requirement, not only a CLI flag.", by decide +kernel⟩
  deltas := ⟨#[.added archiveRequiresHuman], by decide +kernel⟩
}

public def emptySnapshot : SpecSnapshot := SpecSnapshot.empty

#guard archiveRequiresHuman.wellFormed
#guard humanAcceptChange.wellFormed
#guard
  match emptySnapshot.archive humanAcceptChange .declined with
  | .error .noHumanAccept => emptySnapshot.requirements.isEmpty
  | _ => false
#guard
  match emptySnapshot.archive humanAcceptChange .accepted with
  | .ok snap => snap.has "archive.requiresHuman"
  | .error _ => false

end

end LeanSpec.Demo.HumanAccept
