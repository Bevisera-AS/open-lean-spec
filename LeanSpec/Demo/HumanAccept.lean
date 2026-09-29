module

public import LeanSpec.Snapshot
public meta import LeanSpec.Snapshot

namespace LeanSpec.Demo.HumanAccept

open LeanSpec

public section

/-- Fresh SHALL: archive needs an explicit decision flag, not theme selection. -/
public def archiveRequiresHuman : Requirement := {
  id := ⟨"archive.requiresHuman", by native_decide⟩
  shall := ⟨"Archive merges a change only after ArchiveDecision.accepted; declined leaves the snapshot unchanged. The decision is a caller flag, not a verified identity.", by native_decide⟩
  scenarios := ⟨#[{
    name := ⟨"declined writes nothing", by native_decide⟩
    whenText := ⟨"archive is called with ArchiveDecision.declined", by native_decide⟩
    thenText := ⟨"the snapshot requirements are unchanged", by native_decide⟩
    check := .executable
  }], by native_decide⟩
}

public def humanAcceptChange : Change := {
  id := ⟨"add-archive-requires-human", by native_decide⟩
  why := ⟨"State the human archive gate as a requirement, not only a CLI flag.", by native_decide⟩
  deltas := ⟨#[.added archiveRequiresHuman], by native_decide⟩
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
