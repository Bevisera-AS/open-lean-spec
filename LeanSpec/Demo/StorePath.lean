module

public import LeanSpec.Store
public meta import LeanSpec.Store

namespace LeanSpec.Demo.StorePath

open LeanSpec

public section

/-- Experimental P1.5 change: one SHALL about where current spec lives. -/
public def workingSnapshotPath : Requirement := {
  id := ⟨"store.workingSnapshotPath", by decide +kernel⟩
  shall := ⟨"The working spec snapshot is the local file `.lean-spec/Snapshot.lean`; writeSnapshot does not commit git.", by decide +kernel⟩
  scenarios := ⟨#[{
    name := ⟨"default path is local", by decide +kernel⟩
    whenText := ⟨"a caller asks for the default snapshot path", by decide +kernel⟩
    thenText := ⟨"the path is `.lean-spec/Snapshot.lean`", by decide +kernel⟩
    check := .executable
  }, {
    name := ⟨"store is not a git object", by decide +kernel⟩
    whenText := ⟨"writeSnapshot writes a snapshot", by decide +kernel⟩
    thenText := ⟨"the path is not under `.git/`", by decide +kernel⟩
    check := .executable
  }], by decide +kernel⟩
}

public def storePathChange : Change := {
  id := ⟨"add-working-snapshot-path", by decide +kernel⟩
  why := ⟨"Agents must know where current spec lives without treating git as the store.", by decide +kernel⟩
  deltas := ⟨#[.added workingSnapshotPath], by decide +kernel⟩
}

#guard workingSnapshotPath.wellFormed
#guard storePathChange.wellFormed
#guard defaultSnapshotPath.toString == ".lean-spec/Snapshot.lean"
#guard !(defaultSnapshotPath.toString.contains ".git")

end

end LeanSpec.Demo.StorePath
