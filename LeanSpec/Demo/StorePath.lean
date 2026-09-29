module

public import LeanSpec.Store
public meta import LeanSpec.Store

namespace LeanSpec.Demo.StorePath

open LeanSpec

public section

/-- Experimental P1.5 change: one SHALL about where current spec lives. -/
public def workingSnapshotPath : Requirement := {
  id := ⟨"store.workingSnapshotPath", by native_decide⟩
  shall := ⟨"The working spec snapshot is the local file `.lean-spec/Snapshot.lean`; writeSnapshot does not commit git.", by native_decide⟩
  scenarios := ⟨#[{
    name := ⟨"default path is local", by native_decide⟩
    whenText := ⟨"a caller asks for the default snapshot path", by native_decide⟩
    thenText := ⟨"the path is `.lean-spec/Snapshot.lean`", by native_decide⟩
    check := .executable
  }, {
    name := ⟨"store is not a git object", by native_decide⟩
    whenText := ⟨"writeSnapshot writes a snapshot", by native_decide⟩
    thenText := ⟨"the path is not under `.git/`", by native_decide⟩
    check := .executable
  }], by native_decide⟩
}

public def storePathChange : Change := {
  id := ⟨"add-working-snapshot-path", by native_decide⟩
  why := ⟨"Agents must know where current spec lives without treating git as the store.", by native_decide⟩
  deltas := ⟨#[.added workingSnapshotPath], by native_decide⟩
}

#guard workingSnapshotPath.wellFormed
#guard storePathChange.wellFormed
#guard defaultSnapshotPath.toString == ".lean-spec/Snapshot.lean"
#guard !(defaultSnapshotPath.toString.contains ".git")

end

end LeanSpec.Demo.StorePath
