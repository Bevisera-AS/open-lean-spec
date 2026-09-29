module

public import Lean.Data.Json
public import LeanJson
public import LeanSpec.Codec.Snapshot
public import LeanSpec.Codec.Change
public import LeanSpec.Emit
public meta import LeanJson
public meta import LeanSpec.Emit

namespace LeanSpec

open Lean
open LeanJson

public section

/-- Working snapshot directory. Not a git object; this library never commits it. -/
public def defaultStoreDir : System.FilePath := ⟨".lean-spec"⟩

/-- Canonical spec store. JSON remains transport for extract/change files. -/
public def defaultSnapshotPath : System.FilePath := defaultStoreDir / "Snapshot.lean"

/-- Legacy JSON snapshot; read for one-time migration only. -/
public def defaultJsonSnapshotPath : System.FilePath := defaultStoreDir / "snapshot.json"

public def writeFileAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  match path.parent with
  | none => pure ()
  | some dir => IO.FS.createDirAll dir
  let tmp : System.FilePath := ⟨path.toString ++ ".tmp"⟩
  IO.FS.writeFile tmp contents
  IO.FS.rename tmp path

public def isJsonSnapshotPath (path : System.FilePath) : Bool :=
  path.toString.endsWith ".json"

public def writeSnapshot (path : System.FilePath) (s : SpecSnapshot) : IO Unit :=
  if isJsonSnapshotPath path then
    writeFileAtomic path (Json.pretty (encodeSnapshot s))
  else
    writeFileAtomic path (emitSnapshotSource s)

public def readSnapshot (path : System.FilePath) : IO (Except LeanJson.DecodeError SpecSnapshot) := do
  let raw ← IO.FS.readFile path
  if isJsonSnapshotPath path then
    pure (acceptSnapshotString raw)
  else
    pure (parseSnapshotSource raw)

/-- Prefer the Lean store; fall back to legacy JSON if the Lean file is absent. -/
public def resolveWorkingSnapshotPath : IO System.FilePath := do
  if ← defaultSnapshotPath.pathExists then
    return defaultSnapshotPath
  else if ← defaultJsonSnapshotPath.pathExists then
    return defaultJsonSnapshotPath
  else
    return defaultSnapshotPath

public def writeChange (path : System.FilePath) (c : Change) : IO Unit :=
  writeFileAtomic path (Json.pretty (encodeChange c))

public def readChange (path : System.FilePath) : IO (Except LeanJson.DecodeError Change) := do
  let raw ← IO.FS.readFile path
  match parseJson raw with
  | .error e => pure (.error e)
  | .ok j => pure (decodeChange j)

/-- Apply a change to the snapshot file. `declined` returns `noHumanAccept` and does not write.
The write is `writeFileAtomic` (tmp + rename); crash-between-rename is not a kernel theorem. -/
public def archiveChangeFile (snapPath : System.FilePath) (c : Change) (gate : ArchiveDecision) :
    IO (Except String SpecSnapshot) := do
  match ← readSnapshot snapPath with
  | .error e => pure (.error e.pretty)
  | .ok s =>
    match s.archive c gate with
    | .error e => pure (.error e.pretty)
    | .ok next => do
      writeSnapshot snapPath next
      pure (.ok next)

end

end LeanSpec
