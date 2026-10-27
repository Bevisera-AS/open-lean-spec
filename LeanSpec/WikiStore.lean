module

public import LeanSpec.Codec.Reflection
public meta import LeanJson

/-!
# IO persistence for the Wiki store

The agent-experience `Wiki` on disk. Requirements are Lean source
(`LeanSpec.Logic`); the Wiki is JSON only: reflections are *provisional* agent
knowledge, a transport record, not source. This library never commits the file.

`recordReflectionFile` is the IO analogue of the maintainer fold: load (or start
empty), consolidate via `Wiki.record`, write back atomically. Fail-closed on read:
an absent file is the empty store, but a *malformed* file errors rather than
silently resetting — a corrupt Wiki must not be overwritten with a blank one.
-/

namespace LeanSpec

open Lean
open LeanJson

public section

/-- Local working directory. Not a git object; this library never commits it. -/
public def defaultStoreDir : System.FilePath := ⟨".lean-spec"⟩

public def writeFileAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  match path.parent with
  | none => pure ()
  | some dir => IO.FS.createDirAll dir
  let tmp : System.FilePath := ⟨path.toString ++ ".tmp"⟩
  IO.FS.writeFile tmp contents
  IO.FS.rename tmp path

/-- Working Wiki store path. Agent-axis, JSON only, not a git object. -/
public def defaultWikiPath : System.FilePath := defaultStoreDir / "wiki.json"

public def writeWiki (path : System.FilePath) (w : Wiki) : IO Unit :=
  writeFileAtomic path (Json.pretty (encodeWiki w))

/-- Read a Wiki from disk. A malformed file is an error; an absent file is not
handled here — see `loadWiki`. -/
public def readWiki (path : System.FilePath) : IO (Except LeanJson.DecodeError Wiki) := do
  let raw ← IO.FS.readFile path
  pure (acceptWikiString raw)

/-- Load the Wiki, treating an absent file as the empty store (the store starts
empty). A present-but-malformed file still errors — fail-closed, not silently
reset to blank. -/
public def loadWiki (path : System.FilePath) : IO (Except String Wiki) := do
  if ← path.pathExists then
    match ← readWiki path with
    | .ok w => pure (.ok w)
    | .error e => pure (.error e.pretty)
  else
    pure (.ok ({} : Wiki))

/-- Record a reflection into the on-disk Wiki: load (or start empty), consolidate
via `Wiki.record`, and write back atomically (tmp + rename). The IO analogue of the
maintainer fold. A malformed existing store aborts without overwriting. -/
public def recordReflectionFile (path : System.FilePath) (r : Reflection) :
    IO (Except String Wiki) := do
  match ← loadWiki path with
  | .error e => pure (.error e)
  | .ok w =>
    let next := w.record r
    writeWiki path next
    pure (.ok next)

end

end LeanSpec
