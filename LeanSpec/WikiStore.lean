module

public import LeanSpec.Store
public import LeanSpec.Codec.Reflection
public meta import LeanJson

/-!
# IO persistence for the Wiki store

The agent-experience `Wiki` on disk. Unlike `SpecSnapshot` (which has a `.lean`
source emit — it is authored, human knowledge), the Wiki is JSON only: reflections
are *provisional* agent knowledge, a transport record, not source. Like the spec
store, this library never commits the file.

`recordReflectionFile` is the IO analogue of the maintainer fold: load (or start
empty), consolidate via `Wiki.record`, write back atomically. Fail-closed on read:
an absent file is the empty store, but a *malformed* file errors rather than
silently resetting — a corrupt Wiki must not be overwritten with a blank one.
-/

namespace LeanSpec

open Lean
open LeanJson

public section

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
