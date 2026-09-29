import LeanSpec

open LeanSpec
open LeanSpec.Workflow

def usage : String :=
  "usage: lean-spec (list-skillsets | boot-plan <token> | show-skillset <token> | decode-requirement | show-snapshot [path] | validate-change <file> [snapshot] | check-precedents <file> [snapshot] | archive --change <file> [--human] [--snapshot <path>])"

def fail (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return 1

def loadSnapshot (path : System.FilePath) : IO (Except String SpecSnapshot) := do
  if !(← path.pathExists) then
    return .error s!"no snapshot at {path}"
  match ← readSnapshot path with
  | .error e => return .error e.pretty
  | .ok s => return .ok s

def workingSnapshot : IO System.FilePath :=
  resolveWorkingSnapshotPath

def showSnapshotAt (path : System.FilePath) : IO UInt32 := do
  match ← loadSnapshot path with
  | .error d => fail d
  | .ok s => do
      if s.requirements.isEmpty then
        IO.println "(empty snapshot)"
      else
        IO.println (formatSnapshot s)
      return 0

def validateChangeAt (changePath snapPath : System.FilePath) : IO UInt32 := do
  if !(← changePath.pathExists) then
    fail s!"no change file at {changePath}"
  else
    match ← loadSnapshot snapPath with
    | .error d => fail d
    | .ok snap =>
        match ← readChange changePath with
        | .error e => fail e.pretty
        | .ok c =>
            match snap.checkChange c with
            | .error e => fail e.pretty
            | .ok () => do
                IO.println s!"ok {c.id.value}"
                return 0

/-- Decode a precedented-change file, confirm it applies, and gate coherence of
its recorded precedents against the snapshot. Read-only; writes nothing. -/
def checkPrecedentsAt (pcPath snapPath : System.FilePath) : IO UInt32 := do
  if !(← pcPath.pathExists) then
    fail s!"no file at {pcPath}"
  else
    match ← loadSnapshot snapPath with
    | .error d => fail d
    | .ok snap => do
        let raw ← IO.FS.readFile pcPath
        match acceptPrecedentedChangeString raw with
        | .error e => fail e.pretty
        | .ok pc =>
            match snap.checkChange pc.change with
            | .error e => fail e.pretty
            | .ok () =>
                if pc.coherentIn snap then do
                  IO.println
                    s!"ok {pc.change.id.value} ({pc.precedents.size} precedent(s) coherent)"
                  return 0
                else
                  fail s!"incoherent precedents for {pc.change.id.value}"

structure ArchiveCli where
  changeFile : String
  human : Bool
  snapshot? : Option String

def parseArchive (args : List String) : Except String ArchiveCli :=
  let rec go (change? : Option String) (human : Bool) (snap? : Option String) :
      List String → Except String ArchiveCli
    | [] =>
      match change? with
      | none => .error "archive requires --change <file>"
      | some file =>
        .ok { changeFile := file, human, snapshot? := snap? }
    | "--human" :: rest => go change? true snap? rest
    | "--change" :: file :: rest => go (some file) human snap? rest
    | "--change" :: [] => .error "archive --change needs a file"
    | "--snapshot" :: path :: rest => go change? human (some path) rest
    | "--snapshot" :: [] => .error "archive --snapshot needs a path"
    | other :: _ => .error s!"archive: unknown argument `{other}`"
  go none false none args

def archiveAt (changePath snapPath : System.FilePath) : IO UInt32 := do
  if !(← changePath.pathExists) then
    fail s!"no change file at {changePath}"
  else
    match ← loadSnapshot snapPath with
    | .error d => fail d
    | .ok snap =>
        match ← readChange changePath with
        | .error e => fail e.pretty
        | .ok c =>
            match snap.checkChange c with
            | .error e => fail e.pretty
            | .ok () =>
                match ← archiveChangeFile snapPath c .accepted with
                | .error d => fail d
                | .ok _ => do
                    IO.println s!"archived {c.id.value}"
                    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list-skillsets"] =>
      for ss in catalog.skillsets do
        IO.println s!"{ss.id.value} token={ss.pasteToken.value} role={ss.roleSkill.value}"
      return 0
  | ["boot-plan", token] =>
      match catalog.findSkillset? token with
      | some ss =>
          for id in ss.boot.toArray do
            IO.println id.value
          return 0
      | none => fail s!"skillset not found: {token}"
  | ["show-skillset", token] =>
      match catalog.findSkillset? token with
      | some ss =>
          IO.println s!"# {ss.id.value}"
          IO.println s!"paste-token: {ss.pasteToken.value}"
          IO.println s!"mission: {ss.mission.value}"
          IO.println s!"role-skill: {ss.roleSkill.value}"
          IO.println "boot:"
          for id in ss.boot.toArray do
            IO.println s!"  - {id.value}"
          return 0
      | none => fail s!"skillset not found: {token}"
  | ["decode-requirement"] => do
      let raw ← (← IO.getStdin).readToEnd
      match acceptRequirementString raw with
      | .ok r =>
          IO.println s!"ok {r.id.value}"
          return 0
      | .error e => fail e.pretty
  | ["show-snapshot"] => do
      showSnapshotAt (← workingSnapshot)
  | ["show-snapshot", path] =>
      showSnapshotAt ⟨path⟩
  | ["validate-change", file] => do
      validateChangeAt ⟨file⟩ (← workingSnapshot)
  | ["validate-change", file, snap] =>
      validateChangeAt ⟨file⟩ ⟨snap⟩
  | ["check-precedents", file] => do
      checkPrecedentsAt ⟨file⟩ (← workingSnapshot)
  | ["check-precedents", file, snap] =>
      checkPrecedentsAt ⟨file⟩ ⟨snap⟩
  | "archive" :: rest =>
      match parseArchive rest with
      | .error d => fail d
      | .ok a =>
          if !a.human then
            fail "noHumanAccept"
          else do
            -- `--human` is ArchiveDecision.accepted, not a build or identity check.
            let snap ←
              match a.snapshot? with
              | some p => pure ⟨p⟩
              | none => workingSnapshot
            archiveAt ⟨a.changeFile⟩ snap
  | "export-skills" :: _ =>
      fail "removed: skills are Lean ProcessSkill values; this library does not emit SKILL.md"
  | _ => fail usage
