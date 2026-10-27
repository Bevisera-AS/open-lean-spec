/-!
Import firewall. Tests are executables, not the spec library.

`LeanUtil` and `LeanJson` are shared helper libraries: they sit below the spec
types and must not import them, so the dependency stays one-directional.
-/

namespace ImportFirewall

def importModule? (line : String) : Option String :=
  let t := line.trimAscii.copy
  let rest :=
    if t.startsWith "public meta import " then (t.dropPrefix "public meta import ").copy
    else if t.startsWith "public import " then (t.dropPrefix "public import ").copy
    else if t.startsWith "import " then (t.dropPrefix "import ").copy
    else ""
  if rest.isEmpty then none
  else some (String.ofList (rest.toList.takeWhile (fun c => !c.isWhitespace)))

def isSpecImport (mod : String) : Bool :=
  mod == "LeanSpec" || mod.startsWith "LeanSpec."

/-- A shared helper library may not depend on the spec types. -/
def forbiddenInShared (mod : String) : Bool :=
  isSpecImport mod

/-- The agent-facing library (`LeanSpec`, `LeanSpec.Core.*`, `LeanSpec.Logic.*`)
may import only itself: never the process or knowledge layers, so a workspace
that imports `LeanSpec` builds Core, Logic and `Lean` and nothing more. -/
def forbiddenInAgentLib (mod : String) : Bool :=
  isSpecImport mod && mod != "LeanSpec" &&
    !(mod.startsWith "LeanSpec.Core") && !(mod.startsWith "LeanSpec.Logic")

def importsIn (path : System.FilePath) : IO (Array String) := do
  let raw ← IO.FS.readFile path
  let mut acc : Array String := #[]
  for line in raw.splitOn "\n" do
    match importModule? line with
    | some m => acc := acc.push m
    | none => pure ()
  return acc

def assertNoForbidden (label : String) (path : System.FilePath)
    (forbidden : String → Bool) : IO Unit := do
  for mod in ← importsIn path do
    if forbidden mod then
      throw <| IO.userError s!"test failed: {label} {path} imports {mod}"

def assertTrue (label : String) (condition : Bool) : IO Unit := do
  if !condition then
    throw <| IO.userError s!"test failed: {label}"

def check : IO Unit := do
  assertTrue "LeanSpec is a spec import" (isSpecImport "LeanSpec")
  assertTrue "LeanSpec.ProcessSkill is a spec import" (isSpecImport "LeanSpec.ProcessSkill")
  assertTrue "a longer name is not a spec import" (!isSpecImport "LeanSpecial")
  assertTrue "LeanUtil is not a spec import" (!isSpecImport "LeanUtil")
  assertTrue "import line"
    (importModule? "public import LeanSpec.ProcessSkill" == some "LeanSpec.ProcessSkill")
  assertTrue "ignore comments" (importModule? "-- import LeanSpec.ProcessSkill" == none)
  assertNoForbidden "LeanUtil" ⟨"LeanUtil.lean"⟩ forbiddenInShared
  assertNoForbidden "LeanJson" ⟨"LeanJson.lean"⟩ forbiddenInShared
  assertTrue "process import is forbidden in the agent lib"
    (forbiddenInAgentLib "LeanSpec.ProcessSkill")
  assertTrue "Core import is allowed in the agent lib" (!forbiddenInAgentLib "LeanSpec.Core.Types")
  assertNoForbidden "LeanSpec" ⟨"LeanSpec.lean"⟩ forbiddenInAgentLib
  assertNoForbidden "LeanSpec.Core" ⟨"LeanSpec/Core.lean"⟩ forbiddenInAgentLib
  for f in ← System.FilePath.readDir ⟨"LeanSpec/Core"⟩ do
    if f.path.extension == some "lean" then
      assertNoForbidden "LeanSpec.Core" f.path forbiddenInAgentLib
  assertNoForbidden "LeanSpec.Logic.Core" ⟨"LeanSpec/Logic/Core.lean"⟩ forbiddenInAgentLib
  for f in ← System.FilePath.readDir ⟨"LeanSpec/Logic/Demo"⟩ do
    if f.path.extension == some "lean" then
      assertNoForbidden "LeanSpec.Logic.Demo" f.path forbiddenInAgentLib

end ImportFirewall
