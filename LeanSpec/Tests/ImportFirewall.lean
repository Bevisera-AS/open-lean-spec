import Lean.Data.Json

/-!
Import firewall. Tests are executables, not the spec library.

Three boundaries:

- The agent-facing library (`LeanSpec`, `LeanSpec.Core.*`, `LeanSpec.Logic.*`) imports
  only itself and `Lean`: never the process layer, the knowledge instance or the
  lean-kb package, so a workspace that imports `LeanSpec` builds Core, Logic and
  `Lean` and nothing more.
- `LeanJson` is a shared helper library: it sits below the spec types and must not
  import them, so the dependency stays one-directional.
- The knowledge core lives in the sibling package lean-kb (`LeanKb.*`, `LeanUtil`)
  and imports nothing from lean-spec, so a knowledge-base consumer can take it
  without the spec and process layers. lean-kb is lean-spec's only dependency: a
  workspace build fetches nothing else.
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

def isPrelude (mod : String) : Bool :=
  mod == "Lean" || mod.startsWith "Lean." || mod == "Init" || mod.startsWith "Init." ||
    mod == "Std" || mod.startsWith "Std."

/-- A shared helper library may not depend on the spec types. -/
def forbiddenInShared (mod : String) : Bool :=
  isSpecImport mod

/-- The agent-facing library may import only itself and `Lean`: never the process
layer, the knowledge instance, lean-kb (`LeanKb.*`, `LeanUtil`) or `LeanJson`. -/
def forbiddenInAgentLib (mod : String) : Bool :=
  !(mod == "LeanSpec" || mod.startsWith "LeanSpec.Core" || mod.startsWith "LeanSpec.Logic" ||
    isPrelude mod)

/-- The knowledge core (lean-kb) may not import anything of lean-spec: not the spec
library, not the process layer, not the knowledge instance, not `LeanJson`. -/
def forbiddenInKnowledgeCore (mod : String) : Bool :=
  mod.startsWith "LeanSpec" || mod == "LeanJson"

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

def assertNoForbiddenIn (label : String) (dir : System.FilePath)
    (forbidden : String → Bool) : IO Unit := do
  for f in ← System.FilePath.readDir dir do
    if f.path.extension == some "lean" then
      assertNoForbidden label f.path forbidden

def assertTrue (label : String) (condition : Bool) : IO Unit := do
  if !condition then
    throw <| IO.userError s!"test failed: {label}"

/-- The manifest's one dependency, lean-kb, and where its sources are: the `dir` of
a path dependency, else `.lake/packages/lean-kb`. -/
def leanKbDir : IO System.FilePath := do
  let raw ← IO.FS.readFile ⟨"lake-manifest.json"⟩
  let json ← IO.ofExcept (Lean.Json.parse raw)
  let packages ← IO.ofExcept (json.getObjValAs? (Array Lean.Json) "packages")
  assertTrue "lean-kb is the only dependency" (packages.size == 1)
  let pkg := packages[0]!
  let name ← IO.ofExcept (pkg.getObjValAs? String "name")
  assertTrue s!"the dependency is lean-kb, not {name}" (name == "«lean-kb»")
  match pkg.getObjValAs? String "type" with
  | .ok "path" => return ⟨← IO.ofExcept (pkg.getObjValAs? String "dir")⟩
  | _ => return ⟨".lake/packages/lean-kb"⟩

def check : IO Unit := do
  assertTrue "LeanSpec is a spec import" (isSpecImport "LeanSpec")
  assertTrue "LeanSpec.ProcessSkill is a spec import" (isSpecImport "LeanSpec.ProcessSkill")
  assertTrue "a longer name is not a spec import" (!isSpecImport "LeanSpecial")
  assertTrue "LeanUtil is not a spec import" (!isSpecImport "LeanUtil")
  assertTrue "import line"
    (importModule? "public import LeanSpec.ProcessSkill" == some "LeanSpec.ProcessSkill")
  assertTrue "ignore comments" (importModule? "-- import LeanSpec.ProcessSkill" == none)
  assertNoForbidden "LeanJson" ⟨"LeanJson.lean"⟩ forbiddenInShared
  assertTrue "process import is forbidden in the agent lib"
    (forbiddenInAgentLib "LeanSpec.ProcessSkill")
  assertTrue "lean-kb import is forbidden in the agent lib" (forbiddenInAgentLib "LeanKb.Kb")
  assertTrue "LeanUtil import is forbidden in the agent lib" (forbiddenInAgentLib "LeanUtil")
  assertTrue "Core import is allowed in the agent lib" (!forbiddenInAgentLib "LeanSpec.Core.Types")
  assertTrue "Lean import is allowed in the agent lib" (!forbiddenInAgentLib "Lean.Data.Json")
  assertNoForbidden "LeanSpec" ⟨"LeanSpec.lean"⟩ forbiddenInAgentLib
  assertNoForbidden "LeanSpec.Core" ⟨"LeanSpec/Core.lean"⟩ forbiddenInAgentLib
  assertNoForbiddenIn "LeanSpec.Core" ⟨"LeanSpec/Core"⟩ forbiddenInAgentLib
  assertNoForbidden "LeanSpec.Logic.Core" ⟨"LeanSpec/Logic/Core.lean"⟩ forbiddenInAgentLib
  assertNoForbiddenIn "LeanSpec.Logic.Demo" ⟨"LeanSpec/Logic/Demo"⟩ forbiddenInAgentLib
  assertNoForbiddenIn "LeanSpec.Spec" ⟨"LeanSpec/Spec"⟩ forbiddenInAgentLib
  assertTrue "spec import is forbidden in the knowledge core"
    (forbiddenInKnowledgeCore "LeanSpec.Reflection")
  assertTrue "LeanUtil is allowed in the knowledge core" (!forbiddenInKnowledgeCore "LeanUtil")
  let kb ← leanKbDir
  assertNoForbidden "LeanUtil" (kb / "LeanUtil.lean") forbiddenInKnowledgeCore
  assertNoForbidden "LeanKb" (kb / "LeanKb.lean") forbiddenInKnowledgeCore
  assertNoForbiddenIn "LeanKb" (kb / "LeanKb") forbiddenInKnowledgeCore

end ImportFirewall
