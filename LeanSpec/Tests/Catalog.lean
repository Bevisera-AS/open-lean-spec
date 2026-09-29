import LeanSpec.Skillset
import LeanSpec.Workflow.Catalog
import LeanSpec.Workflow.BootClosure

namespace LeanSpec.Tests.Catalog

open LeanSpec
open LeanSpec.Workflow

private def rejectsAt
    (expectedPath : String) (issue : ValidationIssue)
    (result : Except ValidationError Catalog) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == issue
  | .ok _ => false

theorem ofProjectsCatalog
    {skills : Array ProcessSkill} {skillsets : Array Skillset} {catalog : Catalog}
    (h : Catalog.of "catalog" skills skillsets = .ok catalog) :
    catalog.skills = skills ∧ catalog.skillsets = skillsets :=
  let ⟨hs, hss, _, _, _, _⟩ := Catalog.of_sound h
  ⟨hs, hss⟩

theorem ofCompletes (catalog : Catalog) :
    Catalog.of "catalog" catalog.skills catalog.skillsets = .ok catalog :=
  Catalog.of_complete catalog "catalog"

theorem errorsEmpty (catalog : Catalog) : catalog.errors = #[] :=
  Catalog.errors_empty catalog

def checks : Array (String × Bool) := #[
  ("spec-change catalog is accepted",
    (Catalog.of "catalog" catalog.skills catalog.skillsets).isOk),
  ("spec-change catalog roundtrips",
    match Catalog.of "catalog" catalog.skills catalog.skillsets with
    | .ok c => c.skills == catalog.skills && c.skillsets == catalog.skillsets && c.errors.isEmpty
    | .error _ => false),
  ("duplicate skill ids keep their path",
    rejectsAt "catalog.skills" .duplicateIds
      (Catalog.of "catalog" #[proposeChange, proposeChange] #[])),
  ("duplicate skillset ids keep their path",
    rejectsAt "catalog.skillsets" .duplicateIds
      (Catalog.of "catalog" catalog.skills #[specChange, specChange])),
  ("unregistered boot skill keeps its path",
    rejectsAt "catalog.skillsets" .unregisteredSkill
      (Catalog.of "catalog" #[proposeChange] #[specChange])),
  -- WI1.2: dependency-graph invariants on requires.
  ("a real requires edge to a registered skill is accepted",
    -- skillExec requires humanGates; both are in the catalog. No skillsets, so
    -- boot registration is vacuous — this isolates the requires check.
    (Catalog.of "catalog"
      #[{ skillExec with requires := #[humanGates.id] }, humanGates] #[]).isOk),
  ("a requires edge to an unregistered skill is refused",
    rejectsAt "catalog.skills.requires" .unregisteredSkill
      (Catalog.of "catalog"
        #[{ skillExec with requires := #[proposeChange.id] }] #[])),
  ("a self-cycle in requires is refused",
    rejectsAt "catalog.skills.requires" .requiresCycle
      (Catalog.of "catalog"
        #[{ skillExec with requires := #[skillExec.id] }] #[]))
]

/-! ## Work item 2 — boot-closure properties (validated on the concrete catalog)

The `specChange` skillset boots 7 skills with no `requires` edges yet, so the
closure equals the declared boot id-set. These guards check properties 1–4 on the
real catalog; property 5 (determinism) is the proved `bootClosure_congr`. -/

private def closureIds : Array String := catalog.bootClosureIds specChange
private def bootIds : Array String := specChange.boot.toArray.map (·.value)

-- Property 1: every declared boot id is in the closure.
#guard bootIds.all (fun id => closureIds.contains id)
-- Property 4: the role skill is in the closure.
#guard closureIds.contains roleSpecifier.id.value
-- Property 3: the closure has no duplicate id.
#guard closureIds.toList.Nodup
-- Property 2 (transitive, vacuous here — no edges): closure equals the boot id-set,
-- so nothing beyond boot leaked in and nothing was dropped.
#guard sameIdSet closureIds bootIds
-- The skill-level closure resolves every id to a registered skill.
#guard (catalog.bootClosure specChange).size == bootIds.size

end LeanSpec.Tests.Catalog
