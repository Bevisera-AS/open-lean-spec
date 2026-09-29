import LeanSpec.Snapshot
import LeanSpec.Demo.Theme

namespace LeanSpec.Tests.Snapshot

open LeanSpec
open LeanSpec.Demo.Theme

private def rejectsAt
    (expectedPath : String) (issue : ValidationIssue)
    (result : Except ValidationError SpecSnapshot) : Bool :=
  match result with
  | .error error => error.path == expectedPath && error.issue == issue
  | .ok _ => false

theorem ofProjectsRequirements
    {reqs : Array Requirement} {snapshot : SpecSnapshot}
    (h : SpecSnapshot.of "snapshot.requirements" reqs = .ok snapshot) :
    snapshot.requirements = reqs ∧ UniqueRequirementIds reqs ∧
      snapshot.designs = (#[] : Array DesignUnit) :=
  SpecSnapshot.of_sound h

theorem ofCompletes (snapshot : SpecSnapshot) :
    SpecSnapshot.ofDesigned "snapshot.requirements" snapshot.requirements snapshot.designs
      = .ok snapshot :=
  SpecSnapshot.of_complete snapshot "snapshot.requirements"

def checks : Array (String × Bool) := #[
  ("empty snapshot is unique", SpecSnapshot.empty.wellFormed),
  ("singleton snapshot is accepted",
    (SpecSnapshot.of "snapshot.requirements" #[themeSelection]).isOk),
  ("singleton snapshot roundtrips",
    match SpecSnapshot.of "snapshot.requirements" #[themeSelection] with
    | .ok snapshot => snapshot.requirements == #[themeSelection] && snapshot.designs.isEmpty
    | .error _ => false),
  ("duplicate ids keep their path",
    rejectsAt "snapshot.requirements" .duplicateIds
      (SpecSnapshot.of "snapshot.requirements" #[themeSelection, themeSelection])),
  ("designed snapshot links by id",
    match SpecSnapshot.ofDesigned "snapshot.requirements" #[themeSelection]
        #[themeSelectionDesign] with
    | .ok snapshot =>
        snapshot.findDesign? "theme.selection" == some themeSelectionDesign
    | .error _ => false),
  ("unlinked design keeps its path",
    match SpecSnapshot.ofDesigned "snapshot.requirements" #[themeSelection]
        #[{ themeSelectionDesign with id := ⟨"theme.missing", by native_decide⟩ }] with
    | .error error => error.issue == .unlinkedDesign
    | .ok _ => false),
  ("attachDesign refuses a missing requirement",
    match SpecSnapshot.empty.attachDesign themeSelectionDesign with
    | .error error => error.issue == .unlinkedDesign
    | .ok _ => false)
]

end LeanSpec.Tests.Snapshot
