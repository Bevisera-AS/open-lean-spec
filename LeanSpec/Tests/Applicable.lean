import LeanSpec.Snapshot
import LeanSpec.Demo.Archive

namespace LeanSpec.Tests.Applicable

open LeanSpec
open LeanSpec.Demo.Archive
open LeanSpec.Demo.Theme

theorem ofEstablishesApply
    {s : SpecSnapshot} {c : Change} {ac : ApplicableChange s}
    (h : ApplicableChange.of s c = .ok ac) :
    s.applyDeltas ac.change.deltas.toArray = .ok ac.result :=
  ApplicableChange.of_sound h

theorem ofStoresChange
    {s : SpecSnapshot} {c : Change} {ac : ApplicableChange s}
    (h : ApplicableChange.of s c = .ok ac) :
    ac.change = c :=
  ApplicableChange.of_change h

theorem addedIsFreshPush
    {s : SpecSnapshot} {r : Requirement} {next : SpecSnapshot}
    (h : s.applyDelta (.added r) = .ok next) :
    s.has r.id.value = false ∧ next.requirements = s.requirements.push r :=
  SpecSnapshot.applyDelta_added h

theorem declinedDoesNotArchive (s : SpecSnapshot) (c : Change) :
    s.archive c .declined = .error .noHumanAccept :=
  SpecSnapshot.archive_declined s c

def checks : Array (String × Bool) := #[
  ("dark-mode change is applicable to the theme snapshot",
    match ApplicableChange.of initialSnapshot darkModeChange with
    | .ok ac => ac.result.has "theme.contrast" && ac.result.has "theme.selection"
    | .error _ => false),
  ("applicable archive accepted returns the stored result",
    match ApplicableChange.of initialSnapshot darkModeChange with
    | .ok ac =>
      match ac.archive .accepted with
      | .ok snap => snap == ac.result
      | .error _ => false
    | .error _ => false),
  ("applicable archive declined is noHumanAccept",
    match ApplicableChange.of initialSnapshot darkModeChange with
    | .ok ac =>
      match ac.archive .declined with
      | .error .noHumanAccept => true
      | _ => false
    | .error _ => false),
  ("duplicate add is not applicable",
    match ApplicableChange.of initialSnapshot {
      id := ⟨"dup", by native_decide⟩
      why := ⟨"already present", by native_decide⟩
      deltas := ⟨#[.added themeSelection], by native_decide⟩
    } with
    | .error (.apply (.duplicateId "theme.selection")) => true
    | _ => false),
  ("missing modified id is not applicable",
    match ApplicableChange.of initialSnapshot {
      id := ⟨"miss", by native_decide⟩
      why := ⟨"no such requirement", by native_decide⟩
      deltas := ⟨#[.modified {
        id := ⟨"theme.missing", by native_decide⟩
        shall := ⟨"gone", by native_decide⟩
        scenarios := themeSelection.scenarios
      }], by native_decide⟩
    } with
    | .error (.apply (.missingId "theme.missing")) => true
    | _ => false),
  ("apply is the stored result",
    match ApplicableChange.of initialSnapshot darkModeChange with
    | .ok ac => ApplicableChange.apply ac == ac.result
    | .error _ => false),
  ("accepted applicable archive is the stored result",
    match ApplicableChange.of initialSnapshot darkModeChange with
    | .ok ac =>
      match ac.archive .accepted with
      | .ok snap => snap == ac.result
      | .error _ => false
    | .error _ => false),
  ("added is a fresh push",
    match SpecSnapshot.empty.applyDelta (.added themeSelection) with
    | .ok next =>
      !SpecSnapshot.empty.has "theme.selection" &&
        next.requirements == SpecSnapshot.empty.requirements.push themeSelection &&
        next.has "theme.selection"
    | .error _ => false),
  ("rename preserves uniqueness",
    match ApplicableChange.of initialSnapshot {
      id := ⟨"rename-theme", by native_decide⟩
      why := ⟨"stable id", by native_decide⟩
      deltas := ⟨#[.renamed {
        frm := ⟨"theme.selection", by native_decide⟩
        to := ⟨"theme.mode", by native_decide⟩
        property := by native_decide
      }], by native_decide⟩
    } with
    | .ok ac =>
      decide (UniqueRequirementIds (ApplicableChange.apply ac).requirements) &&
        ac.result.has "theme.mode" && !ac.result.has "theme.selection"
    | .error _ => false)
]

end LeanSpec.Tests.Applicable
