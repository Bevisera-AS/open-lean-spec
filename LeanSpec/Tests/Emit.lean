import LeanSpec.Emit
import LeanSpec.Codec.Snapshot
import LeanSpec.Demo.Archive

namespace LeanSpec.Tests.Emit

open LeanSpec
open LeanSpec.Demo.Archive

theorem emitIgnoresProof {s t : SpecSnapshot}
    (h : s.requirements = t.requirements) (hDes : s.designs = t.designs) :
    emitSnapshotSource s = emitSnapshotSource t :=
  emitSnapshotSource_of_requirements h hDes

theorem emptyRoundtrips : (parseSnapshotSource (emitSnapshotSource SpecSnapshot.empty)).isOk = true :=
  parse_emit_empty_isOk

open LeanSpec
open LeanSpec.Demo.Archive

def checks : Array (String × Bool) := #[
  ("theme snapshot roundtrips through Lean source",
    match parseSnapshotSource (emitSnapshotSource initialSnapshot) with
    | .ok s => s == initialSnapshot
    | .error _ => false),
  ("emission is deterministic",
    let src := emitSnapshotSource initialSnapshot
    match parseSnapshotSource src with
    | .ok s => emitSnapshotSource s == src
    | .error _ => false),
  ("generated header is required",
    match parseSnapshotSource "def snapshot : SpecSnapshot := { requirements := #[] }" with
    | .error (.illFormed "snapshot.lean" _) => true
    | _ => false),
  ("JSON snapshot remains readable as transport",
    match acceptSnapshot (encodeSnapshot initialSnapshot) with
    | .ok s => s == initialSnapshot
    | .error _ => false),
  ("designed snapshot roundtrips through Lean source",
    match parseSnapshotSource (emitSnapshotSource initialSnapshot) with
    | .ok s => s == initialSnapshot && !s.designs.isEmpty
    | .error _ => false)
]

end LeanSpec.Tests.Emit
