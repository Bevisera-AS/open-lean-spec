module

public import LeanUtil

/-!
# WikiAccess: the closed capability for agent-knowledge operations

Generic (library-owned) capability governing who may read, maintain, or propose a
promotion from the agent-experience store. The mapping from principals/authorities
to a `WikiAccess` level is **downstream policy** (a company pack);
this module only defines the capability, its order, and the gate predicates.

Design: `docs/lw0-agent-knowledge-governance-design.md`.

Levels are totally ordered by increasing capability:

    none < readEffective < maintain < promoteCandidate

- `readEffective`  — may read `effectiveByKind`; cannot write.
- `maintain`       — may run the maintainer fold (`Wiki.record`); implies read.
- `promoteCandidate` — may *propose* a promotion into the human gate; implies maintain.

`promoteCandidate` is proposal authority only. Acceptance stays a human gate
(`SpecSnapshot.archiveWithReflections`), unchanged — the valve remains singular.
-/

namespace LeanSpec

public section

/-- Closed capability for agent-knowledge operations. A typo cannot inhabit it. -/
public inductive WikiAccess where
  | «none»
  | readEffective
  | maintain
  | promoteCandidate
  deriving Repr, BEq, DecidableEq

namespace WikiAccess

/-- Rank in the capability order. Higher rank ⇒ strictly more capability. -/
public def rank : WikiAccess → Nat
  | .«none» => 0
  | .readEffective => 1
  | .maintain => 2
  | .promoteCandidate => 3

/-- `have` is at least as capable as `need`. The generic gate predicate. -/
public def atLeast (have_ need : WikiAccess) : Bool := need.rank ≤ have_.rank

/-- May read the effective readback. -/
public def canRead (a : WikiAccess) : Bool := a.atLeast .readEffective

/-- May run the maintainer fold (`Wiki.record`). -/
public def canMaintain (a : WikiAccess) : Bool := a.atLeast .maintain

/-- May propose a promotion into the human gate. -/
public def canPropose (a : WikiAccess) : Bool := a.atLeast .promoteCandidate

/-! ## Order facts used by the gate proofs -/

/-- `atLeast` is reflexive: any level is at least itself. -/
public theorem atLeast_refl (a : WikiAccess) : a.atLeast a = true := by
  simp [atLeast]

/-- Proposing implies maintaining implies reading (capability inclusion). -/
public theorem canPropose_canMaintain {a : WikiAccess} (h : a.canPropose = true) :
    a.canMaintain = true := by
  cases a <;> simp_all [canPropose, canMaintain, atLeast, rank]

public theorem canMaintain_canRead {a : WikiAccess} (h : a.canMaintain = true) :
    a.canRead = true := by
  cases a <;> simp_all [canMaintain, canRead, atLeast, rank]

end WikiAccess

end

/-! ## Worked examples -/

-- The order holds end to end.
#guard WikiAccess.«none».atLeast .«none»
#guard !WikiAccess.«none».canRead
#guard WikiAccess.readEffective.canRead && !WikiAccess.readEffective.canMaintain
#guard WikiAccess.maintain.canMaintain && WikiAccess.maintain.canRead
#guard WikiAccess.maintain.canMaintain && !WikiAccess.maintain.canPropose
#guard WikiAccess.promoteCandidate.canPropose
-- Capability inclusion: proposing implies maintaining implies reading.
#guard WikiAccess.promoteCandidate.canMaintain && WikiAccess.promoteCandidate.canRead

end LeanSpec
