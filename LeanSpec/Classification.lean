module

public import LeanUtil

/-!
# Classification: an opaque, ordered sensitivity label for agent knowledge

Generic (library-owned) sensitivity lattice carried by a `Reflection`. The library
assigns **no meaning** to the levels — it only provides a bounded, totally ordered
lattice with a `join`, and proves that consolidation (`Reflection.merge`) takes the
join, so consolidation can only *raise* sensitivity, never lower it.

Downstream company packs map their disclosure audiences onto these levels and
choose the *default* classification for a newly captured reflection. The library's
lattice **bottom is the most open** level, so that `join` means "consolidation
raises sensitivity"; the downstream default for a new reflection is a policy
choice (often a `.private`-equivalent), deliberately distinct from the lattice
bottom.

Design: `docs/lw0-agent-knowledge-governance-design.md`.
-/

namespace LeanSpec

public section

/-- Opaque sensitivity level. Ordered `open_ < internal < sensitive`; `open_` is the
lattice bottom. Closed enum: a typo cannot inhabit it. -/
public inductive Classification where
  | open_       -- lattice bottom: least sensitive
  | internal
  | sensitive   -- lattice top: most sensitive
  deriving Repr, BEq, DecidableEq

namespace Classification

/-- Rank in the sensitivity order. -/
public def rank : Classification → Nat
  | .open_ => 0
  | .internal => 1
  | .sensitive => 2

/-- Least sensitive level (lattice bottom); the wire/default value when absent. -/
public def bottom : Classification := .open_

/-- Lattice join: the more sensitive of two levels. -/
public def join : Classification → Classification → Classification
  | .sensitive, _ => .sensitive
  | _, .sensitive => .sensitive
  | .internal, _ => .internal
  | _, .internal => .internal
  | .open_, .open_ => .open_

/-! ## Lattice facts -/

/-- Join is commutative. -/
public theorem join_comm (a b : Classification) : join a b = join b a := by
  cases a <;> cases b <;> rfl

/-- Join is idempotent. -/
public theorem join_self (a : Classification) : join a a = a := by
  cases a <;> rfl

/-- Join is an upper bound on the left: it is at least as sensitive as `a`. -/
public theorem le_join_left (a b : Classification) : a.rank ≤ (join a b).rank := by
  cases a <;> cases b <;> simp [join, rank]

/-- Join is an upper bound on the right. -/
public theorem le_join_right (a b : Classification) : b.rank ≤ (join a b).rank := by
  cases a <;> cases b <;> simp [join, rank]

/-- `bottom` is the identity for join: joining with the most-open level changes
nothing. -/
public theorem join_bottom (a : Classification) : join a bottom = a := by
  cases a <;> rfl

end Classification

end

/-! ## Worked examples -/

#guard Classification.join .open_ .internal == .internal
#guard Classification.join .internal .sensitive == .sensitive
#guard Classification.join .sensitive .open_ == .sensitive
#guard Classification.join .open_ .open_ == .open_
-- bottom is the join identity
#guard Classification.join .internal .bottom == .internal

end LeanSpec
