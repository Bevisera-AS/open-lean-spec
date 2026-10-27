import LeanSpec.Logic.Core

/-!
# LRU cache, as logic

The chain in one file: a design signature, system requirements as `Prop`s over
it, a user-level requirement refined from them by a theorem, a shipped
implementation with `@[satisfies]` witnesses and counter-models, and a black-box
requirement with examples for the same product's JSON face.
-/

namespace LeanSpec.Logic.Demo.Lru

open LeanSpec.Logic LeanSpec.Core Lean

/-- The design: what any LRU cache exposes. -/
structure Sig where
  State    : Type
  empty    : Nat → State
  capacity : State → Nat
  put      : State → String → Int → State
  get      : State → String → Option Int × State

/-- A fresh cache has the capacity it was given. -/
@[requirement must]
def emptyHasCapacity (S : Sig) : Prop := ∀ n, S.capacity (S.empty n) = n

/-- With room for at least one entry, get after put returns the value. -/
@[requirement must]
def getAfterPut (S : Sig) : Prop :=
  ∀ s k v, 0 < S.capacity s → (S.get (S.put s k v) k).1 = some v

/-- With capacity 0 nothing is stored. -/
@[requirement must]
def capacityZeroStoresNothing (S : Sig) : Prop :=
  ∀ k v, (S.get (S.put (S.empty 0) k v) k).1 = none

/-- User level: a caller reads back what it stored in a cache of capacity one. -/
@[requirement must user]
def readsBackWhatItStores (S : Sig) : Prop :=
  ∀ k v, (S.get (S.put (S.empty 1) k v) k).1 = some v

/-- Traceability as a theorem: two system requirements imply the user requirement,
for any design. The statement closes `readsBackWhatItStores` once both are closed. -/
@[refines]
theorem readsBack_from_system (S : Sig) (h1 : emptyHasCapacity S) (h2 : getAfterPut S) :
    readsBackWhatItStores S :=
  fun k v => h2 (S.empty 1) k v (by rw [h1]; exact Nat.one_pos)

-- ─── Implementation ──────────────────────────────────────────────────────────

/-- Capacity and entries, most recently used first. -/
abbrev St := Nat × List (String × Int)

def putImpl (s : St) (k : String) (v : Int) : St :=
  (s.1, ((k, v) :: s.2.filter (·.1 != k)).take s.1)

def getImpl (s : St) (k : String) : Option Int × St :=
  match s.2.find? (·.1 == k) with
  | some (_, v) => (some v, (s.1, (k, v) :: s.2.filter (·.1 != k)))
  | none => (none, s)

@[shipped] def impl : Sig where
  State := St
  empty n := (n, [])
  capacity s := s.1
  put := putImpl
  get := getImpl

@[satisfies] theorem impl_emptyHasCapacity : emptyHasCapacity impl := fun _ => rfl

@[satisfies] theorem impl_getAfterPut : getAfterPut impl := by
  intro s k v h
  obtain ⟨cap, l⟩ := s
  cases cap with
  | zero => exact absurd h (Nat.lt_irrefl 0)
  | succ n => simp [impl, putImpl, getImpl, List.take_succ_cons]

@[satisfies] theorem impl_capacityZeroStoresNothing : capacityZeroStoresNothing impl := by
  intro k v; simp [impl, putImpl, getImpl]

-- ─── Counter-models ──────────────────────────────────────────────────────────

/-- Ignores every put. -/
def frozen : Sig := { impl with put := fun s _ _ => s }

/-- Reports capacity 1 for every state. -/
def liar : Sig := { impl with capacity := fun _ => 1 }

/-- Stores even at capacity 0. -/
def greedy : Sig := { impl with put := fun s k v => (s.1, (k, v) :: s.2) }

@[refutes] theorem frozen_fails : ¬ getAfterPut frozen := by
  intro h
  have := h (1, []) "a" 0 (by decide +kernel)
  simp [frozen, impl, getImpl] at this

@[refutes] theorem liar_fails : ¬ emptyHasCapacity liar := by
  intro h
  have := h 0
  simp [liar, impl] at this

@[refutes] theorem greedy_fails : ¬ capacityZeroStoresNothing greedy := by
  intro h
  have := h "a" 0
  simp [greedy, impl, getImpl] at this

-- ─── The JSON face: a black-box requirement with examples ────────────────────

/-- Over stdin and stdout: put then get returns the value. -/
@[requirement should]
def putGetIO : IOSig → Prop := Req.holds [
  ex "put-get" (json% {"capacity": 2, "ops": [["put","a",1],["get","a"]]}) (json% {"results": [null, 1]})]

@[example putGetIO]
def putGetIO_miss : Ex :=
  ex "miss" (json% {"capacity": 2, "ops": [["get","a"]]}) (json% {"results": [null]})

@[evidence putGetIO]
theorem putImpl_keeps_capacity (s : St) (k : String) (v : Int) : (putImpl s k v).1 = s.1 := rfl

spec_statement statement for LeanSpec.Logic.Demo.Lru

#guard statement.statusOf ``emptyHasCapacity == "proved"
#guard statement.statusOf ``getAfterPut == "proved"
#guard statement.statusOf ``capacityZeroStoresNothing == "proved"
#guard statement.statusOf ``readsBackWhatItStores == "refined"
#guard statement.gapsOf ``readsBackWhatItStores == #[.viaRefinement ``readsBack_from_system, .vacuous]
#guard (statement.row? ``readsBackWhatItStores).map (·.level) == some .user
-- The JSON row closes only in `spec report`, by a test run against the program.
#guard statement.statusOf ``putGetIO == "open"
#guard statement.verified

end LeanSpec.Logic.Demo.Lru
