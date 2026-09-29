module

public import LeanSpec.Validated
public import LeanSpec.Kb
public meta import LeanSpec.Kb
public meta import LeanUtil

/-!
# Determinations, defeasible resolution, and boundary search

Three ideas from defeasible / hypergraph-style knowledge work, recast on
`lean-spec`'s fail-closed primitives.

1. **Atomicity of a determination.** A decision is *one* N-ary typed relation
   binding several role-players and an outcome — not a bag of binary facts.
   `Determination` carries a `NonEmptyArray Role`; a determination with no
   role-player cannot be constructed.

2. **Defeasible resolution (the `supersedes` 2-morphism).** A later determination
   can *defeat* an earlier one, but only while the defeater is itself active.
   `effective` returns the latest active, undefeated determination. Proven:
   `effective_active` — resolution never returns an inactive determination.

3. **Fearless optimization.** Use a decidable feasibility predicate as an oracle
   and push a value until it is rejected; the boundary is the proven optimum.
   `boundary` + `boundary_feasible` (the returned value is feasible), with a
   worked `#guard` showing feasibility at the boundary and rejection one step past.

Round-trip `validate_sound` / `validate_complete` for `Determination` are
deferred (reason: experimental surface; the constructors are already fail-closed
on blank ids and empty role sets). Deferring a proof explicitly — rather than
pretending — mirrors `CheckStatus.deferred`.
-/

namespace LeanSpec.TypeSystems

open LeanSpec

public section

/-- A typed role-player inside a determination: which role, and who fills it. -/
public structure Role where
  role : NonBlank
  player : NonBlank
  deriving Repr

/-- Closed outcome vocabulary. A typo cannot inhabit this type. -/
public inductive Outcome where
  | eligible
  | phasedOut
  | disqualified
  | permitted
  | blocked
  deriving Repr, BEq, DecidableEq

/-- An N-ary determination: at least one role-player, one outcome, a logical
clock, whether it is currently in force, and the source version it relied on. -/
public structure Determination where
  id : NonBlank
  roles : NonEmptyArray Role
  outcome : Outcome
  clock : Nat
  active : Bool := true
  /-- The source/snapshot version this determination relied on. Used for
  bi-temporal staleness: when the source advances past this, the determination
  is stale and must be re-reviewed. -/
  provenance : Nat := 0
  deriving Repr

/-- The 2-morphism vocabulary: relations *between* determinations. -/
public inductive MorphismKind where
  | supersedes
  | exceptionOf
  | precedentFor
  deriving Repr, BEq, DecidableEq

/-- A relation between two determinations, addressed by their ids. -/
public structure Morphism where
  kind : MorphismKind
  source : NonBlank
  target : NonBlank
  deriving Repr, BEq

/-! ### Bridge to the generic defeasible core

`Determination.defeated` and `Wiki.superseded` were the *same* algorithm written
twice; both now delegate to `Kb.defeated`, parameterised by what "present" means.
The morphism→relation map lives here, next to `Morphism`, and `Wiki` reuses it. -/

/-- Map the 2-morphism kind to the generic `Kb.RelationKind` (same three cases). -/
@[expose] public def kindToRelKind : MorphismKind → Kb.RelationKind
  | .supersedes  => .supersedes
  | .exceptionOf => .exceptionOf
  | .precedentFor => .precedentFor

/-- `kindToRelKind` preserves the "defeats" verdict: the old inline
`supersedes || exceptionOf` test is exactly the generic `RelationKind.defeats`. -/
public theorem kindToRelKind_defeats (k : MorphismKind) :
    (kindToRelKind k).defeats
      = (k == MorphismKind.supersedes || k == MorphismKind.exceptionOf) := by
  cases k <;> rfl

/-- Map a determination morphism to a generic `Kb.Relation` (ids projected to
strings). Reused by `Wiki` so the mapping exists once, not per axis. -/
@[expose] public def morphismToRelation (m : Morphism) : Kb.Relation :=
  { kind := kindToRelKind m.kind, source := m.source.value, target := m.target.value }

/-- Determination-style presence: an id is present when some determination has it
*and is active*. This is the `present` predicate the generic `Kb.defeated` is
parameterised by on the regulatory axis — contrast `Wiki.present`, which needs
merely present. The single parameter is what lets one algorithm serve both axes. -/
@[expose] public def presentActive (ds : List Determination) : String → Bool :=
  fun idv => ds.any (fun s => s.active && s.id.value == idv)

/-- `d` is defeated when some defeating morphism targets it *and* its source
determination is present and active. A retracted (inactive) defeater does not
defeat — this is what makes the logic defeasible rather than monotone. Now
**delegates to the generic `Kb.defeated`**: the defeat algorithm is the core's,
shared with `Wiki.superseded`, rather than a parallel copy. -/
@[expose] public def defeated (ds : List Determination) (ms : List Morphism)
    (d : Determination) : Bool :=
  Kb.defeated (presentActive ds) (ms.map morphismToRelation) d.id.value

/-- Pick the determination with the highest clock, keeping a member of the list. -/
public def pickLatest : List Determination → Option Determination
  | [] => none
  | a :: rest =>
    match pickLatest rest with
    | none => some a
    | some best => if best.clock < a.clock then some a else some best

/-- The effective determination: latest active, undefeated one. -/
public def effective (ds : List Determination) (ms : List Morphism) :
    Option Determination :=
  pickLatest (ds.filter (fun d => d.active && !defeated ds ms d))

/-- `pickLatest` only ever returns an element of its input. -/
public theorem pickLatest_mem :
    ∀ {xs : List Determination} {d}, pickLatest xs = some d → d ∈ xs := by
  intro xs
  induction xs with
  | nil =>
    intro d h
    simp [pickLatest] at h
  | cons a rest ih =>
    intro d h
    simp only [pickLatest] at h
    split at h
    · cases h
      rw [List.mem_cons]; exact Or.inl rfl
    · next best hsome =>
      split at h
      · cases h
        rw [List.mem_cons]; exact Or.inl rfl
      · cases h
        rw [List.mem_cons]; exact Or.inr (ih hsome)

/-- Membership in a filtered list implies the predicate held. -/
public theorem keep_of_mem_filter {keep : Determination → Bool}
    {xs : List Determination} {d} (h : d ∈ xs.filter keep) : keep d = true :=
  (List.mem_filter.mp h).2

/-- Resolution never returns an inactive determination. -/
public theorem effective_active {ds : List Determination} {ms d}
    (h : effective ds ms = some d) : d.active = true := by
  have hmem := pickLatest_mem h
  have hkeep : (d.active && !defeated ds ms d) = true := keep_of_mem_filter hmem
  cases hd : d.active with
  | true => rfl
  | false =>
    rw [hd] at hkeep
    simp at hkeep

/-! ## Bi-temporal: staleness when the source provenance advances -/

/-- Stale relative to `current`: the source version it relied on is older. -/
public def Determination.stale (current : Nat) (d : Determination) : Bool :=
  decide (d.provenance < current)

/-- Fresh: it relied on at least the current source version. -/
public def Determination.fresh (current : Nat) (d : Determination) : Bool :=
  decide (current ≤ d.provenance)

/-- The active determinations made stale by advancing the source to `current` —
"the source updated; here is exactly what must be re-reviewed". -/
public def staleActive (current : Nat) (ds : List Determination) : List Determination :=
  ds.filter (fun d => d.active && d.stale current)

/-- Everything `staleActive` returns is active and relied on an outdated source. -/
public theorem staleActive_active_and_outdated
    {current : Nat} {ds : List Determination} {d : Determination}
    (h : d ∈ staleActive current ds) : d.active = true ∧ d.provenance < current := by
  have hkeep : (d.active && d.stale current) = true := keep_of_mem_filter h
  have ha : d.active = true := by
    cases hd : d.active with
    | true => rfl
    | false => rw [hd] at hkeep; simp at hkeep
  have hs : d.stale current = true := by
    cases hd : d.stale current with
    | true => rfl
    | false => rw [hd] at hkeep; simp at hkeep
  have hprov : d.provenance < current := by
    simp only [Determination.stale] at hs
    exact of_decide_eq_true hs
  exact ⟨ha, hprov⟩

/-! ## Conflict detection (prioritised default logic) -/

/-- Two determinations conflict for `subjectOf`: both active, same subject,
different outcome. -/
public def conflicting (subjectOf : Determination → String) (a b : Determination) : Bool :=
  a.active && b.active && subjectOf a == subjectOf b && a.outcome != b.outcome

/-- The first conflicting pair, if any. Surfacing this lets the caller *refuse*
(Catala's "crash on conflicting definitions") instead of silently picking one. -/
public def firstConflict (subjectOf : Determination → String) :
    List Determination → Option (Determination × Determination)
  | [] => none
  | d :: rest =>
    match rest.find? (fun e => conflicting subjectOf d e) with
    | some e => some (d, e)
    | none => firstConflict subjectOf rest

/-- A reported conflict is a genuine one: the pair really does conflict. -/
public theorem firstConflict_conflicting {subjectOf : Determination → String} :
    ∀ {ds : List Determination} {a b : Determination},
      firstConflict subjectOf ds = some (a, b) → conflicting subjectOf a b = true := by
  intro ds
  induction ds with
  | nil => intro a b h; simp [firstConflict] at h
  | cons d rest ih =>
    intro a b h
    simp only [firstConflict] at h
    split at h
    · next e hfind =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact List.find?_some hfind
    · exact ih h

/-! ## Fearless optimization: the checker as a boundary oracle -/

/-- Push upward while `valid` accepts, bounded by `fuel`; return the highest
value reached from `n`. Invariant: if `valid n` then `valid` of the result. -/
public def climb (valid : Nat → Bool) : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if valid (n + 1) = true then climb valid fuel (n + 1) else n

/-- Search from 0. `none` when even 0 is infeasible; otherwise the boundary. -/
public def boundary (valid : Nat → Bool) (fuel : Nat) : Option Nat :=
  if valid 0 = true then some (climb valid fuel 0) else none

/-- Everything `climb` returns from a feasible start is itself feasible. -/
public theorem climb_feasible (valid : Nat → Bool) :
    ∀ (fuel n : Nat), valid n = true → valid (climb valid fuel n) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    simp only [climb]; exact hn
  | succ f ih =>
    intro n hn
    simp only [climb]
    split
    · next hv => exact ih (n + 1) hv
    · exact hn

/-- The boundary the search returns is feasible — the proven-optimum guarantee. -/
public theorem boundary_feasible (valid : Nat → Bool) (fuel b : Nat)
    (h : boundary valid fuel = some b) : valid b = true := by
  simp only [boundary] at h
  split at h
  · next h0 =>
    cases h
    exact climb_feasible valid fuel 0 h0
  · cases h

end

/-! ## Worked examples (executable `#guard`s) -/

private def nb (s : String)
    (h : LeanUtil.nonemptyText s = true := by native_decide) : NonBlank := ⟨s, h⟩

private def det (id : NonBlank) (clock : Nat) (active : Bool) (o : Outcome)
    (prov : Nat := 0) : Determination :=
  { id
    roles := ⟨#[{ role := nb "subject", player := nb "acme" }], by decide⟩
    outcome := o
    clock
    active
    provenance := prov }

-- FLSA in miniature: the default (worker is non-exempt) is superseded by a
-- later computer-employee exemption.
private def dDefault : Determination := det (nb "flsa.default") 1 true .disqualified
private def dException : Determination := det (nb "flsa.computer") 2 true .eligible
private def dExceptionOff : Determination := det (nb "flsa.computer") 2 false .eligible
private def mSupersede : Morphism :=
  { kind := .supersedes, source := nb "flsa.computer", target := nb "flsa.default" }

private def flsaWorld : List Determination := [dDefault, dException]
private def flsaMorphs : List Morphism := [mSupersede]

-- The exemption wins while it is active.
#guard ((effective flsaWorld flsaMorphs).map (·.id.value)) == some "flsa.computer"
#guard defeated flsaWorld flsaMorphs dDefault
#guard !defeated flsaWorld flsaMorphs dException

-- Defeasible: retract the exemption (inactive) and the default stands again.
#guard ((effective [dDefault, dExceptionOff] flsaMorphs).map (·.id.value))
        == some "flsa.default"

-- Bi-temporal: advancing the source snapshot marks receipts that relied on an
-- older version as stale (active-and-outdated); inactive ones are not returned.
private def recentReceipt : Determination := det (nb "r.recent") 1 true .permitted 2
private def oldReceipt    : Determination := det (nb "r.old")    1 true .permitted 1
private def oldInactive   : Determination := det (nb "r.old2")   1 false .permitted 1

#guard (staleActive 2 [recentReceipt, oldReceipt]).map (·.id.value) == ["r.old"]
#guard (staleActive 2 [recentReceipt, oldReceipt, oldInactive]).map (·.id.value) == ["r.old"]
#guard recentReceipt.fresh 2
#guard oldReceipt.stale 2

-- An `exceptionOf` morphism also defeats its target (not only `supersedes`).
private def mException : Morphism :=
  { kind := .exceptionOf, source := nb "flsa.computer", target := nb "flsa.default" }
#guard defeated flsaWorld [mException] dDefault

-- Conflict: two active determinations on the same subject with different outcomes.
private def subjKey (d : Determination) : String :=
  match d.roles.items[0]? with
  | some r => r.player.value
  | none => ""
private def relA    : Determination := det (nb "a") 1 true .permitted
private def relB    : Determination := det (nb "b") 1 true .blocked
private def relC    : Determination := det (nb "c") 1 true .permitted
private def relBoff : Determination := det (nb "b") 1 false .blocked

#guard (firstConflict subjKey [relA, relB]).isSome
#guard !(firstConflict subjKey [relA, relC]).isSome
#guard !(firstConflict subjKey [relA, relBoff]).isSome
#guard match firstConflict subjKey [relA, relB] with
       | some (x, y) => x.id.value == "a" && y.id.value == "b"
       | none => false

-- Fearless optimization: feasible iff conversion ≤ 187 (the tax story, in small).
private def feasibleTax (conversion : Nat) : Bool := conversion ≤ 187

#guard boundary feasibleTax 500 == some 187   -- proven optimum
#guard feasibleTax 187                        -- boundary is feasible
#guard !feasibleTax 188                        -- one step past → rejected

end LeanSpec.TypeSystems
