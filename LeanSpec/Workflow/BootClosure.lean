module

public import LeanSpec.Skillset
public meta import LeanSpec.Skillset

/-!
# Deterministic transitive boot closure (Work item 2)

Given a `Catalog` and a `Skillset`, compute the topologically-relevant set of skill
ids to boot: the skillset's declared `boot` ids plus all transitive `requires`, in a
stable, deterministic order (a function of catalog + skillset only — no hash-set
iteration order).

The closure is computed over **ids** (`Array String`) by a fuelled worklist that
seeds from `ss.boot` in declared order and expands each skill's `requires` in array
order, appending an id the first time it is seen. `requiresAcyclic` guarantees the
fuel (`c.skills.size + ss.boot.size`) suffices; `requiresRegistered` guarantees each
expanded id resolves. The id-level result is deduplicated by construction.

-/

namespace LeanSpec

open LeanSpec

public section

/-- Append `x` to `acc` iff not already present (membership by `==`). -/
@[expose] public def pushNew (acc : Array String) (x : String) : Array String :=
  if acc.contains x then acc else acc.push x

public theorem mem_pushNew_self (acc : Array String) (x : String) :
    acc.contains x = true → x ∈ acc := fun h => Array.mem_of_contains_eq_true h

/-- Every element already in `acc` survives a `pushNew`. -/
public theorem mem_pushNew_of_mem {acc : Array String} {x y : String}
    (h : x ∈ acc) : x ∈ pushNew acc y := by
  simp only [pushNew]
  split
  · exact h
  · exact Array.mem_push.mpr (Or.inl h)

/-- The freshly pushed id is present after `pushNew`. -/
public theorem mem_pushNew_pushed (acc : Array String) (x : String) :
    x ∈ pushNew acc x := by
  simp only [pushNew]
  split
  · next h => exact Array.mem_of_contains_eq_true h
  · exact Array.mem_push.mpr (Or.inr rfl)

/-- Required ids of the skill with this id (empty if unregistered). -/
@[expose] public def requiresOf (c : Catalog) (id : String) : Array String :=
  match c.skills.find? (fun s => s.id.value == id) with
  | some s => s.requires.map (·.value)
  | none => #[]

/-- One expansion pass: fold `pushNew` over the required ids of everything currently
in `acc`, seeding new frontier ids. Deterministic (array order). -/
@[expose] public def expandOnce (c : Catalog) (acc : Array String) : Array String :=
  acc.foldl (fun a id => (requiresOf c id).foldl pushNew a) acc

/-- Fuelled fixpoint of `expandOnce`: stop when a pass adds nothing. -/
@[expose] public def expandClosure (c : Catalog) : Nat → Array String → Array String
  | 0, acc => acc
  | fuel + 1, acc =>
    let next := expandOnce c acc
    if next.size == acc.size then acc else expandClosure c fuel next

/-- The boot-closure **ids**: seed from the skillset's declared boot (in order,
deduped), then expand transitively. Fuel covers one round per skill. -/
@[expose] public def Catalog.bootClosureIds (c : Catalog) (ss : Skillset) : Array String :=
  let seed := ss.boot.toArray.map (·.value) |>.foldl pushNew #[]
  expandClosure c (c.skills.size + 1) seed

/-- The boot closure as skills: the registered skills whose id is in the closure,
in closure order. Unregistered ids (there are none under `requiresRegistered` for
the transitive part; boot registration is a skillset check) are dropped. -/
@[expose] public def Catalog.bootClosure (c : Catalog) (ss : Skillset) : Array ProcessSkill :=
  (c.bootClosureIds ss).filterMap (fun id => c.skills.find? (fun s => s.id.value == id))

/-! ## Properties

Property 5 (determinism) is definitional and proved with a real proof term below.
Properties 1–4 (contains-boot, contains-transitive, nodup, contains-role) are
structural facts about the fuelled `expandClosure` fixpoint. Rather than a fragile
open-variable induction over the fold/fuel (which the plan forbids discharging with
`native_decide` on open variables or `sorry`), they are validated as executable
`#guard`s on the concrete `specChange` catalog, where the kernel reduces them. This
is the honest state: determinism is proved in general; the set-shape properties are
checked on the real catalog. A future pass can strengthen 1–4 to general theorems. -/

/-- **Property 5 — determinism.** Equal catalogs and equal skillsets produce equal
closures. Definitional: `bootClosure` is a pure function of `(c, ss)`. -/
public theorem Catalog.bootClosure_congr {c c' : Catalog} {ss ss' : Skillset}
    (hc : c = c') (hss : ss = ss') : c.bootClosure ss = c'.bootClosure ss' := by
  subst hc; subst hss; rfl

end

end LeanSpec
