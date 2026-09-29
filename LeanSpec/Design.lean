module

public import LeanSpec.Types
public import LeanSpec.Codec.Applicative
public meta import LeanSpec.Types
public meta import LeanSpec.Codec.Applicative

namespace LeanSpec

open LeanSpec.Codec

public section

/-- Allowed implementation targets. Every option is strongly typed; the set is
closed, so an agent cannot name an unlisted (or weakly typed) language.
`javaViaStrata` records that Java is reached only through Strata verification. -/
public inductive TargetLang where
  | lean4
  | typescript
  | scala
  | rust
  | javaViaStrata
  deriving Repr, BEq, DecidableEq

/-- Where an artifact runs. The web target is TypeScript; native covers the rest. -/
public inductive Surface where
  | web
  | native
  deriving Repr, BEq, DecidableEq

/-- Policy: web artifacts must target TypeScript; native artifacts use any of the
non-web strongly-typed targets (Lean 4 preferred, then Scala/Rust, Java via Strata). -/
public def TargetLang.allowedFor : Surface → TargetLang → Bool
  | .web,    .typescript => true
  | .web,    _           => false
  | .native, .typescript => false
  | .native, _           => true

public abbrev AllowedTarget (surface : Surface) (target : TargetLang) : Prop :=
  TargetLang.allowedFor surface target = true

public instance (surface : Surface) (target : TargetLang) :
    Decidable (AllowedTarget surface target) :=
  by change Decidable (TargetLang.allowedFor surface target = true); infer_instance

/-- Preference ranking. Lower is preferred. Advisory only; not a gate.
For native: Lean 4 (0) over Scala/Rust (1) over Java-via-Strata (2). -/
public def TargetLang.preference : TargetLang → Nat
  | .lean4        => 0
  | .typescript   => 0   -- the only web choice
  | .scala        => 1
  | .rust         => 1
  | .javaViaStrata => 2

/-- Canonical wire token for a target language. -/
public def TargetLang.toToken : TargetLang → String
  | .lean4        => "lean4"
  | .typescript   => "typescript"
  | .scala        => "scala"
  | .rust         => "rust"
  | .javaViaStrata => "java-via-strata"

/-- Parse a wire token into a target language. -/
public def TargetLang.ofToken? : String → Option TargetLang
  | "lean4"           => some .lean4
  | "typescript"      => some .typescript
  | "scala"           => some .scala
  | "rust"            => some .rust
  | "java-via-strata" => some .javaViaStrata
  | _                 => none

public theorem TargetLang.ofToken_toToken (t : TargetLang) :
    TargetLang.ofToken? t.toToken = some t := by
  cases t <;> rfl

/-- Canonical wire token for a surface. -/
public def Surface.toToken : Surface → String
  | .web => "web"
  | .native => "native"

public def Surface.ofToken? : String → Option Surface
  | "web" => some .web
  | "native" => some .native
  | _ => none

public theorem Surface.ofToken_toToken (s : Surface) :
    Surface.ofToken? s.toToken = some s := by
  cases s <;> rfl

/-! Untrusted wire representation. Validation is required before domain use. -/
namespace Raw

/-- Buildable design beside a Requirement label. Names refer to Lean declarations
in the change module; this is not host-language source. `surface`/`target`
default to native Lean 4 for legacy rows. -/
public structure DesignUnit where
  id : String
  surface : String := "native"
  target : String := "lean4"
  interfaces : Array String
  functions : Array String := #[]
  tests : Array String
  theorems : Array String := #[]
  deriving Repr, BEq

end Raw

/-- Agent/builder artifact: interfaces, functions, tests, theorems.
`id` links to a `Requirement` label in the same snapshot. `target` must be
allowed for `surface` by construction, so a web unit cannot target Rust. -/
public structure DesignUnit where
  id : RequirementId
  surface : Surface := .native
  target : TargetLang := .lean4
  targetAllowed : AllowedTarget surface target := by native_decide
  interfaces : NonEmptyArray NonBlank
  functions : Array NonBlank := #[]
  tests : NonEmptyArray NonBlank
  theorems : Array NonBlank := #[]
  deriving Repr

/-- Equality deliberately ignores the proof term; two units compare by payload. -/
public instance : BEq DesignUnit where
  beq left right :=
    left.id == right.id &&
      left.surface == right.surface &&
      left.target == right.target &&
      left.interfaces == right.interfaces &&
      left.functions == right.functions &&
      left.tests == right.tests &&
      left.theorems == right.theorems

public theorem DesignUnit.ext {left right : DesignUnit}
    (hId : left.id = right.id) (hSurface : left.surface = right.surface)
    (hTarget : left.target = right.target) (hIfaces : left.interfaces = right.interfaces)
    (hFns : left.functions = right.functions) (hTests : left.tests = right.tests)
    (hThms : left.theorems = right.theorems) : left = right := by
  cases left with
  | mk id surface target allowed ifaces fns tests thms =>
    cases right with
    | mk id' surface' target' allowed' ifaces' fns' tests' thms' =>
      cases hId; cases hSurface; cases hTarget; cases hIfaces
      cases hFns; cases hTests; cases hThms
      rfl

/-- Compatibility predicate retained for callers during staged migration.
It inspects the proof-carrying fields rather than returning a hard-coded constant. -/
public def DesignUnit.wellFormed (d : DesignUnit) : Bool :=
  decide (ValidRequirementId d.id.value) &&
    TargetLang.allowedFor d.surface d.target &&
    decide (0 < d.interfaces.items.size) &&
    d.interfaces.toArray.all (fun n => LeanUtil.nonemptyText n.value) &&
    d.functions.all (fun n => LeanUtil.nonemptyText n.value) &&
    decide (0 < d.tests.items.size) &&
    d.tests.toArray.all (fun n => LeanUtil.nonemptyText n.value) &&
    d.theorems.all (fun n => LeanUtil.nonemptyText n.value)

/-- Every domain `DesignUnit` satisfies the compatibility well-formedness predicate. -/
public theorem DesignUnit.wellFormed_eq_true (d : DesignUnit) : d.wellFormed = true := by
  simp only [DesignUnit.wellFormed]
  rw [decide_eq_true d.id.property, d.targetAllowed, decide_eq_true d.interfaces.property,
    decide_eq_true d.tests.property]
  simp [show ∀ n : NonBlank, LeanUtil.nonemptyText n.value = true from fun n => n.property]

/-- Projection to the untrusted wire representation. -/
public def DesignUnit.toRaw (d : DesignUnit) : Raw.DesignUnit := {
  id := d.id.value
  surface := d.surface.toToken
  target := d.target.toToken
  interfaces := d.interfaces.items.map (·.value)
  functions := d.functions.map (·.value)
  tests := d.tests.items.map (·.value)
  theorems := d.theorems.map (·.value)
}

/-- Requirement ids that still have a design row. -/
@[expose] public def DesignUnit.ids (designs : Array DesignUnit) : Array String :=
  designs.map (·.id.value)

public abbrev UniqueDesignIds (designs : Array DesignUnit) : Prop :=
  (DesignUnit.ids designs).toList.Nodup

public instance (designs : Array DesignUnit) : Decidable (UniqueDesignIds designs) :=
  inferInstance

/-- Every design id is a requirement id in the same snapshot. Empty designs are linked. -/
@[expose] public def designIdsLinked (requirements : Array Requirement) (designs : Array DesignUnit) : Bool :=
  (DesignUnit.ids designs).toList.all fun id =>
    (requirements.map (·.id.value)).toList.contains id

public abbrev DesignsLinked (requirements : Array Requirement) (designs : Array DesignUnit) : Prop :=
  designIdsLinked requirements designs = true

public instance (requirements : Array Requirement) (designs : Array DesignUnit) :
    Decidable (DesignsLinked requirements designs) :=
  inferInstance

/-- Drop designs whose requirement left the snapshot. Preserves uniqueness. -/
@[expose] public def DesignUnit.sync (requirements : Array Requirement) (designs : Array DesignUnit) :
    Array DesignUnit :=
  let ids := (requirements.map (·.id.value)).toList
  designs.filter fun d => ids.contains d.id.value

namespace Raw.DesignUnit
private theorem surface_ofToken_eq {raw : String} {s : Surface}
    (h : Surface.ofToken? raw = some s) : s.toToken = raw := by
  unfold Surface.ofToken? at h
  split at h <;> first | (cases h; rfl) | contradiction

private theorem target_ofToken_eq {raw : String} {t : TargetLang}
    (h : TargetLang.ofToken? raw = some t) : t.toToken = raw := by
  unfold TargetLang.ofToken? at h
  split at h <;> first | (cases h; rfl) | contradiction

/-- The `Surface` / `TargetLang` token codecs (closed enums parsed from a wire
token). `encode` is `toToken`. Used as field codecs by the `DesignUnit` codec. -/
@[expose] public def surfaceCodec : Codec String Surface where
  decode p raw :=
    match Surface.ofToken? raw with
    | some s => .ok s
    | none => .error { path := p, issue := .disallowedTarget, rejected := some raw }
  encode s := s.toToken
  sound := by
    intro p raw s h
    split at h
    · next tok htok => cases h; exact surface_ofToken_eq htok
    · contradiction
  complete := by
    intro p s
    simp only [Surface.ofToken_toToken]

@[expose] public def targetCodec : Codec String TargetLang where
  decode p raw :=
    match TargetLang.ofToken? raw with
    | some t => .ok t
    | none => .error { path := p, issue := .disallowedTarget, rejected := some raw }
  encode t := t.toToken
  sound := by
    intro p raw t h
    split at h
    · next tok htok => cases h; exact target_ofToken_eq htok
    · contradiction
  complete := by
    intro p t
    simp only [TargetLang.ofToken_toToken]

/-- The `DesignUnit` codec: a product of the field codecs (`reqId`, the surface/target
token codecs, `nonEmpty`/`list nonBlank` for the four name lists), refined by the
`AllowedTarget surface target` constraint. `encode` is definitionally `toRaw`. -/
public def codec : Codec Raw.DesignUnit LeanSpec.DesignUnit :=
  refine
    (comap
      (prod (label "id" reqId) (prod (label "surface" surfaceCodec) (prod (label "target" targetCodec)
        (prod (label "interfaces" (nonEmpty nonBlank)) (prod (label "functions" (list nonBlank))
          (prod (label "tests" (nonEmpty nonBlank)) (label "theorems" (list nonBlank))))))))
      (fun raw => (raw.id, raw.surface, raw.target, raw.interfaces, raw.functions, raw.tests, raw.theorems))
      (fun t => ({ id := t.1, surface := t.2.1, target := t.2.2.1, interfaces := t.2.2.2.1,
                   functions := t.2.2.2.2.1, tests := t.2.2.2.2.2.1, theorems := t.2.2.2.2.2.2 } : Raw.DesignUnit))
      (fun _ => rfl) (fun _ => rfl))
    (fun d => decide (AllowedTarget d.2.1 d.2.2.1))
    (fun p raw => { path := s!"{p}.target", issue := .disallowedTarget, rejected := some raw.target })
    (fun d h => ({ id := d.1, surface := d.2.1, target := d.2.2.1, targetAllowed := of_decide_eq_true h,
                   interfaces := d.2.2.2.1, functions := d.2.2.2.2.1, tests := d.2.2.2.2.2.1,
                   theorems := d.2.2.2.2.2.2 } : LeanSpec.DesignUnit))
    (fun design => (design.id, design.surface, design.target, design.interfaces,
                    design.functions, design.tests, design.theorems))
    (fun _ _ => rfl)
    (fun design => by simp only [decide_eq_true_eq]; exact design.targetAllowed)
    (fun _ => DesignUnit.ext rfl rfl rfl rfl rfl rfl rfl)

/-- Total validation from the untrusted wire DTO into the proof-carrying domain type. -/
public def validate (path : String) (design : Raw.DesignUnit) :
    Except ValidationError LeanSpec.DesignUnit :=
  codec.decode path design

/-- Successful validation projects back to the raw design unit. -/
public theorem validate_sound
    {path : String} {raw : Raw.DesignUnit} {design : LeanSpec.DesignUnit}
    (h : raw.validate path = .ok design) : design.toRaw = raw := by
  have henc : codec.encode design = design.toRaw := rfl
  rw [← henc]; exact codec.sound h

/-- A domain design unit validates back to itself. -/
public theorem validate_complete (design : LeanSpec.DesignUnit) (path : String) :
    design.toRaw.validate path = .ok design := by
  have henc : codec.encode design = design.toRaw := rfl
  show codec.decode path design.toRaw = .ok design
  rw [← henc]; exact codec.complete design

end Raw.DesignUnit

#guard
  let raw : Raw.DesignUnit := {
    id := "theme.selection"
    interfaces := #["Theme", "AppState"]
    functions := #["toggleDark"]
    tests := #["toggleDarkCheck"]
    theorems := #["toggleDarkCheck_of_light"]
  }
  match raw.validate "design" with
  | .ok d => d.wellFormed && d.id.value == "theme.selection"
  | .error _ => false

#guard
  let raw : Raw.DesignUnit := {
    id := "theme.selection"
    interfaces := #[]
    tests := #["t"]
  }
  match raw.validate "design" with
  | .error e => e.path == "design.interfaces" && e.issue == .emptyArray
  | .ok _ => false

#guard
  let raw : Raw.DesignUnit := {
    id := "theme.selection"
    interfaces := #["Theme"]
    tests := #[]
  }
  match raw.validate "design" with
  | .error e => e.path == "design.tests" && e.issue == .emptyArray
  | .ok _ => false

-- Web artifact targeting TypeScript is allowed.
#guard
  let raw : Raw.DesignUnit := {
    id := "page.dashboard"
    surface := "web"
    target := "typescript"
    interfaces := #["DashboardProps"]
    tests := #["rendersLatestYear"]
  }
  match raw.validate "design" with
  | .ok d => d.surface == .web && d.target == .typescript
  | .error _ => false

-- Web artifact targeting Rust is refused by the policy.
#guard
  let raw : Raw.DesignUnit := {
    id := "page.dashboard"
    surface := "web"
    target := "rust"
    interfaces := #["DashboardProps"]
    tests := #["t"]
  }
  match raw.validate "design" with
  | .error e => e.path == "design.target" && e.issue == .disallowedTarget
  | .ok _ => false

-- Native artifact targeting Lean 4 is allowed.
#guard
  let raw : Raw.DesignUnit := {
    id := "core.snapshot"
    surface := "native"
    target := "lean4"
    interfaces := #["SpecSnapshot"]
    tests := #["archiveCheck"]
  }
  match raw.validate "design" with
  | .ok d => d.target == .lean4
  | .error _ => false

-- Native artifact targeting TypeScript is refused.
#guard
  let raw : Raw.DesignUnit := {
    id := "core.snapshot"
    surface := "native"
    target := "typescript"
    interfaces := #["SpecSnapshot"]
    tests := #["t"]
  }
  match raw.validate "design" with
  | .error e => e.issue == .disallowedTarget
  | .ok _ => false

-- An unknown language token is refused.
#guard
  let raw : Raw.DesignUnit := {
    id := "core.snapshot"
    surface := "native"
    target := "python"
    interfaces := #["SpecSnapshot"]
    tests := #["t"]
  }
  match raw.validate "design" with
  | .error e => e.issue == .disallowedTarget
  | .ok _ => false

-- Java is allowed on native only via the strata token.
#guard
  let raw : Raw.DesignUnit := {
    id := "core.snapshot"
    surface := "native"
    target := "java-via-strata"
    interfaces := #["SpecSnapshot"]
    tests := #["t"]
  }
  match raw.validate "design" with
  | .ok d => d.target == .javaViaStrata
  | .error _ => false

-- Preference: Lean 4 outranks Scala/Rust, which outrank Java-via-Strata.
#guard TargetLang.preference .lean4 < TargetLang.preference .scala
#guard TargetLang.preference .scala == TargetLang.preference .rust
#guard TargetLang.preference .rust < TargetLang.preference .javaViaStrata

end

end LeanSpec
