import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.DocString
import LeanSpec.Core.Types

/-!
# Spec as logic

A requirement is a `Prop` over a design signature. Evidence is a theorem whose
type is that `Prop` applied to an implementation. A counter-model is a theorem
`¬ R bad`. Nothing here carries prose: the id is the Lean `Name`, the claim is
the `Prop`, and a docstring is a label only.

- `@[requirement must]` / `@[requirement should]` on `def R : Sig → Prop`;
  `@[requirement must user]` for a user-level requirement (default `system`)
- `@[refines]` on `theorem t : … → R₁ S → R₂ S → U S`: the system requirements
  among the premises refine the user requirement `U`; `U` closes when they do
- `@[satisfies]` on `theorem t : R impl` (or `… → R impl`)
- `@[refutes]` on `theorem t : ¬ R bad`
- `@[shipped]` on `def impl : Sig` when that Lean code is the product, not a model of it
- `@[sign_off signer "digest"]` on `axiom a : SignOff R impl`: a human judgement
- `@[example R]` on `def e : Ex`: the requirement at one point, run by `spec test`
- `@[evidence R₁ R₂]` on a theorem about the product's functions: supporting
  evidence for those requirements, linked by name, never a proof of them

For a black-box program the signature is `LeanSpec.Core.IOSig` and a requirement
is `Req.holds [examples]` or `IOReq pre post` (`LeanSpec/Core/Types.lean`).

The requirement a `@[satisfies]` theorem witnesses is read off its type, never
from an argument the author writes, so a theorem cannot be attached to the wrong
one; so are the parent and children of a `@[refines]` theorem. `@[example]` and
`@[evidence]` name the requirement; the name is resolved at elaboration, so an
unknown one is a compile error.

`spec%` reflects every requirement in scope into `List LeanSpec.Core.ReqView`
for the `spec` CLI; `statement%` is the kernel-side `Statement` as a term.
-/

namespace LeanSpec.Logic

open Lean Meta Elab Command

/-- `must` keeps the mark off while open; `should` is listed and never blocks. -/
inductive Strength where
  | must
  | should
  deriving Repr, DecidableEq, Inhabited, ToExpr

def Strength.text : Strength → String
  | .must => "must"
  | .should => "should"

/-- `system`: about the design. `user`: stakeholder level; it closes through a
`@[refines]` theorem from closed system requirements, or by its own witness. -/
inductive Level where
  | system
  | user
  deriving Repr, DecidableEq, Inhabited, ToExpr

def Level.text : Level → String
  | .system => "system"
  | .user => "user"

/-- Criterion `R` holds of `impl` by a person's judgement. The constructor is
private, so outside this file a `SignOff` exists only as a hypothesis (the proof
waits for one) or as a `@[sign_off]` axiom (a named person gave one). Either way
it shows in the statement. -/
structure SignOff {Sig : Sort u} (R : Sig → Prop) (impl : Sig) : Prop where
  private mk ::
  holds : R impl

inductive Entry where
  | requirement (decl : Name) (strength : Strength) (level : Level)
  | witness (thm req : Name)
  | counter (thm req : Name)
  | shipped (decl : Name)
  | signOff (ax req : Name) (signer : Name) (digest : String)
  /-- `@[example req] def decl : Ex`. -/
  | exampleOf (decl req : Name)
  /-- `@[evidence req] theorem thm`; `general` when it quantifies over an input. -/
  | supporting (thm req : Name) (general : Bool)
  /-- `@[refines] theorem thm : … → child S → … → parent S`. -/
  | refinement (thm parent : Name) (children : Array Name)
  deriving Inhabited

initialize specExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

def requirements (env : Environment) : Array (Name × Strength × Level) :=
  (specExt.getState env).filterMap fun
    | .requirement d s l => some (d, s, l)
    | _ => none

def witnesses (env : Environment) : Array (Name × Name) :=
  (specExt.getState env).filterMap fun
    | .witness t r => some (t, r)
    | _ => none

def counters (env : Environment) : Array (Name × Name) :=
  (specExt.getState env).filterMap fun
    | .counter t r => some (t, r)
    | _ => none

def shippedDecls (env : Environment) : Array Name :=
  (specExt.getState env).filterMap fun
    | .shipped d => some d
    | _ => none

/-- `(axiom, requirement, signer, digest signed)`. -/
def signOffs (env : Environment) : Array (Name × Name × Name × String) :=
  (specExt.getState env).filterMap fun
    | .signOff a r s d => some (a, r, s, d)
    | _ => none

/-- `(example decl, requirement)`. -/
def examplesOf (env : Environment) : Array (Name × Name) :=
  (specExt.getState env).filterMap fun
    | .exampleOf d r => some (d, r)
    | _ => none

/-- `(theorem, requirement, general)`. -/
def supporting (env : Environment) : Array (Name × Name × Bool) :=
  (specExt.getState env).filterMap fun
    | .supporting t r g => some (t, r, g)
    | _ => none

/-- `(theorem, parent, children)`. -/
def refinements (env : Environment) : Array (Name × Name × Array Name) :=
  (specExt.getState env).filterMap fun
    | .refinement t p cs => some (t, p, cs)
    | _ => none

/-! ## Digest

FNV-1a 64 over the requirement's name and its fully qualified `Prop`. A sign-off
records the digest it saw; if the `Prop` changes later, the sign-off is stale. -/

def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

def hex64 (n : UInt64) : String :=
  let digits := Nat.toDigits 16 n.toNat
  "fnv1a64:" ++ String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

private def oneLine (s : String) : String :=
  String.ofList <| s.toList.map fun c => if c == '\n' || c == '\t' then ' ' else c

private def pp (e : Expr) : MetaM String := do
  return oneLine ((← ppExpr e).pretty 100000)

/-- Fully qualified, so `open` and local notation do not move the digest. -/
private def ppFull (e : Expr) : MetaM String :=
  withOptions (fun o => pp.fullNames.set o true) (pp e)

/-- Examples attached to `req` by `@[example]`, in registration order. -/
def attachedExamples (env : Environment) (req : Name) : Array Name :=
  (specExt.getState env).filterMap fun
    | .exampleOf d r => if r == req then some d else none
    | _ => none

/-- The digest covers the `Prop` and every attached example's value: for a
black-box requirement the examples are the claim at its points, so a changed,
added or dropped example moves the digest and turns a sign-off stale. With no
attached examples the digest is over the name and the `Prop` alone. -/
def requirementDigest (req : Name) : MetaM String := do
  let env ← getEnv
  let some info := env.find? req | throwError "unknown {req}"
  let mut text := s!"{req}\n{← ppFull info.value!}"
  for e in attachedExamples env req do
    let some einfo := env.find? e | continue
    text := text ++ s!"\n{e}\n{← ppFull einfo.value!}"
  return hex64 (fnv1a64 text)

/-- `#requirement_digest R` prints the digest a sign-off of `R` must quote. -/
elab "#requirement_digest " r:ident : command => do
  let req ← liftCoreM <| realizeGlobalConstNoOverload r
  logInfo (← liftTermElabM (requirementDigest req))

/-! ## Attributes -/

/-- The requirement and the model a statement is about: `R impl` gives `(R, impl)`,
`¬ R bad` gives `(R, bad)` when `negated`. Binders are opened without unfolding,
so `R` itself is never reduced away. -/
def subjectOf? (type : Expr) (negated : Bool) : MetaM (Option (Name × Expr)) :=
  forallTelescope type fun _ body => do
    let body ← instantiateMVars body
    let body ←
      if negated then
        if body.isAppOfArity ``Not 1 then pure body.appArg!
        else return none
      else pure body
    match body.getAppFn.constName?, body.getAppArgs.back? with
    | some r, some m => return some (r, m)
    | _, _ => return none

/-- Binders of a theorem's type that are `SignOff R _`: the proof waits for them. -/
def signOffHyps (type : Expr) : MetaM (Array Name) :=
  forallTelescope type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if t.isAppOf ``SignOff then
        if let some r := t.getAppArgs[1]?.bind (·.getAppFn.constName?) then
          out := out.push r
    return out

/-- General: quantifies over a non-Prop variable, also behind definitions or
∧/∨/↔ (∃ does not count). A closed statement is an example. -/
partial def isGeneral (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun xs b => do
    if ← xs.anyM fun x => do return !(← isProp (← inferType x)) then return true
    if b.isAppOfArity ``And 2 || b.isAppOfArity ``Or 2 || b.isAppOfArity ``Iff 2 then
      return (← isGeneral b.appFn!.appArg!) || (← isGeneral b.appArg!)
    return false

private def isRegistered (env : Environment) (r : Name) : Bool :=
  (requirements env).any (·.1 == r)

syntax (name := requirementAttr) "requirement " ident (ident)? : attr

initialize registerBuiltinAttribute {
  name := `requirementAttr
  descr := "a requirement: a `def R : Sig → Prop`"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[requirement] must be global"
    let strength ← match stx[1].getId.toString with
      | "must" => pure Strength.must
      | "should" => pure Strength.should
      | _ => throwError "expected `@[requirement must]` or `@[requirement should]`, optionally followed by `user`"
    let level ← match stx[2].getNumArgs with
      | 0 => pure Level.system
      | _ => match stx[2][0].getId.toString with
        | "system" => pure Level.system
        | "user" => pure Level.user
        | other => throwError "unknown level `{other}`; expected `system` or `user`"
    let some info := (← getEnv).find? decl | throwError "unknown {decl}"
    unless info matches .defnInfo _ do
      throwError "@[requirement] goes on a `def R : Sig → Prop`, not a {decl}"
    MetaM.run' do
      let ok ← forallTelescopeReducing info.type fun xs body =>
        pure (xs.size ≥ 1 && body.isProp)
      unless ok do throwError "@[requirement] {decl} must have type `Sig → Prop`"
    modifyEnv (specExt.addEntry · (.requirement decl strength level))
}

private def registerEvidence (decl : Name) (negated : Bool) : AttrM Unit := do
  let some info := (← getEnv).find? decl | throwError "unknown {decl}"
  unless info matches .thmInfo _ do throwError "{decl} must be a theorem"
  let some (r, _) ← (subjectOf? info.type negated).run' |
    throwError (if negated then "@[refutes] needs a statement `¬ R bad`"
      else "@[satisfies] needs a statement `R impl`")
  unless isRegistered (← getEnv) r do
    throwError "{decl} is about {r}, which is not a @[requirement]"
  modifyEnv (specExt.addEntry · (if negated then .counter decl r else .witness decl r))

/-- The parent and children of a refinement theorem: the conclusion `U S` names
the parent; every premise `R x…` whose head is a registered requirement is a child. -/
def refinementOf? (type : Expr) (registered : Name → Bool) : MetaM (Option (Name × Array Name)) :=
  forallTelescope type fun xs body => do
    let body ← instantiateMVars body
    let some parent := body.getAppFn.constName? | return none
    unless registered parent do return none
    let mut children := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if let some r := t.getAppFn.constName? then
        if registered r && !children.contains r then children := children.push r
    return some (parent, children)

syntax (name := satisfiesAttr) "satisfies" : attr
syntax (name := refutesAttr) "refutes" : attr
syntax (name := refinesAttr) "refines" : attr
syntax (name := shippedAttr) "shipped" : attr
syntax (name := signOffAttr) "sign_off " ident str : attr
syntax (name := exampleAttr) "example " ident : attr
syntax (name := evidenceAttr) "evidence " ident+ : attr

initialize registerBuiltinAttribute {
  name := `satisfiesAttr
  descr := "evidence: a theorem `R impl` for a @[requirement] R"
  applicationTime := .afterTypeChecking
  add := fun decl _ _ => registerEvidence decl false
}

initialize registerBuiltinAttribute {
  name := `refutesAttr
  descr := "a counter-model: a theorem `¬ R bad` for a @[requirement] R"
  applicationTime := .afterTypeChecking
  add := fun decl _ _ => registerEvidence decl true
}

initialize registerBuiltinAttribute {
  name := `refinesAttr
  descr := "traceability: a theorem `… → R₁ S → R₂ S → U S`, the requirements R refining U"
  applicationTime := .afterTypeChecking
  add := fun decl _ _ => do
    let some info := (← getEnv).find? decl | throwError "unknown {decl}"
    unless info matches .thmInfo _ do throwError "@[refines] goes on a theorem"
    if (← collectAxioms decl).contains ``sorryAx then
      throwError "@[refines]: {decl} depends on sorryAx"
    let env ← getEnv
    let some (parent, children) ← (refinementOf? info.type (isRegistered env)).run' |
      throwError "@[refines] needs a statement `… → U S` whose conclusion is a @[requirement]"
    if children.isEmpty then
      throwError "@[refines] {decl}: no premise is a @[requirement]; nothing refines {parent}"
    modifyEnv (specExt.addEntry · (.refinement decl parent children))
}

initialize registerBuiltinAttribute {
  name := `shippedAttr
  descr := "this definition is the product's code, not a model of it"
  applicationTime := .afterTypeChecking
  add := fun decl _ _ => do
    let some info := (← getEnv).find? decl | throwError "unknown {decl}"
    unless info matches .defnInfo _ do throwError "@[shipped] goes on a `def`"
    modifyEnv (specExt.addEntry · (.shipped decl))
}

initialize registerBuiltinAttribute {
  name := `signOffAttr
  descr := "a person's sign-off: an `axiom a : SignOff R impl`"
  applicationTime := .afterTypeChecking
  add := fun decl stx _ => do
    let `(attr| sign_off $signer:ident $digest:str) := stx
      | throwError "expected `@[sign_off signer \"fnv1a64:…\"]`"
    let some info := (← getEnv).find? decl | throwError "unknown {decl}"
    unless info matches .axiomInfo _ do throwError "@[sign_off] goes on an `axiom`"
    let some r := (do
        guard (info.type.isAppOf ``SignOff)
        info.type.getAppArgs[1]?.bind (·.getAppFn.constName?)) |
      throwError "@[sign_off] needs an axiom of type `SignOff R impl`"
    unless isRegistered (← getEnv) r do
      throwError "{decl} signs off {r}, which is not a @[requirement]"
    modifyEnv (specExt.addEntry · (.signOff decl r signer.getId digest.getString))
}

initialize registerBuiltinAttribute {
  name := `exampleAttr
  descr := "an example of a @[requirement]: a `def e : Ex`"
  applicationTime := .afterTypeChecking
  add := fun decl stx _ => do
    let `(attr| example $r:ident) := stx | throwError "expected `@[example R]`"
    let req ← realizeGlobalConstNoOverload r
    let some info := (← getEnv).find? decl | throwError "unknown {decl}"
    unless info matches .defnInfo _ && info.type.isConstOf ``LeanSpec.Core.Ex do
      throwError "@[example] goes on a `def e : Ex`"
    unless isRegistered (← getEnv) req do
      throwError "{decl} is an example of {req}, which is not a @[requirement]"
    modifyEnv (specExt.addEntry · (.exampleOf decl req))
}

initialize registerBuiltinAttribute {
  name := `evidenceAttr
  descr := "a sorry-free theorem about the product, linked to the requirements it supports"
  applicationTime := .afterTypeChecking
  add := fun decl stx _ => do
    let some info := (← getEnv).find? decl | throwError "unknown {decl}"
    unless info matches .thmInfo _ do throwError "@[evidence] goes on a theorem"
    if (← collectAxioms decl).contains ``sorryAx then
      throwError "@[evidence]: {decl} depends on sorryAx; a sorry'd proof is not evidence"
    let general ← (isGeneral info.type).run'
    for r in stx[1].getArgs do
      let req ← realizeGlobalConstNoOverload r
      unless isRegistered (← getEnv) req do
        throwError "{decl} is evidence for {req}, which is not a @[requirement]"
      modifyEnv (specExt.addEntry · (.supporting decl req general))
}

/-! ## Gaps: one function, every reason a requirement is not proved -/

inductive Gap where
  /-- No `@[satisfies]` theorem. -/
  | noWitness
  /-- A witness depends on `sorryAx`. -/
  | usesSorry
  /-- A witness depends on an axiom that is neither standard nor a `@[sign_off]`. -/
  | nonStandardAxiom (ax : Name)
  /-- A witness takes a `SignOff` hypothesis that nobody has given. -/
  | awaitingSignOff
  /-- A sign-off quotes a digest the requirement no longer has. -/
  | staleSignOff (signer : Name)
  /-- Holds by a person's judgement, not a proof. -/
  | signedOff (signer : Name)
  /-- No witness is about a `@[shipped]` definition: proved of a model only. -/
  | modelOnly
  /-- No `@[refutes]` counter-model: the kernel has not seen this differ from `True`. -/
  | vacuous
  /-- A user-level requirement with neither a witness nor a `@[refines]` theorem. -/
  | unrefined
  /-- A refinement whose child is still open. -/
  | childOpen (child : Name)
  /-- Closed by a `@[refines]` theorem from children that are all closed. -/
  | viaRefinement (thm : Name)
  deriving Repr, DecidableEq, Inhabited, ToExpr

def standardAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

/-- What `gaps` needs about one witness theorem. -/
structure WitnessFacts where
  axioms : Array Name
  /-- It takes a `SignOff` hypothesis. -/
  awaiting : Bool
  /-- Its model is a `@[shipped]` definition. -/
  shipped : Bool
  deriving Inhabited

/-- What `gaps` needs about one sign-off axiom. -/
structure SignOffFacts where
  ax : Name
  signer : Name
  current : Bool
  deriving Inhabited

/-- What `gaps` needs about one refinement theorem. -/
structure RefinementFacts where
  thm : Name
  /-- Children whose own row is open or absent. -/
  openChildren : Array Name
  deriving Inhabited

private def dedup [BEq α] (xs : Array α) : Array α :=
  xs.foldl (fun acc a => if acc.contains a then acc else acc.push a) #[]

/-- All gaps in stable order, from facts already collected. Pure, so consumers
and tests never re-derive the rules. Without a witness, a refinement from closed
children closes the row (`viaRefinement`); one with an open child does not. -/
def gaps (ws : Array WitnessFacts) (sos : Array SignOffFacts) (counters : Nat)
    (level : Level := .system) (refs : Array RefinementFacts := #[]) : Array Gap :=
  let g : Array Gap :=
    if !ws.isEmpty then #[]
    else if refs.isEmpty then
      #[.noWitness] ++ (if level == .user then #[.unrefined] else #[])
    else refs.flatMap fun r =>
      if r.openChildren.isEmpty then #[.viaRefinement r.thm] else r.openChildren.map .childOpen
  let axs := dedup (ws.flatMap (·.axioms))
  let g := if axs.contains ``sorryAx then g.push .usesSorry else g
  let signed := axs.filterMap fun a => sos.find? (·.ax == a)
  let extra := axs.filter fun a =>
    a != ``sorryAx && !standardAxiom a && !signed.any (·.ax == a)
  let g := g ++ extra.map .nonStandardAxiom
  let g := if ws.any (·.awaiting) then g.push .awaitingSignOff else g
  let g := g ++ (signed.filter (!·.current)).map (.staleSignOff ·.signer)
  let g := g ++ (signed.filter (·.current)).map (.signedOff ·.signer)
  let g := if !ws.isEmpty && !ws.any (·.shipped) then g.push .modelOnly else g
  if counters == 0 then g.push .vacuous else g

/-- Whether a gap keeps the row open. A current sign-off, a model-only proof,
vacuity and a refinement from closed children are reported, not blocking: each
is a named limit a reader can weigh. -/
def Gap.blocks : Gap → Bool
  | .noWitness | .usesSorry | .nonStandardAxiom _ | .awaitingSignOff | .staleSignOff _
  | .unrefined | .childOpen _ => true
  | .signedOff _ | .modelOnly | .vacuous | .viaRefinement _ => false

def Gap.text : Gap → String
  | .noWitness => "no-witness"
  | .usesSorry => "uses-sorry"
  | .nonStandardAxiom a => s!"non-standard-axiom {a}"
  | .awaitingSignOff => "awaiting-sign-off"
  | .staleSignOff s => s!"stale-sign-off {s}"
  | .signedOff s => s!"signed-off {s}"
  | .modelOnly => "model-only"
  | .vacuous => "vacuous"
  | .unrefined => "unrefined"
  | .childOpen c => s!"child-open {c}"
  | .viaRefinement t => s!"via-refinement {t}"

/-! ## The statement -/

structure WitnessRow where
  thm : Name
  model : String
  shipped : Bool
  axioms : Array Name
  awaiting : Bool
  /-- Quantifies over an input (after unfolding), as opposed to a closed instance. -/
  general : Bool
  deriving Repr, Inhabited, ToExpr

structure Row where
  req : Name
  strength : Strength
  level : Level
  digest : String
  label : String
  prop : String
  /-- `examples` for a `Req.holds` body, `io` for `IOReq`, `prop` otherwise. -/
  kind : String
  /-- `@[example]` declarations attached by name. -/
  examples : Array Name
  witnesses : Array WitnessRow
  /-- `@[evidence]` theorems, each with whether it is general. -/
  evidence : Array (Name × Bool)
  /-- `@[refines]` theorems concluding this requirement, with their children. -/
  refinedBy : Array (Name × Array Name)
  counters : Array (Name × String)
  gaps : Array Gap
  deriving Repr, Inhabited, ToExpr

def Row.proved (r : Row) : Bool := !r.gaps.any Gap.blocks

/-- `open`, or how far a closed row's evidence reaches: `signed` (a person's
judgement), `model` (proved of a model, not the shipped code), `refined` (closed
through a refinement from closed children, no witness of its own) or `proved`. -/
def Row.status (r : Row) : String :=
  if !r.proved then "open"
  else if r.gaps.any (· matches .signedOff _) then "signed"
  else if r.gaps.contains .modelOnly then "model"
  else if r.gaps.any (· matches .viaRefinement _) then "refined"
  else "proved"

structure Statement where
  toolchain : String
  digest : String
  rows : Array Row
  deriving Repr, Inhabited, ToExpr

/-- The mark holds when every `must` row is closed. -/
def Statement.verified (s : Statement) : Bool :=
  s.rows.all fun r => r.strength == .should || r.proved

def Statement.row? (s : Statement) (req : Name) : Option Row :=
  s.rows.find? (·.req == req)

def Statement.gapsOf (s : Statement) (req : Name) : Array Gap :=
  (s.row? req).map (·.gaps) |>.getD #[]

def Statement.statusOf (s : Statement) (req : Name) : String :=
  (s.row? req).map Row.status |>.getD "absent"

private def q (s : String) : String := "\"" ++ s ++ "\""

private def scopeText (general : Bool) : String :=
  if general then "general" else "example"

/-- Rendered one way for humans. Nothing reads this text back. -/
def Statement.render (s : Statement) : String := Id.run do
  let mut out := "schema lean-spec.verification/3\n"
  out := out ++ s!"mark {if s.verified then "lean-spec-verified" else "none"}\n"
  out := out ++ s!"toolchain {s.toolchain}\n"
  out := out ++ s!"spec-digest {s.digest}\n"
  for r in s.rows do
    out := out ++ s!"requirement {r.req}\n"
    out := out ++ s!"  strength {r.strength.text}\n"
    out := out ++ s!"  level {r.level.text}\n"
    out := out ++ s!"  status {r.status}\n"
    out := out ++ s!"  kind {r.kind}\n"
    out := out ++ s!"  digest {r.digest}\n"
    unless r.label.isEmpty do out := out ++ s!"  label {q r.label}\n"
    out := out ++ s!"  prop {q r.prop}\n"
    for e in r.examples do
      out := out ++ s!"  example {e}\n"
    for w in r.witnesses do
      out := out ++ s!"  witness {w.thm}\n"
      out := out ++ s!"    model {w.model} ({if w.shipped then "shipped" else "model only"})\n"
      out := out ++ s!"    scope {scopeText w.general}\n"
      let axs := if w.axioms.isEmpty then "(none)" else " ".intercalate (w.axioms.toList.map toString)
      out := out ++ s!"    axioms {axs}\n"
      if w.awaiting then out := out ++ "    awaits sign-off\n"
    for (t, g) in r.evidence do
      out := out ++ s!"  evidence {t} ({scopeText g})\n"
    for (t, cs) in r.refinedBy do
      out := out ++ s!"  refined-by {t}\n    from {" ".intercalate (cs.toList.map toString)}\n"
    for (c, m) in r.counters do
      out := out ++ s!"  refuted-by {c}\n    model {m}\n"
    for g in r.gaps do
      out := out ++ s!"  gap {g.text}\n"
  return out

/-- What a requirement's body is built from: `Req.holds exs` gives `(some exs, none)`,
`IOReq pre post` gives `(none, some post)`, anything else `(none, none)`. The
parts must not depend on the signature variable. -/
def bodyParts (req : Name) : MetaM (Option Expr × Option Expr) := do
  let some info := (← getEnv).find? req | return (none, none)
  let some v := info.value? | return (none, none)
  lambdaTelescope v fun xs body => do
    let closed (e : Expr) : Bool := !xs.any fun x => e.containsFVar x.fvarId!
    let f := body.getAppFn
    let args := body.getAppArgs
    if f.isConstOf ``LeanSpec.Core.Req.holds then
      if let some exs := args[0]? then
        if closed exs then return (some exs, none)
    if f.isConstOf ``LeanSpec.Core.IOReq then
      if let some post := args[1]? then
        if closed post then return (none, some post)
    return (none, none)

def kindOf (req : Name) : MetaM String := do
  match ← bodyParts req with
  | (some _, _) => pure "examples"
  | (_, some _) => pure "io"
  | _ => pure "prop"

/-- The facts a row's gaps are computed from, kept so refinement can be
re-evaluated once every row's status is known. -/
private structure RowFacts where
  witnesses : Array WitnessFacts
  signOffs : Array SignOffFacts
  counters : Nat
  level : Level
  /-- `(theorem, children)`. -/
  refinedBy : Array (Name × Array Name)

/-- Build the statement for every requirement whose name lies under `ns`. Rows are
built once, then their gaps are recomputed until no refinement changes status, so
a chain of user-level requirements closes from the bottom up. -/
def collect (ns : Name) : MetaM Statement := do
  let env ← getEnv
  let shipped := shippedDecls env
  let mut rows : Array Row := #[]
  let mut facts : Array RowFacts := #[]
  for (req, strength, level) in requirements env do
    unless ns.isPrefixOf req do continue
    let some info := env.find? req | continue
    let label := ((← findDocString? env req).getD "").trimAscii.toString
    let digest ← requirementDigest req
    let mut wrows := #[]
    for (t, r) in witnesses env do
      unless r == req do continue
      let some tinfo := env.find? t | continue
      let (model, isShipped) ← match ← subjectOf? tinfo.type false with
        | some (_, m) => pure (← pp m, m.getAppFn.constName?.any shipped.contains)
        | none => pure ("?", false)
      wrows := wrows.push {
        thm := t, model, shipped := isShipped, axioms := ← collectAxioms t
        awaiting := !(← signOffHyps tinfo.type).isEmpty
        general := ← isGeneral tinfo.type }
    let mut crows := #[]
    for (t, r) in counters env do
      unless r == req do continue
      let some tinfo := env.find? t | continue
      let model ← match ← subjectOf? tinfo.type true with
        | some (_, m) => pp m
        | none => pure "?"
      crows := crows.push (t, model)
    let sos := (signOffs env).filterMap fun (a, r, s, d) =>
      if r == req then some { ax := a, signer := s, current := d == digest } else none
    let wfacts := wrows.map fun w =>
      { axioms := w.axioms, awaiting := w.awaiting, shipped := w.shipped : WitnessFacts }
    let refinedBy := (refinements env).filterMap fun (t, p, cs) =>
      if p == req then some (t, cs) else none
    facts := facts.push { witnesses := wfacts, signOffs := sos, counters := crows.size, level, refinedBy }
    rows := rows.push {
      req, strength, level, digest, label, prop := ← pp info.value!
      kind := ← kindOf req
      examples := (examplesOf env).filterMap fun (d, r) => if r == req then some d else none
      witnesses := wrows
      evidence := (supporting env).filterMap fun (t, r, g) => if r == req then some (t, g) else none
      refinedBy
      counters := crows
      gaps := gaps wfacts sos crows.size level #[] }
  -- Refinement: a child is open until its own row closes; iterate to a fixpoint.
  for _ in [:rows.size + 1] do
    let before := rows.map Row.status
    let current := rows
    rows := rows.zipWith (fun (r : Row) (f : RowFacts) =>
      let refs := f.refinedBy.map fun (t, cs) =>
        { thm := t, openChildren := cs.filter fun c =>
            (current.find? (·.req == c)).map (!·.proved) |>.getD true : RefinementFacts }
      { r with gaps := gaps f.witnesses f.signOffs f.counters f.level refs }) facts
    if rows.map Row.status == before then break
  let digest := hex64 (fnv1a64 ("\n".intercalate (rows.toList.map (·.digest))))
  return { toolchain := Lean.versionString, digest, rows }

/-- `spec_statement name for Ns` defines `name : Statement` over the requirements
under namespace `Ns`, computed from this environment. -/
elab "spec_statement " name:ident " for " ns:ident : command => do
  let st ← liftTermElabM (collect ns.getId)
  let value := toExpr st
  liftTermElabM do
    addAndCompile <| .defnDecl {
      name := (← getCurrNamespace) ++ name.getId
      levelParams := []
      type := mkConst ``Statement
      value
      hints := .abbrev
      safety := .safe
    }

/-- `statement%` : the `Statement` over every requirement in scope, as a term. -/
elab "statement%" : term => do
  return toExpr (← collect Name.anonymous)

/-- `spec%` : `List LeanSpec.Core.ReqView`, one per `@[requirement]` in scope, for
the `spec` CLI. Examples written in a `Req.holds` body are spliced as the
expression the author wrote; `@[example]` declarations are appended by name. -/
elab "spec%" : term => do
  let env ← getEnv
  let exTy := mkConst ``LeanSpec.Core.Ex
  let jsonTy := mkConst ``Lean.Json
  let postTy ← mkArrow jsonTy (← mkArrow jsonTy (mkConst ``Bool))
  let mut views : Array Expr := #[]
  for (req, strength, level) in requirements env do
    let label := ((← findDocString? env req).getD "").trimAscii.toString
    let (exs?, post?) ← bodyParts req
    let attached := (examplesOf env).filterMap fun (d, r) => if r == req then some (mkConst d) else none
    let exList ← mkListLit exTy attached.toList
    let exsE ← match exs? with
      | some e => mkAppM ``List.append #[e, exList]
      | none => pure exList
    let postE ← match post? with
      | some p => mkAppM ``Option.some #[p]
      | none => mkAppOptM ``Option.none #[postTy]
    let mut wits : List (String × Bool) := []
    for (t, r) in witnesses env do
      if r == req then
        wits := wits ++ [(t.toString, ← isGeneral (← getConstInfo t).type)]
    let evs := ((supporting env).filter (·.2.1 == req)).toList.map fun (t, _, g) => (t.toString, g)
    views := views.push (← mkAppM ``LeanSpec.Core.ReqView.mk
      #[toExpr req.toString, toExpr label, toExpr strength.text, toExpr level.text,
        exsE, postE, toExpr wits, toExpr evs])
  mkListLit (mkConst ``LeanSpec.Core.ReqView) views.toList

end LeanSpec.Logic
