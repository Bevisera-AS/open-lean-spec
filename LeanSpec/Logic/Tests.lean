import LeanSpec.Logic.Core
import LeanSpec.Core.Check

/-! Checks that the attributes refuse misattached evidence and that gaps are computed. -/

namespace LeanSpec.Logic.Tests

open LeanSpec.Logic

structure Sig where
  f : Nat → Nat

/-- `f` is the identity. -/
@[requirement must]
def isId (S : Sig) : Prop := ∀ n, S.f n = n

def notARequirement (S : Sig) : Prop := S.f 0 = 0

/-- error: LeanSpec.Logic.Tests.wrong is about LeanSpec.Logic.Tests.notARequirement, which is not a @[requirement] -/
#guard_msgs in
@[satisfies] theorem wrong : notARequirement ⟨id⟩ := rfl

/-- error: @[requirement] goes on a `def R : Sig → Prop`, not a LeanSpec.Logic.Tests.notDef -/
#guard_msgs in
@[requirement must] theorem notDef : True := trivial

/-- error: @[refutes] needs a statement `¬ R bad` -/
#guard_msgs in
@[refutes] theorem notNegated : isId ⟨id⟩ := fun _ => rfl

/-- error: @[requirement] LeanSpec.Logic.Tests.notProp must have type `Sig → Prop` -/
#guard_msgs in
@[requirement must] def notProp (S : Sig) : Nat := S.f 0

/-- warning: declaration uses `sorry` -/
#guard_msgs in
@[satisfies] theorem sorried : isId ⟨fun n => n + 0⟩ := sorry

/-- The `f 0 = 0` clause. No counter-model on purpose. -/
@[requirement should]
def fixesZero (S : Sig) : Prop := S.f 0 = 0

axiom trustMe : fixesZero ⟨id⟩

@[satisfies] theorem trusted : fixesZero ⟨id⟩ := trustMe

/-- Requirement with no witness. -/
@[requirement must]
def isDouble (S : Sig) : Prop := ∀ n, S.f n = 2 * n

@[refutes] theorem id_not_double : ¬ isDouble ⟨id⟩ := fun h => by cases h 1

spec_statement st for LeanSpec.Logic.Tests

#guard !st.verified
#guard st.gapsOf ``isId == #[.usesSorry, .modelOnly, .vacuous]
#guard st.gapsOf ``isDouble == #[.noWitness]
#guard (st.gapsOf ``fixesZero).contains (.nonStandardAxiom ``trustMe)
#guard (st.gapsOf ``fixesZero).contains .vacuous
#guard st.row? ``notARequirement |>.isNone

-- ─── Sign-offs ───────────────────────────────────────────────────────────────

/-- `f 1 = 1`, by judgement. -/
@[requirement must]
def looksRight (S : Sig) : Prop := S.f 1 = 1

/-- `f 2 = 2`, by judgement. -/
@[requirement must]
def looksFine (S : Sig) : Prop := S.f 2 = 2

/-- `f 3 = 3`, by judgement. -/
@[requirement must]
def looksOk (S : Sig) : Prop := S.f 3 = 3

-- Waiting: the proof needs a sign-off nobody gave.
@[satisfies] theorem waits (h : SignOff looksRight ⟨id⟩) : looksRight ⟨id⟩ := h.holds

-- Stale: the digest quoted is not the requirement's.
@[sign_off alice "fnv1a64:0000000000000000"]
axiom oldReview : SignOff looksFine ⟨id⟩
@[satisfies] theorem stale : looksFine ⟨id⟩ := oldReview.holds

/-- error: @[sign_off] needs an axiom of type `SignOff R impl` -/
#guard_msgs in
@[sign_off bob "x"] axiom notSignOff : looksOk ⟨id⟩

/-- error: @[sign_off] goes on an `axiom` -/
#guard_msgs in
@[sign_off bob "x"] theorem notAxiom : True := trivial

-- ─── Model only ──────────────────────────────────────────────────────────────

@[shipped] def shippedId : Sig := ⟨id⟩
@[satisfies] theorem shippedOk : looksOk shippedId := rfl

/-- error: @[shipped] goes on a `def` -/
#guard_msgs in
@[shipped] theorem notDefShipped : True := trivial

spec_statement st2 for LeanSpec.Logic.Tests

#guard (st2.gapsOf ``looksRight).contains .awaitingSignOff
#guard st2.statusOf ``looksRight == "open"
#guard (st2.gapsOf ``looksFine).contains (.staleSignOff `alice)
#guard !(st2.gapsOf ``looksFine).any (· matches .nonStandardAxiom _)
#guard st2.statusOf ``looksFine == "open"
#guard !(st2.gapsOf ``looksOk).contains .modelOnly
#guard (st2.gapsOf ``isId).contains .modelOnly
#guard st.digest != st2.digest

-- ─── The pure gap function, without the environment ──────────────────────────

def wf (axs : Array Lean.Name) (shipped := true) (awaiting := false) : WitnessFacts :=
  { axioms := axs, awaiting, shipped }

#guard gaps #[] #[] 1 == #[.noWitness]
#guard gaps #[wf #[``propext]] #[] 1 == #[]
#guard gaps #[wf #[``propext] (shipped := false)] #[] 1 == #[.modelOnly]
#guard gaps #[wf #[`rev]] #[⟨`rev, `ann, true⟩] 1 == #[.signedOff `ann]
#guard gaps #[wf #[`rev]] #[⟨`rev, `ann, false⟩] 1 == #[.staleSignOff `ann]
#guard gaps #[wf #[] (awaiting := true)] #[] 1 == #[.awaitingSignOff]
#guard (gaps #[wf #[`rev] (shipped := false)] #[⟨`rev, `ann, true⟩] 0).all (!·.blocks)
#guard fnv1a64 "" == 14695981039346656037


-- ─── Black-box requirements: examples, IOReq, evidence ───────────────────────

section BlackBox
open LeanSpec.Core

/-- add two numbers -/
@[requirement must]
def add : IOSig → Prop := Req.holds [
  ex "basic" (json% {"op": "add", "xs": [1, 2]}) (json% {"result": 3})]

@[example add]
def add_neg : Ex := ex "neg" (json% {"op": "add", "xs": [-1, 1]}) (json% {"result": 0})

/-- the output echoes the input -/
@[requirement should]
def echo : IOSig → Prop := IOReq (fun _ => true) (fun i o => i == o)

@[example echo]
def echo_one : Ex := ex "echo-one" (json% {"n": 1}) (json% {"n": 1})

def addInts (a b : Int) : Int := a + b

@[evidence add] theorem addInts_comm (a b : Int) : addInts a b = addInts b a := by
  unfold addInts; omega

@[evidence add echo] theorem addInts_zero : addInts 0 0 = 0 := rfl

/-- error: LeanSpec.Logic.Tests.badEx is an example of LeanSpec.Logic.Tests.notARequirement, which is not a @[requirement] -/
#guard_msgs in
@[example notARequirement] def badEx : Ex := ex "x" Lean.Json.null Lean.Json.null

/-- error: @[example] goes on a `def e : Ex` -/
#guard_msgs in
@[example add] def notEx : Nat := 0

/-- error: @[evidence]: LeanSpec.Logic.Tests.sorried2 depends on sorryAx; a sorry'd proof is not evidence -/
#guard_msgs (error) in
@[evidence add] theorem sorried2 : addInts 1 1 = 2 := by sorry

/-- error: @[evidence] goes on a theorem -/
#guard_msgs in
@[evidence add] def notThm : Nat := 0

def view := spec%
def addView := view.find? (·.name == "LeanSpec.Logic.Tests.add")

#guard addView.map (·.examples.map (·.name)) == some ["basic", "neg"]
#guard addView.map (·.evidence) ==
  some [("LeanSpec.Logic.Tests.addInts_comm", true), ("LeanSpec.Logic.Tests.addInts_zero", false)]
#guard addView.map (·.strength) == some "must"
#guard addView.map (·.label) == some "add two numbers"
#guard (view.find? (·.name == "LeanSpec.Logic.Tests.echo")).map (·.post.isSome) == some true
#guard problems (view.filter fun v => v.name.endsWith ".add" || v.name.endsWith ".echo") == []
#guard (problems view).contains
  "requirement 'LeanSpec.Logic.Tests.isDouble': needs at least one example or a @[satisfies] theorem"

spec_statement st3 for LeanSpec.Logic.Tests
#guard (st3.row? ``add).map (·.kind) == some "examples"
#guard (st3.row? ``echo).map (·.kind) == some "io"
#guard (st3.row? ``isId).map (·.kind) == some "prop"
#guard (st3.row? ``add).map (·.examples) == some #[``add_neg]
#guard (st3.row? ``echo).map (·.evidence.size) == some 1
#guard (statement%.row? ``add).isSome

end BlackBox

-- ─── Levels and refinement ───────────────────────────────────────────────────

section Refinement

/-- `f 0 = 0` at user level, with no refinement and no witness. -/
@[requirement must user]
def userUnrefined (S : Sig) : Prop := S.f 0 = 0

/-- `f 5 = 5` at user level, refined from `isId`, which is open. -/
@[requirement should user]
def userFromId (S : Sig) : Prop := S.f 5 = 5

@[refines] theorem userFromId_of_isId (S : Sig) (h : isId S) : userFromId S := h 5

/-- `f 3 = 3` at user level, refined from `looksOk`, which is proved. -/
@[requirement must user]
def userThree (S : Sig) : Prop := S.f 3 = 3

@[refines] theorem userThree_of_looksOk (S : Sig) (h : looksOk S) : userThree S := h

/-- error: @[refines] needs a statement `… → U S` whose conclusion is a @[requirement] -/
#guard_msgs in
@[refines] theorem badRefine (S : Sig) (h : isId S) : S.f 1 = 1 := h 1

/-- error: @[refines] LeanSpec.Logic.Tests.noChild: no premise is a @[requirement]; nothing refines LeanSpec.Logic.Tests.userFromId -/
#guard_msgs in
@[refines] theorem noChild (S : Sig) (h : S.f 5 = 5) : userFromId S := h

/-- error: unknown level `later`; expected `system` or `user` -/
#guard_msgs in
@[requirement must later] def badLevel (S : Sig) : Prop := S.f 0 = 0

spec_statement st4 for LeanSpec.Logic.Tests

#guard st4.gapsOf ``userUnrefined == #[.noWitness, .unrefined, .vacuous]
#guard st4.statusOf ``userUnrefined == "open"
#guard (st4.row? ``userFromId).map (·.level) == some .user
#guard st4.gapsOf ``userFromId == #[.childOpen ``isId, .vacuous]
#guard st4.statusOf ``userFromId == "open"
#guard (st4.row? ``userFromId).map (·.refinedBy) == some #[(``userFromId_of_isId, #[``isId])]
#guard st4.statusOf ``userThree == "refined"
#guard (st4.gapsOf ``userThree).contains (.viaRefinement ``userThree_of_looksOk)
#guard (st4.row? ``isId).map (·.level) == some .system
#guard (spec%.find? (·.name == "LeanSpec.Logic.Tests.userThree")).map (·.level) == some "user"

#guard gaps #[] #[] 1 .user == #[.noWitness, .unrefined]
#guard gaps #[] #[] 1 .system #[⟨`t, #[]⟩] == #[.viaRefinement `t]
#guard gaps #[] #[] 1 .user #[⟨`t, #[`c]⟩] == #[.childOpen `c]
#guard gaps #[wf #[``propext]] #[] 1 .user #[⟨`t, #[`c]⟩] == #[]

end Refinement

-- ─── The digest covers attached examples ─────────────────────────────────────

section Digest
open LeanSpec.Core

/-- echo at one point -/
@[requirement should]
def echoOnce : IOSig → Prop := Req.holds [ex "one" (json% {"n": 1}) (json% {"n": 1})]

spec_statement before for LeanSpec.Logic.Tests

@[example echoOnce]
def echoOnce_two : Ex := ex "two" (json% {"n": 2}) (json% {"n": 2})

spec_statement after for LeanSpec.Logic.Tests

#guard (before.row? ``echoOnce).map (·.digest) != (after.row? ``echoOnce).map (·.digest)
#guard (before.row? ``isId).map (·.digest) == (after.row? ``isId).map (·.digest)
#guard (after.row? ``echoOnce).map (·.examples) == some #[``echoOnce_two]

end Digest

end LeanSpec.Logic.Tests
