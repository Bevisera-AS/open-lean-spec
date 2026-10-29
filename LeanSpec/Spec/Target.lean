import LeanSpec.Logic.Core

/-!
# The target language, as a spec of lean-spec

A change to the library, proposed in the library's own terms. `Sig` is what
`LeanSpec.Logic.Core` would expose about the language a product is written in; the
requirements are `Prop`s over it; the 1.x policy (a closed range) and three other
wrong designs are counter-models; `proposal` is a model that satisfies every row.

Phase: propose. The product is the library itself, a Lean value, so the bar is
`proved`; until `Logic.Core` carries a `@[shipped]` `Target`, every row is `model`
and the statement says so. Apply moves `proposal` into `Logic.Core` and closes the
rows against the shipped code.
-/

namespace LeanSpec.Spec.Target

open LeanSpec.Logic

spec_bar proved

/-- What the library exposes about the target language. -/
structure Sig where
  Target : Type
  /-- Read `spec_target NAME [via strata]`. -/
  parse  : String → Bool → Option Target
  /-- The target the product is: the Lean value itself. -/
  lean   : Target
  text   : Target → String
  /-- Lean, TypeScript, Scala, Rust, Java and Python through Strata. -/
  inRange : Target → Bool
  /-- The highest bar evidence about the Lean side can reach on this target. -/
  reach  : Target → Bar
  /-- What the statement says was lost on this target. -/
  limits : Target → List String
  /-- `@[shipped]` is a true claim on this target. -/
  shippedHolds : Target → Bool
  /-- A row with this bar can be met on this target. -/
  reachable : Bar → Target → Bool
  mark   : Bar → Target → String

/-- `NAME [via strata]` names a target in the range. -/
def inRangeName (S : Sig) (name : String) (viaStrata : Bool) : Prop :=
  ∃ t, S.parse name viaStrata = some t ∧ S.inRange t = true

/-- On a Lean product the kernel sees the product: `proved` is reachable, nothing is lost. -/
@[requirement must]
def leanReachesProved (S : Sig) : Prop :=
  S.inRange S.lean = true ∧ S.reach S.lean = .proved ∧ S.shippedHolds S.lean = true ∧
    S.limits S.lean = []

/-- The 1.x range: Lean; TypeScript; Scala; Rust; Java and Python only through Strata. -/
@[requirement must]
def rangeIsTheOld (S : Sig) : Prop :=
  inRangeName S "lean" false ∧ inRangeName S "typescript" false ∧
    inRangeName S "scala" false ∧ inRangeName S "rust" false ∧
    inRangeName S "java" true ∧ inRangeName S "python" true ∧
    ¬ inRangeName S "java" false ∧ ¬ inRangeName S "python" false ∧
    ¬ inRangeName S "cpp" false

/-- A name outside the range is accepted, not refused; the limits say what it costs. -/
@[requirement must]
def everyNameAccepted (S : Sig) : Prop :=
  ∀ name viaStrata, S.parse name viaStrata ≠ none

/-- On any other target the Lean side is a model: `@[shipped]` does not hold and the
statement says so. -/
@[requirement must]
def nonLeanIsAModel (S : Sig) : Prop :=
  ∀ t, t ≠ S.lean → S.shippedHolds t = false ∧ S.limits t ≠ []

/-- A typed target in the range carries a theorem about the model as far as `evidenced`. -/
@[requirement must]
def typedReachesEvidenced (S : Sig) : Prop :=
  ∀ t, S.inRange t = true → t ≠ S.lean → S.reach t = .evidenced

/-- Outside the range only the examples bind the program: `tested`, with the limits recorded. -/
@[requirement must]
def outsideRangeReachesTested (S : Sig) : Prop :=
  ∀ t, S.inRange t = false → S.reach t = .tested ∧ S.limits t ≠ []

/-- A bar is reachable exactly up to the target's reach. -/
@[requirement must]
def reachIsTheCeiling (S : Sig) : Prop :=
  ∀ b t, S.reachable b t = decide (b.rank ≤ (S.reach t).rank)

/-- The mark names the bar and the target it was reached on. -/
@[requirement must]
def markNamesTarget (S : Sig) : Prop :=
  ∀ b t, S.mark b t = s!"lean-spec-verified at {b.text} ({S.text t})"

/-- User level: whenever `proved` is out of reach, the statement says what was lost. -/
@[requirement must user]
def statementSaysWhatWasLost (S : Sig) : Prop :=
  ∀ t, S.reach t ≠ .proved → S.limits t ≠ []

/-- Traceability: a target below `proved` is not Lean, and a non-Lean target has limits. -/
@[refines]
theorem saysWhatWasLost_from_system (S : Sig) (h1 : leanReachesProved S)
    (h2 : nonLeanIsAModel S) : statementSaysWhatWasLost S := by
  intro t ht
  have hne : t ≠ S.lean := fun e => ht (e ▸ h1.2.1)
  exact (h2 t hne).2

-- ─── The proposal: a model that satisfies every row ───────────────────────────

inductive T where
  | lean | typescript | scala | rust | javaStrata | pythonStrata
  /-- Outside the range; the name as written. -/
  | other (name : String)
  deriving DecidableEq, Repr

def parseT : String → Bool → Option T
  | "lean", _ => some .lean
  | "typescript", _ => some .typescript
  | "scala", _ => some .scala
  | "rust", _ => some .rust
  | "java", true => some .javaStrata
  | "python", true => some .pythonStrata
  | name, _ => some (.other name)

def textT : T → String
  | .lean => "lean"
  | .typescript => "typescript"
  | .scala => "scala"
  | .rust => "rust"
  | .javaStrata => "java via strata"
  | .pythonStrata => "python via strata"
  | .other name => s!"other: {name}"

def inRangeT : T → Bool
  | .other _ => false
  | _ => true

def reachT : T → Bar
  | .lean => .proved
  | .other _ => .tested
  | _ => .evidenced

def modelLimit : String :=
  "the Lean side is a model of the product: a @[satisfies] theorem is model-only and " ++
    "proved is out of reach; the examples are what binds the program"

def limitsT : T → List String
  | .lean => []
  | .javaStrata | .pythonStrata =>
    [modelLimit, "the Strata verification is a claim lean-spec records and does not check"]
  | .other _ =>
    [modelLimit, "outside the range: no type system carries a theorem about the model to " ++
      "the program, so tested is the reach"]
  | _ => [modelLimit]

def proposal : Sig where
  Target := T
  parse := parseT
  lean := .lean
  text := textT
  inRange := inRangeT
  reach := reachT
  limits := limitsT
  shippedHolds t := t == .lean
  reachable b t := decide (b.rank ≤ (reachT t).rank)
  mark b t := s!"lean-spec-verified at {b.text} ({textT t})"

@[satisfies] theorem proposal_leanReachesProved : leanReachesProved proposal :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A name the proposal reads as `other` is outside the range. -/
theorem proposal_other_notInRange (name : String) (viaStrata : Bool)
    (h : parseT name viaStrata = some (.other name)) : ¬ inRangeName proposal name viaStrata := by
  rintro ⟨t, ht, hr⟩
  change parseT name viaStrata = some t at ht
  rw [h] at ht
  cases ht
  simp [proposal, inRangeT] at hr

@[satisfies] theorem proposal_rangeIsTheOld : rangeIsTheOld proposal :=
  ⟨⟨.lean, rfl, rfl⟩, ⟨.typescript, rfl, rfl⟩, ⟨.scala, rfl, rfl⟩, ⟨.rust, rfl, rfl⟩,
    ⟨.javaStrata, rfl, rfl⟩, ⟨.pythonStrata, rfl, rfl⟩,
    proposal_other_notInRange "java" false rfl, proposal_other_notInRange "python" false rfl,
    proposal_other_notInRange "cpp" false rfl⟩

@[satisfies] theorem proposal_everyNameAccepted : everyNameAccepted proposal := by
  intro name viaStrata
  show parseT name viaStrata ≠ none
  unfold parseT
  split <;> simp

@[satisfies] theorem proposal_nonLeanIsAModel : nonLeanIsAModel proposal := by
  intro t ht
  cases t <;> simp_all [proposal, limitsT]

@[satisfies] theorem proposal_typedReachesEvidenced : typedReachesEvidenced proposal := by
  intro t hin hne
  cases t <;> simp_all [proposal, inRangeT, reachT]

@[satisfies] theorem proposal_outsideRangeReachesTested : outsideRangeReachesTested proposal := by
  intro t hout
  cases t <;> simp_all [proposal, inRangeT, reachT, limitsT]

@[satisfies] theorem proposal_reachIsTheCeiling : reachIsTheCeiling proposal :=
  fun _ _ => rfl

@[satisfies] theorem proposal_markNamesTarget : markNamesTarget proposal :=
  fun _ _ => rfl

-- ─── Counter-models ──────────────────────────────────────────────────────────

/-- The 1.x policy: a closed range, an unlisted name is refused. -/
def closed1x : Sig := { proposal with
  parse name viaStrata := match parseT name viaStrata with
    | some (.other _) => none
    | t => t }

/-- Every target reaches `proved`. -/
def optimist : Sig := { proposal with reach := fun _ => .proved }

/-- Never says what was lost. -/
def silent : Sig := { proposal with limits := fun _ => [] }

/-- Every bar is reachable on every target. -/
def flat : Sig := { proposal with reachable := fun _ _ => true }

/-- The mark without the target. -/
def anonymous : Sig := { proposal with mark := fun b _ => s!"lean-spec-verified at {b.text}" }

/-- Claims the TypeScript program is the Lean value. -/
def pretender : Sig := { proposal with shippedHolds := fun _ => true }

/-- Holds even the Lean product to a model's reach. -/
def humble : Sig := { proposal with reach := fun _ => .evidenced }

/-- Trusts no type system but Lean's. -/
def leanOnly : Sig := { proposal with inRange := fun (t : T) => t == .lean }

theorem typescript_ne_lean : (T.typescript : T) ≠ .lean := by decide

@[refutes] theorem closed1x_fails : ¬ everyNameAccepted closed1x := by
  intro h
  exact h "cpp" false rfl

@[refutes] theorem optimist_fails : ¬ typedReachesEvidenced optimist := by
  intro h
  have := h .typescript rfl typescript_ne_lean
  simp [optimist, proposal] at this

@[refutes] theorem optimist_fails_outside : ¬ outsideRangeReachesTested optimist := by
  intro h
  have := (h (.other "cpp") rfl).1
  simp [optimist, proposal] at this

@[refutes] theorem silent_fails : ¬ nonLeanIsAModel silent := by
  intro h
  exact (h .typescript typescript_ne_lean).2 rfl

@[refutes] theorem silent_fails_user : ¬ statementSaysWhatWasLost silent := by
  intro h
  exact h (.other "cpp") (by decide) rfl

@[refutes] theorem flat_fails : ¬ reachIsTheCeiling flat := by
  intro h
  have := h .proved (.other "cpp")
  simp [flat, proposal, reachT, Bar.rank] at this

@[refutes] theorem anonymous_fails : ¬ markNamesTarget anonymous := by
  intro h
  exact absurd (h .tested .typescript) (by decide)

@[refutes] theorem pretender_fails : ¬ nonLeanIsAModel pretender := by
  intro h
  exact absurd (h .typescript typescript_ne_lean).1 (by decide)

@[refutes] theorem humble_fails : ¬ leanReachesProved humble := by
  intro h
  exact absurd h.2.1 (by decide)

@[refutes] theorem leanOnly_fails : ¬ rangeIsTheOld leanOnly := by
  intro h
  obtain ⟨t, ht, hr⟩ := h.2.1
  change parseT "typescript" false = some t at ht
  cases ht
  simp [leanOnly] at hr

-- ─── The statement: the review record ────────────────────────────────────────

spec_statement statement for LeanSpec.Spec.Target

-- Propose phase: the proposal is a model, the product does not carry it yet. Every
-- system row is `model`, which meets `evidenced` and not the bar `proved`; the user
-- row is refined from two of them. The mark is withheld, and that is the record.
#guard statement.rows.size == 9
#guard statement.rows.all (·.bar == .proved)
#guard !statement.verified
#guard statement.mark == "none"
#guard statement.rows.all fun r => r.level == .user || r.status == "model"
#guard statement.statusOf ``statementSaysWhatWasLost == "refined"
#guard statement.rows.all fun r => !r.gaps.any (Gap.blocksAt .evidenced)
#guard statement.rows.all fun r => !r.gaps.contains .vacuous

end LeanSpec.Spec.Target
