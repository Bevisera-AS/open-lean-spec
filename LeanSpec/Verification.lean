module

public import LeanSpec.Emit
public meta import LeanSpec.Emit

namespace LeanSpec

public section

/-!
A verification statement is the `lean-spec-verified` mark.

It records what a build actually proved, for which spec (`spec-digest`) under
which Lean toolchain (`toolchain`): each kernel theorem named by a design,
the requirement id that theorem is attached to, the proposition, and the axioms
`#print axioms` reports for it. Deferred scenarios, executable checks with no
kernel theorem, unresolved names, non-theorems, and proofs that depend on
`sorryAx` stay in `openObligations`. The mark covers the proved rows only, under
the listed axioms.
-/

/-- Wire schema. A statement that does not parse back to itself is not a mark. -/
public def verificationSchema : String := "lean-spec.verification/1"

/-- The mark token. It names the method, not an endorsement, and is meaningful
only together with the statement that follows. -/
public def verificationMark : String := "lean-spec-verified"

/-- Kernel axioms that are not, by themselves, an extra trusted base.
`native_decide` auxiliary axioms and `sorryAx` are not in this set. -/
public def isStandardAxiom (name : String) : Bool :=
  name == "propext" || name == "Classical.choice" || name == "Quot.sound"

/-- Why a row is outside the mark. -/
public inductive OpenObligationKind where
  | deferred
  | unwitnessedExecutable
  | unresolvedTheorem
  | ambiguousTheorem
  | notATheorem
  | dependsOnSorry
  deriving Repr, BEq, DecidableEq

/-- Theorem-shaped obligations name a declaration. The others name a scenario. -/
public def OpenObligationKind.aboutTheorem : OpenObligationKind → Bool
  | .unresolvedTheorem | .ambiguousTheorem | .notATheorem | .dependsOnSorry => true
  | .deferred | .unwitnessedExecutable => false

public def OpenObligationKind.toToken : OpenObligationKind → String
  | .deferred => "deferred"
  | .unwitnessedExecutable => "unwitnessed-executable"
  | .unresolvedTheorem => "unresolved-theorem"
  | .ambiguousTheorem => "ambiguous-theorem"
  | .notATheorem => "not-a-theorem"
  | .dependsOnSorry => "depends-on-sorry"

public def OpenObligationKind.ofToken? : String → Option OpenObligationKind
  | "deferred" => some .deferred
  | "unwitnessed-executable" => some .unwitnessedExecutable
  | "unresolved-theorem" => some .unresolvedTheorem
  | "ambiguous-theorem" => some .ambiguousTheorem
  | "not-a-theorem" => some .notATheorem
  | "depends-on-sorry" => some .dependsOnSorry
  | _ => none

public theorem OpenObligationKind.ofToken_toToken (k : OpenObligationKind) :
    OpenObligationKind.ofToken? k.toToken = some k := by
  cases k <;> rfl

/-- One kernel theorem the mark covers, attached to a requirement id. -/
public structure ProvedClaim where
  requirementId : String
  shall : String
  theoremName : String
  statement : String
  axioms : Array String
  deriving Repr, BEq, DecidableEq

/-- One obligation the mark does not cover. -/
public structure OpenObligation where
  requirementId : String
  shall : String
  kind : OpenObligationKind
  subject : String
  detail : String
  deriving Repr, BEq, DecidableEq

/-- The mark. `axioms` is the union of the proved rows, sorted and duplicate-free.
`toolchain` is the Lean version that checked the proofs. `specDigest` fingerprints
the canonical spec source (`emitSnapshotSource`), so a statement names the exact
spec it was built from. The commit is bound by committing the statement next to
the spec, not recorded inside it (a build artefact cannot know its own commit). -/
public structure VerificationStatement where
  proved : Array ProvedClaim
  axioms : Array String
  openObligations : Array OpenObligation
  toolchain : String := ""
  specDigest : String := ""
  deriving Repr, BEq, DecidableEq

private def fnvOffset : UInt64 := 14695981039346656037
private def fnvPrime : UInt64 := 1099511628211

/-- FNV-1a, 64-bit, over the UTF-8 bytes. A fingerprint, not a cryptographic hash:
it detects a changed spec, it does not resist a deliberate collision. -/
public def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (init := fnvOffset) fun h b => (h ^^^ b.toUInt64) * fnvPrime

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Sixteen lowercase hex digits. -/
public def hex64 (x : UInt64) : String :=
  String.ofList <| (List.range 16).reverse.map fun i => hexDigit ((x.toNat >>> (4 * i)) % 16)

/-- `fnv1a64:` + hex of the canonical spec source. -/
public def specDigestOf (snap : SpecSnapshot) : String :=
  "fnv1a64:" ++ hex64 (fnv1a64 (emitSnapshotSource snap))

/-- What `#print axioms` found for one design citation. Policy lives in `assembleStatement`. -/
public inductive TheoremFact where
  | missing
  | ambiguous (candidates : Array String)
  | resolved (name : String) (kind : String) (isTheorem : Bool)
      (statement : String) (axioms : Array String)
  deriving Repr, BEq, DecidableEq

/-- A design's theorem name, as cited, plus the environment's account of it. -/
public structure NamedTheoremFact where
  requirementId : String
  citedAs : String
  fact : TheoremFact
  deriving Repr, BEq, DecidableEq

private def strLt (a b : String) : Bool :=
  compare a b == Ordering.lt

private def sortUniqStrings (xs : Array String) : Array String :=
  let sorted := xs.qsort strLt
  sorted.foldl (init := #[]) fun acc s =>
    match acc.back? with
    | some t => if t == s then acc else acc.push s
    | none => acc.push s

private def dedup [BEq α] (xs : Array α) : Array α :=
  xs.foldl (init := #[]) fun acc x =>
    if acc.any (· == x) then acc else acc.push x

private def ltProved (a b : ProvedClaim) : Bool :=
  match compare a.requirementId b.requirementId with
  | Ordering.lt => true
  | Ordering.gt => false
  | Ordering.eq => strLt a.theoremName b.theoremName

private def ltOpen (a b : OpenObligation) : Bool :=
  match compare a.requirementId b.requirementId with
  | Ordering.lt => true
  | Ordering.gt => false
  | Ordering.eq =>
    match compare a.kind.toToken b.kind.toToken with
    | Ordering.lt => true
    | Ordering.gt => false
    | Ordering.eq => strLt a.subject b.subject

private def usesSorry (axioms : Array String) : Bool :=
  axioms.any fun name => name == "sorryAx" || name.endsWith ".sorryAx"

/-- Sorted rows, sorted axiom lists, and `axioms` equal to the union of the proved rows. -/
public def VerificationStatement.canonicalize (s : VerificationStatement) : VerificationStatement :=
  let proved :=
    (dedup (s.proved.map fun c => { c with axioms := sortUniqStrings c.axioms })).qsort ltProved
  let axioms := sortUniqStrings (proved.foldl (init := #[]) fun acc c => acc ++ c.axioms)
  let openObligations := (dedup s.openObligations).qsort ltOpen
  { s with proved, axioms, openObligations }

/-- Axioms of the proved rows beyond `propext`, `Classical.choice`, and `Quot.sound`. -/
public def VerificationStatement.extraAxioms (s : VerificationStatement) : Array String :=
  s.canonicalize.axioms.filter fun name => !isStandardAxiom name

/-- The mark covers this requirement's kernel theorem. -/
public def VerificationStatement.covers (s : VerificationStatement)
    (requirementId theoremName : String) : Bool :=
  s.proved.any fun c => c.requirementId == requirementId && c.theoremName == theoremName

/-- `covers`, matching a fully qualified theorem by its last component. -/
public def VerificationStatement.coversSuffix (s : VerificationStatement)
    (requirementId suffix : String) : Bool :=
  s.proved.any fun c =>
    c.requirementId == requirementId &&
      (c.theoremName == suffix || c.theoremName.endsWith ("." ++ suffix))

public def VerificationStatement.hasOpen (s : VerificationStatement)
    (requirementId : String) (kind : OpenObligationKind) (subject : String) : Bool :=
  s.openObligations.any fun o =>
    o.requirementId == requirementId && o.kind == kind && o.subject == subject

/-- Cited theorems resolved to kernel theorems that do not use `sorryAx`.
Deferred checks and unwitnessed executable claims do not fail this. -/
public def VerificationStatement.citationsOk (s : VerificationStatement) : Bool :=
  s.openObligations.all fun o =>
    match o.kind with
    | .deferred | .unwitnessedExecutable => true
    | .unresolvedTheorem | .ambiguousTheorem | .notATheorem | .dependsOnSorry => false

/-- A proved theorem is not also listed as a theorem-shaped open obligation. -/
public def VerificationStatement.disjoint (s : VerificationStatement) : Bool :=
  s.proved.all fun c =>
    s.openObligations.all fun o =>
      !(o.kind.aboutTheorem && o.requirementId == c.requirementId && o.subject == c.theoremName)

private def shallOf (snap : SpecSnapshot) (id : String) : String :=
  match snap.find? id with
  | some r => r.shall.value
  | none => ""

private def factFor (facts : Array NamedTheoremFact) (requirementId cited : String) : TheoremFact :=
  match facts.find? (fun f => f.requirementId == requirementId && f.citedAs == cited) with
  | some f => f.fact
  | none => .missing

private structure AssembleAcc where
  proved : Array ProvedClaim := #[]
  opens : Array OpenObligation := #[]

private def pushOpen (acc : AssembleAcc) (o : OpenObligation) : AssembleAcc :=
  { acc with opens := acc.opens.push o }

private def classify (snap : SpecSnapshot) (requirementId cited : String)
    (fact : TheoremFact) (acc : AssembleAcc) : AssembleAcc :=
  let shall := shallOf snap requirementId
  match fact with
  | .missing =>
    pushOpen acc {
      requirementId, shall, kind := .unresolvedTheorem, subject := cited
      detail := s!"no declaration named {cited}"
    }
  | .ambiguous candidates =>
    let names := sortUniqStrings candidates
    pushOpen acc {
      requirementId, shall, kind := .ambiguousTheorem, subject := cited
      detail := joinSep ", " names.toList
    }
  | .resolved name kind isTheorem statement axioms =>
    if usesSorry axioms then
      pushOpen acc {
        requirementId, shall, kind := .dependsOnSorry, subject := name
        detail := joinSep " " (sortUniqStrings axioms).toList
      }
    else if !isTheorem then
      pushOpen acc {
        requirementId, shall, kind := .notATheorem, subject := name
        detail := s!"{kind} is not a kernel theorem"
      }
    else
      { acc with proved := acc.proved.push {
          requirementId, shall, theoremName := name, statement
          axioms := sortUniqStrings axioms
        } }

private def witnessed (proved : Array ProvedClaim) (requirementId : String) : Bool :=
  proved.any (·.requirementId == requirementId)

private def addScenarios (snap : SpecSnapshot) (proved : Array ProvedClaim)
    (acc : AssembleAcc) : AssembleAcc :=
  snap.requirements.foldl (init := acc) fun acc r =>
    let covered := witnessed proved r.id.value
    r.scenarios.toArray.foldl (init := acc) fun acc scenario =>
      match scenario.check with
      | .deferred reason =>
        pushOpen acc {
          requirementId := r.id.value
          shall := r.shall.value
          kind := .deferred
          subject := scenario.name.value
          detail := reason.value
        }
      | .executable =>
        if covered then acc
        else
          pushOpen acc {
            requirementId := r.id.value
            shall := r.shall.value
            kind := .unwitnessedExecutable
            subject := scenario.name.value
            detail := "executable is a claim that a checker exists; no kernel theorem on the design covers this requirement"
          }

/-- Build the statement from a snapshot and the environment's account of each cited theorem.
Rows are sorted. `axioms` is the union of the proved rows. -/
public def assembleStatement (snap : SpecSnapshot) (facts : Array NamedTheoremFact) :
    VerificationStatement :=
  let acc := snap.designs.foldl (init := {}) fun acc design =>
    design.theorems.foldl (init := acc) fun acc thm =>
      classify snap design.id.value thm.value (factFor facts design.id.value thm.value) acc
  let acc := addScenarios snap acc.proved acc
  VerificationStatement.canonicalize {
    proved := acc.proved
    axioms := #[]
    openObligations := acc.opens
    toolchain := Lean.versionString
    specDigest := specDigestOf snap
  }

private def emitNameBlock (lines : Array String) (header : String) (names : Array String) :
    Array String :=
  let lines := lines.push header
  let lines := names.foldl (init := lines) fun acc name => acc.push name
  lines.push "end"

private def emitProved (lines : Array String) (claims : Array ProvedClaim) : Array String :=
  let lines := lines.push "proved"
  let lines := claims.foldl (init := lines) fun acc c =>
    acc.push "entry"
      |>.push s!"requirement {c.requirementId}"
      |>.push s!"shall {emitQuoted c.shall}"
      |>.push s!"theorem {c.theoremName}"
      |>.push s!"statement {emitQuoted c.statement}"
      |>.push (if c.axioms.isEmpty then "axioms" else s!"axioms {joinSep " " c.axioms.toList}")
  lines.push "end"

private def emitOpen (lines : Array String) (rows : Array OpenObligation) : Array String :=
  let lines := lines.push "open"
  let lines := rows.foldl (init := lines) fun acc o =>
    acc.push "entry"
      |>.push s!"requirement {o.requirementId}"
      |>.push s!"shall {emitQuoted o.shall}"
      |>.push s!"kind {o.kind.toToken}"
      |>.push s!"subject {emitQuoted o.subject}"
      |>.push s!"detail {emitQuoted o.detail}"
  lines.push "end"

/-- Canonical text. Comments (`#`) are not part of the statement; the parser skips them. -/
public def emitVerificationStatement (s : VerificationStatement) : String :=
  let s := s.canonicalize
  let lines : Array String := #[
    s!"schema {verificationSchema}",
    s!"mark {verificationMark}",
    s!"toolchain {s.toolchain}".trimAsciiEnd.copy,
    s!"spec-digest {s.specDigest}".trimAsciiEnd.copy,
    s!"# {verificationMark} covers only the proved rows, for this spec digest and toolchain, under the axioms below. Open obligations are outside the mark."
  ]
  let lines := emitProved lines s.proved
  let lines := emitNameBlock lines "axioms" s.axioms
  let lines := emitNameBlock lines "extra-axioms" s.extraAxioms
  let lines := emitOpen lines s.openObligations
  joinSep "\n" lines.toList ++ "\n"

private def prepare (source : String) : List String :=
  (source.replace "\r\n" "\n").splitOn "\n" |>.filterMap fun raw =>
    let line := raw.trimAscii.copy
    if line.isEmpty || line.startsWith "#" then none else some line

private def unquote (s : String) : Except String String :=
  let rec go (acc : List Char) : List Char → Except String String
    | [] => .error "unterminated string"
    | '"' :: rest =>
      if rest.all Char.isWhitespace then .ok (String.ofList acc.reverse)
      else .error "trailing data after string"
    | '\\' :: [] => .error "unterminated escape"
    | '\\' :: c :: rest =>
      match unescapeLeanChar c with
      | .error detail => .error detail
      | .ok decoded => go (decoded :: acc) rest
    | c :: rest => go (c :: acc) rest
  match s.toList with
  | '"' :: rest => go [] rest
  | _ => .error s!"expected quoted string, got `{s}`"

private def expectWord (word : String) : List String → Except String (List String)
  | w :: rest => if w == word then .ok rest else .error s!"expected `{word}`, got `{w}`"
  | [] => .error s!"expected `{word}`"

private def field (key : String) (line : String) : Except String String :=
  let padded := key ++ " "
  if line.startsWith padded then .ok (line.dropPrefix padded).copy
  else .error s!"expected `{key}`, got `{line}`"

/-- `key value`, or a bare `key` for an empty value. -/
private def optField (key : String) (line : String) : Except String String :=
  if line == key then .ok "" else field key line

private def quotedField (key : String) (line : String) : Except String String := do
  unquote (← field key line)

private def axiomField (line : String) : Except String (Array String) :=
  if line == "axioms" then .ok #[]
  else if line.startsWith "axioms " then
    .ok ((line.dropPrefix "axioms ").copy.splitOn " " |>.filter (· != "") |>.toArray)
  else
    .error s!"expected axioms, got `{line}`"

private def takeEntry (what : String) (lines : List String) : Except String (List String × List String) :=
  if lines.length < 5 then .error s!"{what}: truncated entry"
  else .ok (lines.take 5, lines.drop 5)

private def parseClaim (lines : List String) : Except String (ProvedClaim × List String) := do
  let (chunk, rest) ← takeEntry "proved" lines
  match chunk with
  | [req, shall, thm, stmt, axs] =>
    let requirementId ← field "requirement" req
    let shall ← quotedField "shall" shall
    let theoremName ← field "theorem" thm
    let statement ← quotedField "statement" stmt
    let axioms ← axiomField axs
    .ok ({ requirementId, shall, theoremName, statement, axioms }, rest)
  | _ => .error "proved: truncated entry"

private def parseOpen (lines : List String) : Except String (OpenObligation × List String) := do
  let (chunk, rest) ← takeEntry "open" lines
  match chunk with
  | [req, shall, kindLine, subjectLine, detailLine] =>
    let requirementId ← field "requirement" req
    let shall ← quotedField "shall" shall
    let kindToken ← field "kind" kindLine
    let kind ←
      match OpenObligationKind.ofToken? kindToken with
      | some kind => .ok kind
      | none => .error s!"unknown obligation kind `{kindToken}`"
    let subject ← quotedField "subject" subjectLine
    let detail ← quotedField "detail" detailLine
    .ok ({ requirementId, shall, kind, subject, detail }, rest)
  | _ => .error "open: truncated entry"

private def parseEntries {α} (what : String)
    (parseOne : List String → Except String (α × List String))
    (lines : List String) : Except String (Array α × List String) :=
  let rec go (fuel : Nat) (acc : Array α) (lines : List String) :
      Except String (Array α × List String) :=
    match fuel with
    | 0 => .error s!"{what}: expected `end`"
    | fuel + 1 =>
      match lines with
      | [] => .error s!"{what}: expected `end`"
      | "end" :: rest => .ok (acc, rest)
      | "entry" :: rest => do
        let (item, rest) ← parseOne rest
        go fuel (acc.push item) rest
      | other :: _ => .error s!"{what}: unexpected `{other}`"
  go (lines.length + 1) #[] lines

private def parseNames (what : String) (lines : List String) :
    Except String (Array String × List String) :=
  let rec go (fuel : Nat) (acc : Array String) (lines : List String) :
      Except String (Array String × List String) :=
    match fuel with
    | 0 => .error s!"{what}: expected `end`"
    | fuel + 1 =>
      match lines with
      | [] => .error s!"{what}: expected `end`"
      | "end" :: rest => .ok (acc, rest)
      | line :: rest =>
        if line.any (· == ' ') || line == "entry" then
          .error s!"{what}: expected a name or `end`, got `{line}`"
        else
          go fuel (acc.push line) rest
  go (lines.length + 1) #[] lines

private def sameNames (left right : Array String) : Bool :=
  sortUniqStrings left == sortUniqStrings right

/-- Parse a statement. Sections may be reordered only by the canonicalizer:
the schema, mark, and section order are fixed. A lying `axioms` or `extra-axioms`
section is rejected. -/
public def parseVerificationStatement (source : String) : Except String VerificationStatement := do
  let lines := prepare source
  let rest ←
    match lines with
    | schema :: mark :: rest =>
      if schema != s!"schema {verificationSchema}" then
        .error s!"expected schema {verificationSchema}"
      else if mark != s!"mark {verificationMark}" then
        .error s!"expected mark {verificationMark}"
      else
        .ok rest
    | _ => .error "expected schema and mark"
  let (toolchain, rest) ←
    match rest with
    | line :: rest => do .ok ((← optField "toolchain" line), rest)
    | [] => .error "expected `toolchain`"
  let (specDigest, rest) ←
    match rest with
    | line :: rest => do .ok ((← optField "spec-digest" line), rest)
    | [] => .error "expected `spec-digest`"
  let rest ← expectWord "proved" rest
  let (proved, rest) ← parseEntries "proved" parseClaim rest
  let rest ← expectWord "axioms" rest
  let (axioms, rest) ← parseNames "axioms" rest
  let rest ← expectWord "extra-axioms" rest
  let (extra, rest) ← parseNames "extra-axioms" rest
  let rest ← expectWord "open" rest
  let (openObligations, rest) ← parseEntries "open" parseOpen rest
  match rest with
  | other :: _ => .error s!"trailing `{other}`"
  | [] => do
    let statement := VerificationStatement.canonicalize
      { proved, axioms := #[], openObligations, toolchain, specDigest }
    if !sameNames axioms statement.axioms then
      .error "axioms section does not match the proved rows"
    else if !sameNames extra statement.extraAxioms then
      .error "extra-axioms section does not match the proved rows"
    else
      .ok statement

/-- Parsing the canonical text yields the canonical statement. -/
public def VerificationStatement.checkable (s : VerificationStatement) : Bool :=
  match parseVerificationStatement (emitVerificationStatement s) with
  | .ok parsed => parsed == s.canonicalize
  | .error _ => false

/-- `text` is the canonical artefact for `s`. -/
public def VerificationStatement.certifies (s : VerificationStatement) (text : String) : Bool :=
  s.checkable && text == emitVerificationStatement s

end

end LeanSpec
