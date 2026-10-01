import LeanSpec.Verification
import LeanSpec.Demo.Verification

namespace LeanSpec.Tests.Verification

open LeanSpec
open LeanSpec.Demo.Verification

def deferredOnly : SpecSnapshot := {
  requirements := #[{
    id := ⟨"req.later", by native_decide⟩
    shall := ⟨"say \"later\"", by native_decide⟩
    scenarios := ⟨#[{
      name := ⟨"not yet", by native_decide⟩
      whenText := ⟨"when", by native_decide⟩
      thenText := ⟨"then", by native_decide⟩
      check := .deferred ⟨"fixture missing", by native_decide⟩
    }], by native_decide⟩
  }]
  uniqueIds := by native_decide
}

def deferredStmt : VerificationStatement :=
  assembleStatement deferredOnly #[]

def witnessedSnap : SpecSnapshot := {
  requirements := #[{
    id := ⟨"req.done", by native_decide⟩
    shall := ⟨"it holds", by native_decide⟩
    scenarios := ⟨#[
      { name := ⟨"runs", by native_decide⟩
        whenText := ⟨"when", by native_decide⟩
        thenText := ⟨"then", by native_decide⟩
        check := .executable },
      { name := ⟨"later", by native_decide⟩
        whenText := ⟨"when", by native_decide⟩
        thenText := ⟨"then", by native_decide⟩
        check := .deferred ⟨"still open", by native_decide⟩ }
    ], by native_decide⟩
  }]
  uniqueIds := by native_decide
  designs := #[{
    id := ⟨"req.done", by native_decide⟩
    interfaces := ⟨#[⟨"Iface", by native_decide⟩], by native_decide⟩
    tests := ⟨#[⟨"test", by native_decide⟩], by native_decide⟩
    theorems := #[⟨"holds", by native_decide⟩]
  }]
  uniqueDesignIds := by native_decide
  designsLinked := by native_decide
}

def witnessedStmt : VerificationStatement :=
  assembleStatement witnessedSnap #[
    { requirementId := "req.done", citedAs := "holds"
      fact := .resolved "Demo.holds" "theorem" true "Demo.holds : True" #["propext", "Quot.sound"] }
  ]

def sorryStmt : VerificationStatement :=
  assembleStatement witnessedSnap #[
    { requirementId := "req.done", citedAs := "holds"
      fact := .resolved "Demo.holds" "theorem" true "Demo.holds : True"
        #["propext", "sorryAx"] }
  ]

def missingStmt : VerificationStatement :=
  assembleStatement witnessedSnap #[
    { requirementId := "req.done", citedAs := "holds", fact := .missing }
  ]

def ambiguousStmt : VerificationStatement :=
  assembleStatement witnessedSnap #[
    { requirementId := "req.done", citedAs := "holds"
      fact := .ambiguous #["Other.holds", "Demo.holds"] }
  ]

def defnStmt : VerificationStatement :=
  assembleStatement witnessedSnap #[
    { requirementId := "req.done", citedAs := "holds"
      fact := .resolved "Demo.holds" "definition" false "Demo.holds : True" #["propext"] }
  ]

def tamperedExtra (source : String) : String :=
  source.replace "extra-axioms\nend" "extra-axioms\nnot.an.axiom\nend"

def checks : Array (String × Bool) := #[
  ("empty snapshot is an empty mark",
    let s := assembleStatement SpecSnapshot.empty #[]
    s.proved.isEmpty && s.openObligations.isEmpty && s.axioms.isEmpty &&
      s.checkable && s.citationsOk && s.disjoint && s.certifies (emitVerificationStatement s)),
  ("deferred scenario stays outside the mark",
    deferredStmt.proved.isEmpty &&
      deferredStmt.hasOpen "req.later" .deferred "not yet" &&
      deferredStmt.citationsOk && deferredStmt.checkable &&
      (emitVerificationStatement deferredStmt).contains "say \\\"later\\\""),
  ("a kernel theorem covers the requirement and leaves the deferred scenario open",
    witnessedStmt.covers "req.done" "Demo.holds" &&
      witnessedStmt.citationsOk &&
      !witnessedStmt.hasOpen "req.done" .unwitnessedExecutable "runs" &&
      witnessedStmt.hasOpen "req.done" .deferred "later" &&
      witnessedStmt.axioms == #["Quot.sound", "propext"] &&
      witnessedStmt.extraAxioms.isEmpty &&
      witnessedStmt.disjoint && witnessedStmt.checkable),
  ("sorryAx is an open obligation, not a covered proof",
    sorryStmt.proved.isEmpty &&
      sorryStmt.hasOpen "req.done" .dependsOnSorry "Demo.holds" &&
      !sorryStmt.citationsOk &&
      sorryStmt.axioms.isEmpty &&
      sorryStmt.checkable),
  ("an unresolved citation is open and fails citationsOk",
    missingStmt.hasOpen "req.done" .unresolvedTheorem "holds" &&
      missingStmt.hasOpen "req.done" .unwitnessedExecutable "runs" &&
      !missingStmt.citationsOk && missingStmt.checkable),
  ("ambiguous citations stay outside the mark",
    ambiguousStmt.hasOpen "req.done" .ambiguousTheorem "holds" &&
      (ambiguousStmt.openObligations.any fun o => o.detail == "Demo.holds, Other.holds") &&
      !ambiguousStmt.citationsOk),
  ("a definition is not a kernel theorem",
    defnStmt.hasOpen "req.done" .notATheorem "Demo.holds" &&
      defnStmt.proved.isEmpty && !defnStmt.citationsOk),
  ("a lying extra-axioms section is rejected",
    match parseVerificationStatement (tamperedExtra (emitVerificationStatement witnessedStmt)) with
    | .error "extra-axioms section does not match the proved rows" => true
    | _ => false),
  ("the theme mark covers toggleDarkCheck_of_light and round-trips",
    themeVerified.checkable && themeVerified.certifies themeVerifiedSource &&
      themeVerified.citationsOk && themeVerified.disjoint &&
      themeVerified.openObligations.isEmpty &&
      themeVerified.coversSuffix "theme.selection" "toggleDarkCheck_of_light" &&
      !(themeVerified.axioms.any (· == "sorryAx")) &&
      !themeVerified.axioms.isEmpty &&
      themeVerified.extraAxioms.isEmpty &&
      themeVerifiedSource.contains "mark lean-spec-verified"),
  ("the statement names its toolchain and spec digest",
    witnessedStmt.toolchain == Lean.versionString &&
      witnessedStmt.specDigest == specDigestOf witnessedSnap &&
      witnessedStmt.specDigest.startsWith "fnv1a64:" &&
      witnessedStmt.specDigest.length == 24 &&
      (emitVerificationStatement witnessedStmt).contains s!"spec-digest {witnessedStmt.specDigest}"),
  ("a different spec gives a different digest",
    specDigestOf witnessedSnap != specDigestOf deferredOnly),
  ("a statement claiming another spec does not certify",
    let forged := (emitVerificationStatement witnessedStmt).replace
      witnessedStmt.specDigest (specDigestOf deferredOnly)
    !witnessedStmt.certifies forged),
  ("fnv1a64 matches the reference vectors",
    hex64 (fnv1a64 "") == "cbf29ce484222325" && hex64 (fnv1a64 "a") == "af63dc4c8601ec8c"),
  ("the archived mark keeps deferred contrast and persistence outside",
    archivedVerified.checkable && archivedVerified.citationsOk &&
      archivedVerified.coversSuffix "theme.selection" "toggleDarkCheck_of_light" &&
      archivedVerified.hasOpen "theme.contrast" .deferred "contrast stated" &&
      archivedVerified.hasOpen "theme.selection" .deferred "persist across restart" &&
      !archivedVerified.hasOpen "theme.selection" .unwitnessedExecutable "toggle dark" &&
      archivedVerifiedSource.contains "no pixel checker yet")
]

end LeanSpec.Tests.Verification
