import LeanSpec.Finding

/-! Audit findings: one typed record per defect found in a benchmark run. The
reviewer appends to the lists; `lake env lean bench/Findings.lean` checks them.
`Finding` and its kinds are `LeanSpec.Finding`; every entry converts to a
`Reflection` with its run as provenance. -/

open LeanSpec

namespace Bench

/-- Pilot 2026-10-23: ratelimit × {py, cpp, lean} × {md, lean}, seed 1. All six
programs pass 30/30 hidden cases and 400/400 differential fuzz cases. -/
def findings : List Finding := [
  ⟨"ratelimit-cpp-md-haiku-s1", "-", .specDrift, 1, "SPEC.md:49 (R11-R13), test.sh R11a-c R13e-f",
   "invented input-validation requirements (exit 1 on limit<0, window 0, fractional t, bad overrides); task never asked"⟩,
  ⟨"ratelimit-cpp-md-haiku-s1", "-", .flaw, 1, "test.sh:9",
   "tests compare stdout with all whitespace stripped and keys in fixed order: spaces inside strings are lost, reordered keys fail"⟩,
  ⟨"ratelimit-lean-md-haiku-s1", "-", .specDrift, 1, "test.sh R13_* (5 tests)",
   "invented input validation: rejects unsorted events, limit<0, window 0, bad overrides; task never asked"⟩,
  ⟨"ratelimit-lean-lean-haiku-s1", "R1", .flaw, 1, "Prog.lean:20 inWindow",
   "per-user history never pruned; every event rescans all earlier allowed times (quadratic per user)"⟩,
  ⟨"ratelimit-lean-lean-haiku-s1", "-", .testGap, 1, "Prog.lean",
   "Lean target with backbone arm: no theorem or @[req] evidence; brief did not ask for proofs"⟩,
  ⟨"ratelimit-lean-md-haiku-s1", "R4", .testGap, 1, "Prog.lean:54-71",
   "3 theorems (nil, limit 0) proved unasked but not linked to requirements; md arm has no evidence mechanism"⟩]

/-- Round 2 2026-10-23: 4 tasks × {py, cpp, lean} × {md, lean} × seeds 11, 12; brief asks every run to
show each requirement correct by tests or (Lean target) proofs; change requests self-paced via ./next.
All 48 programs pass every hidden case and 300 fuzz cases. -/
def round2 : List Finding := [
  ⟨"csvclean-cpp-md-haiku-s12", "-", .flaw, 2, "test.sh", "tests compare raw JSON text, not values: a correct program with other spacing fails"⟩,
  ⟨"lru-cpp-md-haiku-s11", "-", .flaw, 2, "test.sh", "tests compare raw JSON text, not values: a correct program with other spacing fails"⟩,
  ⟨"lru-cpp-md-haiku-s12", "-", .flaw, 2, "test.sh", "tests compare raw JSON text, not values: a correct program with other spacing fails"⟩,
  ⟨"ratelimit-cpp-md-haiku-s12", "-", .flaw, 2, "test.sh", "tests compare raw JSON text, not values: a correct program with other spacing fails"⟩,
  ⟨"mortgage-cpp-md-haiku-s12", "-", .flaw, 2, "test.sh", "tests compare raw JSON text, not values: a correct program with other spacing fails"⟩,
  ⟨"lru-lean-md-haiku-s11", "-", .specDrift, 1, "spec + tests", "invented error behaviour for inputs the task never defines; reference accepts them"⟩,
  ⟨"lru-lean-md-haiku-s12", "-", .specDrift, 1, "spec + tests", "invented error behaviour for inputs the task never defines; reference accepts them"⟩,
  ⟨"ratelimit-lean-md-haiku-s11", "-", .specDrift, 1, "spec + tests", "invented error behaviour for inputs the task never defines; reference accepts them"⟩,
  ⟨"ratelimit-lean-md-haiku-s12", "-", .specDrift, 1, "spec + tests", "invented error behaviour for inputs the task never defines; reference accepts them"⟩,
  ⟨"mortgage-lean-md-haiku-s11", "-", .specDrift, 1, "spec + tests", "invented error behaviour for inputs the task never defines; reference accepts them"⟩,
  ⟨"mortgage-py-md-haiku-s11", "-", .specDrift, 1, "spec + tests", "invented error behaviour for inputs the task never defines; reference accepts them"⟩,
  ⟨"mortgage-cpp-md-haiku-s11", "-", .specDrift, 1, "spec + tests", "invented error behaviour for inputs the task never defines; reference accepts them"⟩,
  ⟨"mortgage-lean-lean-haiku-s12", "-", .specDrift, 1, "spec + tests", "invented error behaviour for inputs the task never defines; reference accepts them"⟩,
  ⟨"csvclean-cpp-md-haiku-s11", "R1", .specDrift, 1, "test.sh", "tests pin CSV corners the task leaves open (text after closing quote, unclosed quote); task ambiguity, not a misreading"⟩,
  ⟨"csvclean-lean-md-haiku-s11", "R1", .specDrift, 1, "test.sh", "tests pin CSV corners the task leaves open (text after closing quote, unclosed quote); task ambiguity, not a misreading"⟩,
  ⟨"csvclean-lean-md-haiku-s12", "R1", .specDrift, 1, "test.sh", "tests pin CSV corners the task leaves open (text after closing quote, unclosed quote); task ambiguity, not a misreading"⟩,
  ⟨"csvclean-py-md-haiku-s11", "R1", .specDrift, 1, "test.sh", "tests pin CSV corners the task leaves open (text after closing quote, unclosed quote); task ambiguity, not a misreading"⟩,
  ⟨"csvclean-py-md-haiku-s12", "R1", .specDrift, 1, "test.sh", "tests pin CSV corners the task leaves open (text after closing quote, unclosed quote); task ambiguity, not a misreading"⟩,
  ⟨"round2-lean-target", "-", .testGap, 1, "Prog.lean @[req] theorems", "34 linked theorems in 8 Lean-arm runs, but nearly all are rfl on concrete inputs or restate a definition; few general properties"⟩,
  ⟨"mortgage-cpp-lean-haiku-s11", "-", .flaw, 1, "Spec.lean", "large json% literal needed set_option maxRecDepth 100000 - backbone friction"⟩]

#guard round2.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.note ≠ "")

/-- Round 3 2026-10-23: backbone gains big-json% literals and general-vs-example proof evidence;
brief asks for ∀-theorems; CSV task text fixed. 36 new runs + 12 reused md runs. All 48 correct. -/
def round3 : List Finding := [
  ⟨"csvclean-cpp-md-haiku-s21", "-", .flaw, 2, "test.sh", "tests compare raw JSON text, not values: a correct program with other spacing fails"⟩,
  ⟨"ratelimit-lean-md-haiku-s21", "-", .flaw, 2, "test.sh", "tests compare raw JSON text, not values: a correct program with other spacing fails"⟩,
  ⟨"mortgage-lean-md-haiku-s21", "-", .specDrift, 1, "test.sh", "invented error behaviour for inputs the task never defines"⟩,
  ⟨"mortgage-lean-md-haiku-s22", "-", .specDrift, 1, "SPEC.md R9", "invented error behaviour for inputs the task never defines"⟩,
  ⟨"lru-lean-md-haiku-s21", "-", .specDrift, 1, "test.sh T25-T26", "invented error behaviour for inputs the task never defines"⟩,
  ⟨"lru-lean-md-haiku-s22", "-", .specDrift, 1, "test.sh T-err-*", "invented error behaviour for inputs the task never defines"⟩,
  ⟨"ratelimit-lean-md-haiku-s22", "-", .specDrift, 1, "test.sh r8_*", "invented error behaviour for inputs the task never defines"⟩,
  ⟨"csvclean-cpp-md-haiku-s22", "R5", .specDrift, 1, "test.sh R17", "dedupe_on naming an absent column: task silent, reference dedupes; task ambiguity"⟩,
  ⟨"csvclean-lean-md-haiku-s21", "R5", .specDrift, 1, "test.sh R14", "dedupe_on naming an absent column: task silent, reference dedupes; task ambiguity"⟩,
  ⟨"csvclean-py-md-haiku-s21", "R5", .specDrift, 1, "test.sh R17", "dedupe_on naming an absent column: task silent, reference dedupes; task ambiguity"⟩,
  ⟨"lru-lean-lean-haiku-s21", "-", .flaw, 1, "transcript", "read backbone Evidence.lean to learn @[req]: spec help lacks an @[req] example"⟩,
  ⟨"bench-csvclean-ref", "R2", .bug, 2, "bench/tasks/csvclean/ref.py", "reference split on lone CR and trimmed tabs, against the task text; fixed, hidden outputs unchanged, drift rescored"⟩]

#guard round3.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.note ≠ "")

/-- Round 4 2026-10-24: Sonnet, 24 runs (4 tasks × py/cpp/lean × md/Lean × seed 31); spec help gains an
@[req] example; check rejects unknown ids; CSV corners defined. All 24 correct. -/
def round4 : List Finding := [
  ⟨"lru-cpp-md-sonnet-s31", "-", .flaw, 2, "test.sh T17", "tests compare raw JSON text: expects literal é, program prints \\u00e9 (same value)"⟩,
  ⟨"ratelimit-lean-md-sonnet-s31", "-", .flaw, 2, "test.sh", "tests compare raw JSON text, not values: a correct program with other spacing fails"⟩,
  ⟨"mortgage-cpp-md-sonnet-s31", "-", .specDrift, 1, "test.sh err_*", "invented error behaviour for inputs the task never defines"⟩,
  ⟨"mortgage-lean-md-sonnet-s31", "-", .specDrift, 1, "test.sh", "invented error behaviour (negative interest_only_months)"⟩,
  ⟨"csvclean-lean-md-sonnet-s31", "R5", .specDrift, 1, "test.sh T28", "empty dedupe_on read literally as all rows equal; reference treats [] as absent; task ambiguity"⟩,
  ⟨"csvclean-py-lean-sonnet-s31", "R5", .specDrift, 1, "Spec.lean R8", "empty dedupe_on read literally as all rows equal; reference treats [] as absent; task ambiguity"⟩,
  ⟨"round4-sonnet", "-", .flaw, 1, "transcripts", "4 runs wrote scratch files to /tmp outside the workspace; none read benchmark references"⟩,
  ⟨"backbone-check", "-", .bug, 2, "LeanSpec/Core/Cli.lean", "check accepted @[req] ids absent from the spec; found by the Sonnet reviewer, now a problem (ok:false)"⟩]

#guard round4.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.note ≠ "")

/-- Round 4b 2026-10-26: one seed on the lean-spec 3 surface (`@[requirement]` + `Req.holds`,
`@[example]`, `@[evidence R]` by name; `Prog` imports `Spec`). lru, Lean target, Sonnet, seed 32,
driven by `claude -p`. Correct on every measure (30/30 hidden, no drift, 3/3 mutants, 8 theorems all
general, check ok). 14.2k output tokens against 9.7k for seed 31, which an in-session subagent drove,
so not comparable; round 5 measures it. The agent read `help` and no library source. -/
def round4b : List Finding := [
  ⟨"lru-lean-lean-sonnet-s32", "-", .flaw, 1, "transcript: 4 `Unknown constant` errors",
   "@[evidence R] names a requirement Prog.lean used before Spec.lean defined it; the name gate worked, at the cost of a build per ordering slip"⟩,
  ⟨"lru-lean-lean-sonnet-s32", "-", .flaw, 2, "transcript: sleep 100, pkill -f lean, timeout 100 lake build",
   "Prog imports Spec, so each spec edit rebuilds the program; the cr2 stage took 315 s mostly waiting on lake, and the agent killed lean processes machine-wide to recover"⟩,
  ⟨"lru-lean-lean-sonnet-s32", "-", .flaw, 1, "transcript: ambiguous `get`/`put`",
   "the agent's own `get`/`put` clashed with Lean's `MonadState.get`; renamed to cget/cput with sed; not a surface issue"⟩]

#guard round4b.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.note ≠ "")

/-- Round 5 (seeds 41, 42; Haiku and Sonnet; Python; arms md with a value
comparator, core, logic; each with and without the propose gate). 96 runs, every
one correct on the hidden cases. Four runs drift, all on csvclean. -/
def round5 : List Finding := [
  ⟨"csvclean-py-md-haiku-s41", "R5", .specDrift, 1, "test.sh R22_dedupe_empty_list", "`dedupe_on: []` read as every row equal to every earlier row; the reference reads it as no dedupe; the task text defines neither"⟩,
  ⟨"csvclean-py-md-haiku-s42", "R5", .specDrift, 1, "test.sh R21_dedupe_empty_list", "`dedupe_on: []` read as match-all, as in s41; the task text defines neither reading"⟩,
  ⟨"csvclean-py-md-haiku-s42", "R4", .specDrift, 2, "test.sh R18_dup_header_converts", "invented a rule for duplicate header names with types (the later value wins); the task never defines duplicate headers"⟩,
  ⟨"csvclean-py-logicg-haiku-s41", "R5", .specDrift, 1, "Spec.lean dedupeRows/dedupe-empty-list", "`dedupe_on: []` read as match-all; the reviewer accepted it; the task text defines neither reading"⟩,
  ⟨"csvclean-py-logicg-haiku-s42", "R5", .specDrift, 1, "Spec.lean dedupeOn/dedupe-empty-list", "`dedupe_on: []` read as match-all; the reviewer accepted it; the task text defines neither reading"⟩,
  ⟨"csvclean-task", "R5", .flaw, 2, "bench/tasks/csvclean/task.json cr2", "the task leaves `dedupe_on: []` undefined and the reference treats it as absent; three of four round-5 drifts are this case, so the text now says so"⟩
]
#guard round5.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.note ≠ "")

/-- Round 6 pilot 2026-10-27: the Lean target on the lean-agent driver with glm-5.3-flash
and glm-5.2, `core` arm, seed 11, tasks metno, forcing, nasjonale, mortgage. None of the
four runs completed; two never wrote a spec. Haiku and Sonnet completed all 21 of their
Lean-target runs in rounds 1 to 4b with theorems, so this is the first look at the proof
surface on a model that cannot carry it. -/
def round6 : List Finding := [
  ⟨"metno-lean-core-glm53flashla-s11", "-", .flaw, 3, "transcript: 24 builds, 48 `depends on sorryAx` errors, 3 test runs",
   "the program passed every example at base (11) and cr1 (17), but a sorry'd @[evidence] theorem in Prog.lean fails `lake build prog`, so test and ./next were blocked by proofs the rows did not need to close; cr2 was never finished"⟩,
  ⟨"metno-lean-core-glm53flashla-s11", "-", .flaw, 2, "Prog.lean: 19 theorems, 15 tagged @[evidence]",
   "fifteen @[evidence] theorems were attempted for five requirements whose seventeen examples already covered them; every row would have closed `tested` with none"⟩,
  ⟨"mortgage-lean-core-glm52la-s11", "-", .flaw, 3, "transcript: 32 builds, 1 test run (5/5), no ./next",
   "the base program passed its examples once; every later call went to theorems (27 sorryAx, 8 unknown identifier, 6 omega failures) and ./next was never run, so no change request was released; the reviewer scored the unreleased R5 and R6 as unimplemented"⟩,
  ⟨"forcing-lean-core-glm53flashla-s11", "-", .flaw, 2, "transcript: 8 calls, `repair truncated` x8, stop truncated",
   "the driver stopped after eight truncated completions (lean-agent classifies truncation as fatal); the model tried to answer the long task in one reply and wrote no file; not a data point"⟩,
  ⟨"forcing-lean-core-glm53flashla-s11", "-", .flaw, 3, "findings.json",
   "the reviewer returned findings about a Java codebase with a JWT secret for a workspace holding only the template; the fail-closed contract checked the shape of a Finding, not that its evidence location exists in the workspace"⟩,
  ⟨"nasjonale-lean-core-glm52la-s11", "-", .flaw, 2, "transcript: 7 calls, stop truncated",
   "stopped after seven truncated completions before any file was written; not a data point"⟩,
  ⟨"round6-glm-lean", "-", .flaw, 2, "bench/results/results.jsonl",
   "`mortgage-lean-core-glm53flashla-s11` is in results.jsonl twice, with 2 and 3 calls and no spec: a run refused at its first calls was scored and appended twice; the once-per-run-id rule from the step 7a log is still open"⟩
]
#guard round6.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.note ≠ "")

/-- Layering review 2026-10-29: not a bench run; the review of the five packages after the
lean-kb split, against `LeanSpec/Spec/Layering.lean`. `req` names the Layering row. The
first five are open; the rest were fixed the same day and are kept as experience. -/
def layering : List Finding := [
  ⟨"layering-review-2026-10-29", "-", .flaw, 2, "LeanSpec/Spec/Layering.lean statement.mark",
   "every row is model-only, yet the statement issues `lean-spec-verified at evidenced` while no lakefile has moved: a model meets `evidenced`, so a proposal carries a product's mark"⟩,
  ⟨"layering-review-2026-10-29", "-", .flaw, 1, "LeanSpec/Spec/Layering.lean today",
   "the counter-model `today` is written by hand from reading lakefiles and skills; nothing checks it against them, so it can drift silently"⟩,
  ⟨"layering-review-2026-10-29", "tracesDigestedInLean", .flaw, 2, "business-kb Skills/Knowledge/AgentRun.lean:196 isValid",
   "an empty promptDigest is still valid; RunReceipt can no longer produce one, but a stored or hand-built receipt can"⟩,
  ⟨"layering-review-2026-10-29", "provenanceToTrace", .testGap, 2, "LeanSpec/Reflection.lean:100 derivedFrom",
   "a reflection cites run ids and the store checks only that the id is known, not the content digest of the trace"⟩,
  ⟨"layering-review-2026-10-29", "promotionThroughCore", .flaw, 2, "business-kb Skills/Evolution/Records.lean GateResult",
   "the agent plane promotes through its own GateResult, not lean-kb's promote, so the gate attribution and redaction laws do not cover it"⟩,
  ⟨"layering-review-2026-10-29", "reflectNeverPromotes", .flaw, 3, "business-kb Skills/Defs/Process/ReflectDiscipline.lean:19",
   "fixed: the skill told the agent to update a skill directly when the home was clear, which Memory.reflect forbids in code; skill text and code must say the same"⟩,
  ⟨"layering-review-2026-10-29", "tracesDigestedInLean", .flaw, 2, "business-kb Skills/Agents/RunReceipt.lean sha256OfString",
   "fixed: the prompt digest came from shasum or sha256sum and was empty when neither ran; now LeanAgent.Sha256, pinned by the FIPS vectors in JournalTests"⟩,
  ⟨"layering-review-2026-10-29", "-", .flaw, 3, "lean-spec-agent lake-manifest.json",
   "fixed: after the lean-kb split the manifest lacked lean-kb and the package did not build; a package split updates every downstream manifest in the same change"⟩,
  ⟨"layering-review-2026-10-29", "agentRecordsFreely", .flaw, 2, "LeanSpec/Workflow/Reflect.lean antipatterns",
   "fixed: process.reflect called a free discovery log an antipattern, so the reviewer read business-kb's intended bottom rung as a defect; the antipattern is now editing a human artifact from a reflection"⟩
]
#guard layering.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.note ≠ "")

#guard findings.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.run ≠ "" ∧ f.note ≠ "")

-- Every finding of every round is well-formed and becomes a reflection.
#guard (findings ++ round2 ++ round3 ++ round4 ++ round4b ++ round5 ++ round6 ++ layering).all fun f => f.wellFormed && f.converts

end Bench
