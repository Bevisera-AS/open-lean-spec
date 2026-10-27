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

#guard findings.all (fun f => 1 ≤ f.severity ∧ f.severity ≤ 3 ∧ f.run ≠ "" ∧ f.note ≠ "")

-- Every finding of every round is well-formed and becomes a reflection.
#guard (findings ++ round2 ++ round3 ++ round4 ++ round4b ++ round5).all fun f => f.wellFormed && f.converts

end Bench
