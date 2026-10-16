import LeanSpec.Validated
import LeanSpec.KbAdapter.Wiki

/-!
# Kernel-reducible predicates agree with their `String`-API originals

`nonemptyText`, `ValidRequirementId`, `validProcessSkillId` and secret detection were
rewritten over `List` so the kernel can decide them. Each is compared here, on edge
cases, against the formula it replaced.
-/

namespace LeanSpec.Tests.KernelPredicates

open LeanSpec

def samples : List String :=
  ["", " ", "\t\n", "a", " a ", "page.overview", "page..overview", ".page", "page.",
   "page.over-view_2", "1page", "page.2x", "a.b.c", "ünï", "-skill", "skill-x.y",
   "a/b", "SECRET:", "x SECRET: y", "SECRET", "secret:", "ab SECRET:cd", "SECRET:SECRET:"]

def oldNonempty (s : String) : Bool := s.any fun c => !c.isWhitespace

def oldValidRequirementId (s : String) : Bool :=
  (s.splitOn ".").all fun segment => validRequirementIdSegment segment.toList

def oldValidProcessSkillId (s : String) : Bool :=
  oldNonempty s && !s.startsWith "." && !s.startsWith "-" &&
    s.all fun c => c.isAlphanum || c == '.' || c == '-'

def oldSecret (s : String) : Bool := (s.splitOn "SECRET:").length != 1

def checks : Array (String × Bool) := #[
  ("nonemptyText agrees with String.any",
    samples.all fun s => LeanUtil.nonemptyText s == oldNonempty s),
  ("ValidRequirementId agrees with the splitOn form",
    samples.all fun s => decide (ValidRequirementId s) == oldValidRequirementId s),
  ("validProcessSkillId agrees with the startsWith/all form",
    samples.all fun s => validProcessSkillId s == oldValidProcessSkillId s),
  ("secret detection agrees with the splitOn form",
    samples.all fun s => KbAdapter.containsSecret s == oldSecret s)
]

end LeanSpec.Tests.KernelPredicates
