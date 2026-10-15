import LeanSpec.Elab.Sugar

/-!
# Sugar syntax: fail-closed regression tests

Each rejected `requirement ... where` input is pinned with `#guard_msgs`, so the
human surface syntax stays at least as strict as the JSON wire. These run when the
test executable is built (`lake test`).

A clause missing from a scenario (e.g. no `then_`) is a parse error, which
`#guard_msgs` cannot wrap; the elaborator aborts quietly on such partial syntax
instead of indexing past its end.
-/

namespace LeanSpec.Tests.Sugar

open LeanSpec

/-- error: unknown strength `wont`; expected `must`, `shall` or `should` -/
#guard_msgs in
requirement strengthTypo where
  id "test.strength-typo"
  shall "x"
  strength wont
  scenario "a"
    when "w"
    then_ "t"
    check executable

/-- error: `check deferred` needs a reason string, e.g. `check deferred "no fixture yet"` -/
#guard_msgs in
requirement deferredNoReason where
  id "test.deferred-no-reason"
  shall "x"
  scenario "a"
    when "w"
    then_ "t"
    check deferred

/-- error: unknown check kind `maybe`; expected `executable` or `deferred` -/
#guard_msgs in
requirement unknownCheck where
  id "test.unknown-check"
  shall "x"
  scenario "a"
    when "w"
    then_ "t"
    check maybe

/-- error: `check executable` takes no reason; remove the string or use `check deferred` -/
#guard_msgs in
requirement executableWithReason where
  id "test.executable-with-reason"
  shall "x"
  scenario "a"
    when "w"
    then_ "t"
    check executable "why"

/--
error: duplicate scenario name `a` in requirement `test.duplicate-scenario`; scenario names identify verification obligations and must be unique
-/
#guard_msgs in
requirement duplicateScenario where
  id "test.duplicate-scenario"
  shall "x"
  scenario "a"
    when "w"
    then_ "t"
    check executable
  scenario "a"
    when "w2"
    then_ "t2"
    check executable

-- Each accepted strength word maps to its own value; none is a fallback.
requirement explicitShall where
  id "test.explicit-shall"
  shall "x"
  strength shall
  scenario "a"
    when "w"
    then_ "t"
    check executable

requirement explicitShould where
  id "test.explicit-should"
  shall "x"
  strength should
  scenario "a"
    when "w"
    then_ "t"
    check deferred "no fixture yet"

#guard explicitShall.strength == .shall
#guard explicitShould.strength == .should

end LeanSpec.Tests.Sugar
