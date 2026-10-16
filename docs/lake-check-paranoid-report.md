# `lake check --paranoid` report

Lean 4.35.0 (2026-10-15) ships `lake check`. It exports a development and replays it
through Lean's kernel, rejecting any non-standard axiom. With `--paranoid` it also runs
every external checker bundled with Lean: a hardened-allocator build of Lean's own
kernel (`leanchecker-paranoid`), lean4lean, nanoda, and the verified kernels
con-leche (proven consistent in Lean) and con-ron (a Rust refinement of con-leche).
Background: [Lean now ships with verified kernels](https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/).

This report covers the runs on lean-spec on 2026-10-16: what the checkers found, why,
and what we changed.

## Result

| Checker | Before (1.0.0 + sugar fix) | After (`refactor/kernel-decide`) |
|---|---|---|
| Lean default kernel | accepts | accepts |
| Lean paranoid kernel | accepts | accepts |
| lean4lean | accepts | accepts |
| nanoda | **rejects** (crash) | accepts |
| con-leche | **rejects** | accepts |
| con-ron | **rejects** | accepts |
| Axiom policy | **fails**: 288 non-standard axioms | passes |

"After" covers all 68 modules (library, demos and tests; 93,001 declarations), and
`lake check` exits 0. No checker ever rejected a proof on its merits. Every failure
had one cause, explained below.

## Finding 1 — `native_decide` axioms (all three rejections)

**What was reported.** Lean's kernel accepted everything, but the axiom check listed
288 axioms of the form `…._native.native_decide.ax_N`. The external checkers reacted
as follows:

- **con-leche:** `not implemented yet: non-standard axiom (…native_decide.ax_1)`.
- **con-ron:** `declined: non-standard axiom (…) (--verified)`.
- **nanoda:** panicked with `declaration not found in infer_const, …native_decide.ax_1`
  and exited with 101.

**Explanation.** This is valid and expected. `native_decide` proves a goal by running
compiled code, and since Lean 4.35 each use is recorded as its own axiom that trusts
the compiler. The external kernels deliberately do not trust the compiler, so they
refuse a development that contains such an axiom. That includes the verified kernels,
whose whole point is a smaller trusted base. nanoda's panic is a crash, not a clean
rejection, but it fails for the same reason.

**Where the axioms came from.** 1.0.0 used `by native_decide` about 460 times. Almost
all of those uses built concrete values: "this string literal is non-blank", "these
ids are unique", "this catalog's skill graph is acyclic". A few named theorems
depended on it too:

- `parse_emit_empty_isOk`
- `TempConverter.roundTripCheck_holds` and `referencePointsCheck_holds`. The second
  was documented as "kernel-checked", which was not true.
- the redaction lemmas `redactedLearning_clean` and `specRedacted_clean`.

The generic guarantees (the validation round-trips and the store laws) never used
`native_decide`.

**Why `native_decide` was used.** Plain `decide` could not evaluate these predicates.
The kernel cannot reduce `String.any` and `splitOn`, which are built on UTF-8 byte
arrays and get stuck on `Classical.choice`. It also cannot reliably reduce
`Array.all`, `any` and `map`, which use a well-founded loop.

**Fix.** Every predicate behind those proofs is now written over `List`, which the
kernel reduces, and every proof is `by decide +kernel`. That adds no axiom.

- `nonemptyText`, `ValidRequirementId` (new `LeanUtil.splitChars`), process-skill ids,
  secret detection (new `LeanUtil.hasInfix`), `coherentVia`, `RoleInBoot` and the
  catalog invariants were rewritten. The acyclicity check is the same fuelled Kahn
  reduction, now run on lists.
- `LeanSpec/Tests/KernelPredicates.lean` checks each rewritten predicate against the
  formula it replaced, on edge cases. This is a sample check, not a proof of
  equivalence.
- `parse_emit_empty_isOk` became a `#guard`. The kernel cannot evaluate the
  emit/parse string pipeline, and a theorem about one concrete value is not worth an
  axiom that makes external kernels refuse the whole project.

## Finding 2 — hidden definitions under the module system (found while fixing)

**What happened.** After the rewrite, `decide +kernel` still got stuck in some
modules, for example on `TargetLang.allowedFor`, on skill values, and on the `BEq`
instances.

**Explanation.** This is valid. Under Lean's module system, another module sees a
`public def` only as a typed constant unless the definition is `@[expose]`, and that
applies to the kernel as well as the elaborator. A proof in module B cannot unfold a
predicate defined in module A unless A exposes it.

**Fix.** The predicates, the values they unfold and the defs that `spec` and `skill`
generate are `@[expose]`.

## Finding 3 — tooling limitations (not about lean-spec's proofs)

These shaped how the check was run. None of them is a defect in lean-spec's proofs.

1. **The sandbox needs Linux.** `lake check` sandboxes the project with `bwrap`, which
   needs Linux namespaces. On macOS it stops with exit 2. These runs used
   `--inadvisably-no-sandbox` on our own code. The sandbox protects the checker from an
   untrusted project, so this does not change what the checkers decided about the
   proofs. It does mean the runs are not the official, sandboxed configuration. To be
   done: repeat in a Linux container before quoting the result externally.
2. **Two executables both define `main`.** Without `--from-export`, `lake check`
   imports every default target into one environment and fails with
   `environment already contains 'main'`. That happens because `lean-spec` and
   `lean-spec-verification` each have a `main`. This is a limitation of `lake check`,
   not an error. We exported instead: one throwaway module importing every library
   module except the three `main` roots, exported with `leanexport`, and checked with
   `lake check --from-export=<file> --paranoid`.
3. **`leanexport` with several module arguments panics** (`Option.get!`, `value is
   none`). It works with a single root module, so we used one umbrella module. This
   may be worth reporting upstream.
4. **Stale `.olean` files.** The build directory still held `.olean` files for modules
   that were removed long ago (`LeanSpec.Agent.*`, `Cli`, `Render`). They do not affect
   the build, but anything that lists modules from `.lake/build` picks them up, so list
   modules from the source tree.

## Reproduce

On Linux, drop `--inadvisably-no-sandbox`:

```sh
lake build && lake build lean-spec-tests
# One umbrella module importing every library module except the three `main` roots.
(find LeanSpec -name '*.lean'; echo LeanSpec.lean; echo LeanUtil.lean; echo LeanJson.lean) \
  | sed 's/\.lean$//; s#/#.#g' | sort -u \
  | grep -vxE 'LeanSpec\.Query|LeanSpec\.Demo\.PrintVerification|LeanSpec\.Tests' \
  | sed 's/^/import /' > LeanSpecAll.lean
lake env lean LeanSpecAll.lean -o .lake/build/lib/lean/LeanSpecAll.olean
lake env leanexport LeanSpecAll > lean-spec.ndjson
rm LeanSpecAll.lean .lake/build/lib/lean/LeanSpecAll.*
lake check --from-export=lean-spec.ndjson --paranoid
```

The export is about 450 MB, most of it Lean core. The full paranoid run took about
9 minutes on an Apple M2 Pro.

## Keeping it this way

A single `native_decide` anywhere makes three of the six checkers refuse the whole
development again. When you add a decidable predicate, write it over `List`, mark it
`@[expose]` if other modules' proofs unfold it, and prove literals with
`by decide +kernel`. The README's notes say the same.
