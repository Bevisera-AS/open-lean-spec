# Agents working in this repository

- A requirement is a Lean declaration: `@[requirement must] def R : Sig → Prop`; for a black-box program `Sig` is `IOSig` and the body is `Req.holds [examples]` or `IOReq pre post`. The docstring is a label, never the claim.
- `lake exe spec help` is the manual; `check`, `test ./run`, `statement` and `report ./run` are the referee. Examples are the tests: write no others.
- Evidence is a `@[satisfies]` theorem (closes a row; about the `@[shipped]` product, else the row is `model`) or an `@[evidence R]` theorem (supports it); add `@[refutes]` counter-models, or the row is `vacuous`. No `sorry` anywhere. Never weaken a requirement to make a proof or a test go through.
- Do not write `@[sign_off]` axioms. Only a person signs off.
- Check with `lake build` and `lake test`; `lake check --paranoid` runs in CI (Linux only). The process is `LeanSpec.Workflow.catalog`: propose, review, apply, archive, reflect.
