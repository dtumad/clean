# Canonical generator adapter for #446

This branch is based on Clean #446 head `89e9abec`, with its unchanged Lean 4.32.2 and dependency
manifest. It backports the canonical agreement/data-aware generator from the separate Lean 4.33.1
construction branch, then replaces the scheduler's private array fold with a delegation to
`FlatOperation.witgen`. The private witness-operation filter also delegates to the canonical one.

`rowEvaluator_eq` identifies the evaluator at the same data, hint, operations, and input cells.
`filteredRowEvaluator_eq` applies the proved filtering law: dropping assertions, lookups, and
interactions from the witness-generation program preserves generated values. The full component
still owns its checks and ledger. `Circuit.witgen_usesLocalWitnesses` is available at fixed data.

Reproduce:

```sh
lake build --no-cache --wfail Clean Clean.Utils.Test.TestSchedulerGenerator Clean.Examples.FibonacciVm.WitnessGenerationTest
lake env lean scripts/schedulerGeneratorReport.lean
```

The new interpreter regression includes data and hint reads, a nonempty input prefix, assertion,
lookup, and interaction operations, witness-only filtering, and the legacy empty-data default.
The existing Fibonacci scheduler regressions remain unchanged. The report exposes proof axioms;
no new axiom or `native_decide` is used by the adapter or its new theorem.

This is a row-interpreter compatibility result. `completeRow` still supplies empty hints.
`generate` fixes data from initial inputs before padding/demand, while the returned witness derives
data from final tables. Final-data agreement, per-row hint plumbing, scheduler termination,
padding validity, and successful-generation completeness are not proved by this adapter.
Keep this patch on #446's stack; do not re-pin SP1 to Lean 4.32.2 or import its scheduler as part
of the construction migration. Upstream publication requires a separate decision.
