# Proved construction: a Clean-only adoption example

A memory read and a Boolean choice now consume the data-aware witness and physical row/table
construction proofs in Clean alone. A caller supplies semantic inputs, fixed prover data, and
each row's hint; the generic construction returns rows whose actual circuit checks are proved.

The baseline is Clean `fba2a29f5e36420d797c1de118ac9f11f23b819e`, Lean `v4.33.1`, with the
unchanged dependency manifest. The three construction modules were ported from
dtumad/sp1-lean `27148217a89510bddd26eb27c0b44657cb4e0441`. Those source modules are identical
at fork main `c286859028977f34a9b1485748203d5028a30bac`; other fork and presentation changes
are not dependencies of this example. Talk reference: `03cdb3f5ee1b4b1006b9969c50f13cc55a09ee94`.

## Follow one checked connection

Start at [`memory_row_valid`](../Clean/Examples/Construction.lean), in namespace
`Examples.Construction`. Its literal statement is:

```lean
theorem memory_row_valid (address : Fp) (data : ProverData Fp) (hint : ProverHint Fp)
    (h_address : ValidAddress address data) :
    let env := Environment.fromArray (memoryComponent.buildRow address data hint) data
    memoryComponent.operations.ConstraintsHold env ∧ memoryComponent.Spec env
```

The definitions determining its meaning are small:

- `Fp` is `ZMod 97`, with primality proved by kernel computation. Its field and equality
  instances are the standard ones. The example has no additional instance premises.
- `memoryTable` selects the `"memory"` data key with two columns: address and value.
  Membership requires an in-bounds index and matching stored address and value.
- `ValidAddress` requires an in-bounds address and agreement between that address and the
  selected record's address column. This is the only semantic construction premise.
- `ReadSpec` says that the requested index exists and the output is its stored value.
- `memoryReader` witnesses the value through `dataGet`, then checks the actual lookup.
  Its witness index is u64; the example proves that every `ZMod 97` address fits exactly.
- `memoryComponent` packages that formal circuit. `buildRow` retains the input cell and appends
  the generated value. Constraints and the semantic result use the same fixed `data`.

The proof applies `Component.buildRow_constraintsHold` and `buildRow_spec_requirements`.
`memory_computable` discharges their computability premise; `h_address` discharges prover
assumptions; the circuit's semantic assumptions are `True`. The generic chain relies on
Clean's existing circuit completeness/soundness and the data-aware array/list interpreter
agreement and honesty theorems. No validity premise is supplied for the generated row.

`memory_table_valid` then consumes `Table.build_constraints`. The concrete
`TestConstruction.memory_fixture_valid` discharges the address premises for reads at indices
0 and 2 in `[(0, 11), (1, 42), (2, 96)]`. Its conclusion is the actual built table's `Constraints`.

## Hints and the accepted relation

`booleanChoice` reads the `"choice"` hint key through the witness IR and invokes Clean's bundled
Boolean assertion. Its semantic specification is `IsBool output`. Its prover assumptions
require a Boolean hint, and its prover specification identifies the generated value with that
hint. These are different guarantees: an alternative Boolean witness remains valid even when
it differs from the generator's choice.

`boolean_table_valid` consumes `Table.buildHinted_constraints`, with each input carrying its
own hint and all rows sharing the same data. `TestConstruction.mixed_fixture_valid` discharges
the premises for hints 0, 1, 0 and proves the resulting physical table valid. The empty case
also has a theorem. All fixtures and counterexamples use kernel proofs; execution results
are additional checks, not proof assumptions.

The public generic interfaces retain their field polymorphism and names. New layout
normalization rules use Clean's `circuit_norm` set rather than extending the global simp set.
The examples have no channel interactions. The retained `Table.buildHinted_interactions`
theorem characterizes the physical interaction list; this pilot makes no assembled-balance
or whole-machine completeness claim.

## Regressions and reproduction

[`TestConstruction`](../Clean/Utils/Test/TestConstruction.lean) proves that its executable
checkers are equivalent to row width plus the components' raw `ConstraintsHold`. Its 26 cases
exercise:

| Obligation | Cases |
|---|---|
| Actual indexed lookup | First/last addresses; corrupted value; invalid address; empty memory; wrong stored address |
| Data dependency | Regenerated row accepts changed data; old row rejects; input cells agree while witnesses differ |
| Construction | Read table, empty table, input layout, array/list agreement on first/last reads |
| Row-local hints | Individual 0/1 hints, one mixed-hint table, non-Boolean hint/output rejection |
| Accepted witness freedom | A valid alternative Boolean value accepts |
| Physical layout | Short and long rows reject for both components |

`data_needs_agreement` and `hint_needs_agreement` give separate kernel-checked counterexamples:
identical cell functions do not imply identical witness evaluation when data or hints differ.
Both components pass Clean's witness exportability check. No backend lowering is added.

From the checkout root:

```sh
npm install --prefix .lake/test-tools snarkjs@0.7.6 wabt@1.0.39
bash scripts/check-construction-pilot.sh
```

The runner builds `Clean` and the new regression module with warnings treated as errors. It
also builds all of `CleanTests`; the pinned upstream `TestCircuitProofStart` contains ten
deliberately unfinished tactic smoke tests, so this target allows only their exact existing
`sorry` diagnostics and verifies that file is unchanged. The pilot's 20 audited statements
depend only on `propext`, `Classical.choice`, and `Quot.sound`. The runner requires the
backend test tools, rejects skipped backend tests, runs all construction cases, prints literal
types/definitions and axiom reports, checks the production import closure, and runs Clean's
whitespace gate. Exceptions and unexpected case outcomes fail the command. Reports are written
under `.lake/build/construction-pilot`, including revisions, dependency pins, exact commands,
exit codes, and actual outputs. The runner reports cache reuse; it does not imply a cold build.
Release-cache downloads are disabled during validation; dependency artifacts already present
may still be reused. The example/report scripts can also be run individually with `lake env lean`
after the build.

## Alignment with pending Clean work

The pilot keeps the named baseline. The following heads were inspected separately; none is
silently combined into its dependency graph.

| Pending work | Head | Migration |
|---|---|---|
| [#450](https://github.com/Verified-zkEVM/clean/pull/450) | `8301b77a` | Strengthened agreement can replace the additive agreement predicate and corresponding computability adapters once the consumers agree on its API. Data-aware interpretation and table construction still need their own connection. |
| [#426](https://github.com/Verified-zkEVM/clean/pull/426) | `da62df69` | Reuse bundled computability evidence instead of retaining a parallel long-term predicate family. |
| [#448](https://github.com/Verified-zkEVM/clean/pull/448) | `7efc1af2` | Reconcile the strengthened predicates with the compositional laws on its #426-based branch. |
| [#446](https://github.com/Verified-zkEVM/clean/pull/446) | `89e9abec` | Connect its private data-aware row interpreter to the proved interpreter; preserve inputs, data, and row hints. |

For #446, the proposed row-level bridge is equality between its `witgenWithData data hint ops
input` and `FlatOperation.witgenWithData data hint ops input`. Their folds use the same witness
evaluation and append operation. Its `PreparedComponent.witgenOps` filters out non-witness
operations; the proof bridge must account for that filtering and the same input-cell layout.

Two further obligations remain visible in that source. `completeRow` always supplies an empty
hint, whereas this example uses different hints per row. `generate` fixes `generatedData` from
initial inputs before generation and padding, while final `EnsembleWitness.data` is derived
from the final physical tables. Applying row validity requires an agreement/transport argument
between those environments, including the data used by lookups and the semantic contract.
Equality of the interpreter folds alone does not discharge either obligation or prove the
scheduler, termination, padding, or full completeness. Public submission is a separate step.

## Speaker paragraph

The construction proofs now have a small consumer in Clean alone. A memory reader generates
its witness from fixed lookup data and proves that the resulting physical row satisfies the
lookup and returns the addressed value. A second component builds one table with different
Boolean hints per row, while preserving the freedom to accept another valid Boolean witness.
The examples expose the data and hint agreement needed by honest generation. They demonstrate
reuse of the existing proofs; they do not certify a demand-driven ensemble scheduler or
cryptographic commitment binding.
