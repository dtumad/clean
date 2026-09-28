import Clean.Circuit.Theorems

/-!
# Array-backed witness generation (witgen IR plan, phase 3)

`FlatOperation.dynamicWitnesses` is the semantic reference for witness generation, but
it is accidentally quadratic: the accumulator is a `List` (O(n) append per operation),
and the prover environment it builds is list-backed, so every `env.get` inside a
witness callback walks the list from the head (O(i) per read).

`FlatOperation.witgen` below is the runtime counterpart: a single linear fold over the
operations with an `Array` accumulator (amortized O(1) append, in-place when the array
is used linearly) and an array-backed environment (O(1) reads).

The theorem `witgen_eq_dynamicWitnesses` proves once, by induction, that it computes
exactly the same witnesses. Downstream corollaries transfer the existing
`UsesLocalWitnesses` result, so `Circuit.witgen` is a drop-in fast path for honest
witness generation — and the reference interpreter that the future Rust witgen
pipeline is differentially tested against.

Both interpreters keep the supplied prover data and hint fixed throughout generation.
Empty data remains the default for existing callers. Honesty requires the canonical
`ComputableWitnesses` predicate, whose environment agreement preserves data and hints.
The data-aware proof extension was first exercised in dtumad/sp1-lean and its Clean pilot.
-/

variable {F : Type} [FiniteField F] {α : Type}

/-- Build a `ProverEnvironment` from a witness array (O(1) reads) and a prover hint.
Array-backed counterpart of `ProverEnvironment.fromList`. -/
def ProverEnvironment.fromArray (witnesses : Array F) (hint : ProverHint F)
    (data : ProverData F := fun _ _ => #[]) : ProverEnvironment F where
  get i := witnesses[i]?.getD 0
  data
  hint

theorem ProverEnvironment.fromArray_eq_fromList (witnesses : Array F) (hint : ProverHint F)
    {data : ProverData F} :
    ProverEnvironment.fromArray witnesses hint (data:=data) = .fromList witnesses.toList hint (data:=data) := by
  simp only [ProverEnvironment.fromArray, ProverEnvironment.fromList, Array.getElem?_toList]

namespace FlatOperation

/-- One step of array-backed witness generation: a witness operation appends its
values, computed against the environment of all witnesses so far; other operations
leave the array unchanged. -/
def witgenStep (hint : ProverHint F) (acc : Array F) (op : FlatOperation F)
    (data : ProverData F := fun _ _ => #[]) : Array F := match op with
  | .witness _ code => acc ++ (code.eval (.fromArray acc hint (data:=data))).toArray
  | .assert _ | .lookup _ | .interact _ => acc

/--
Array-backed witness generation: a single linear fold over the operations.
Computes the same witnesses as `dynamicWitnesses` (theorem
`witgen_eq_dynamicWitnesses`), without the quadratic list overhead.
-/
def witgen (hint : ProverHint F) (ops : List (FlatOperation F)) (init : Array F)
    (data : ProverData F := fun _ _ => #[]) : Array F :=
  ops.foldl (fun acc op => witgenStep hint acc op (data:=data)) init

lemma witgenStep_toList (hint : ProverHint F) (acc : Array F) (op : FlatOperation F) {data : ProverData F} :
    (witgenStep hint acc op (data:=data)).toList =
      acc.toList ++ op.dynamicWitness hint acc.toList (data:=data) := by
  cases op <;>
    simp [witgenStep, dynamicWitness, ProverEnvironment.fromArray_eq_fromList, Vector.toList]

/-- The array-backed interpreter agrees with the list-backed reference semantics. -/
theorem witgen_eq_dynamicWitnesses (hint : ProverHint F) (ops : List (FlatOperation F))
    (init : Array F) {data : ProverData F} :
    witgen hint ops init (data:=data) = (dynamicWitnesses ops hint init.toList (data:=data)).toArray := by
  induction ops generalizing init with
  | nil => simp [witgen, dynamicWitnesses]
  | cons op ops ih =>
    rw [witgen, List.foldl_cons, ← witgen, dynamicWitnesses_cons, ih, witgenStep_toList]

/-- Keep the operations that contribute witness cells, in their original order. -/
def witnessOperationsOnly : List (FlatOperation F) → List (FlatOperation F)
  | [] => []
  | .witness n code :: ops => .witness n code :: witnessOperationsOnly ops
  | .assert _ :: ops | .lookup _ :: ops | .interact _ :: ops => witnessOperationsOnly ops

/-- Prepared row interpreters may omit assertions, lookups and interactions while generating
witnesses. Those operations must still be retained by the circuit's checked relation. -/
theorem witgen_witnessOperationsOnly (hint : ProverHint F) (ops : List (FlatOperation F))
    (init : Array F) {data : ProverData F} :
    witgen hint (witnessOperationsOnly ops) init (data:=data) =
      witgen hint ops init (data:=data) := by
  induction ops generalizing init with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp_all [witnessOperationsOnly, witgen, witgenStep]

end FlatOperation

namespace Circuit

/--
Fast witness generation for a circuit: array-backed, single linear pass.

`init` provides the witnesses below the circuit's starting offset (typically the
inputs); the result extends it with all witnesses created by the circuit.
-/
def witgen (circuit : Circuit F α) (hint : ProverHint F) (init : Array F := #[])
    (data : ProverData F := fun _ _ => #[]) : Array F :=
  FlatOperation.witgen hint (circuit.operations init.size).toFlat init (data:=data)

/-- `Circuit.witgen` builds exactly the environment of `Circuit.proverEnvironment`. -/
theorem witgen_proverEnvironment (circuit : Circuit F α) (hint : ProverHint F)
    (init : Array F) {data : ProverData F} :
    ProverEnvironment.fromArray (circuit.witgen hint init (data:=data)) hint (data:=data)
      = circuit.proverEnvironment hint init.toList (data:=data) := by
  rw [proverEnvironment, witgen, ProverEnvironment.fromArray_eq_fromList,
    FlatOperation.witgen_eq_dynamicWitnesses]
  simp

/--
If a circuit has computable witnesses, the environment built from `Circuit.witgen`
uses the circuit's local witnesses — i.e., array-backed witness generation is honest.
-/
theorem witgen_usesLocalWitnesses (circuit : Circuit F α) (hint : ProverHint F)
    (init : Array F) (h_computable : circuit.ComputableWitnesses init.size)
    {data : ProverData F} :
    (ProverEnvironment.fromArray (circuit.witgen hint init (data:=data)) hint (data:=data)).UsesLocalWitnesses
      init.size (circuit.operations init.size) := by
  rw [witgen_proverEnvironment]
  have h := circuit.proverEnvironment_usesLocalWitnesses hint init.toList (data:=data)
  simp only [Array.length_toList] at h
  exact h h_computable

/-- Generation appends exactly the circuit's local witness cells. -/
theorem size_witgen (circuit : Circuit F α) (hint : ProverHint F)
    (init : Array F) {data : ProverData F} :
    (circuit.witgen hint init (data:=data)).size
      = init.size + (circuit.operations init.size).localLength := by
  rw [witgen, FlatOperation.witgen_eq_dynamicWitnesses]
  simp only [List.size_toArray, FlatOperation.dynamicWitnesses_length,
    Array.length_toList, FlatOperation.localLength_toFlat]

/-- Generation preserves every seeded input cell. -/
theorem getElem?_witgen_of_lt (circuit : Circuit F α) (hint : ProverHint F)
    {init : Array F} {i : ℕ} (hi : i < init.size) {data : ProverData F} :
    (circuit.witgen hint init (data:=data))[i]?.getD 0 = init[i] := by
  rw [witgen, FlatOperation.witgen_eq_dynamicWitnesses, List.getElem?_toArray]
  exact FlatOperation.getElem?_dynamicWitnesses_of_lt (by simp_all)

end Circuit
