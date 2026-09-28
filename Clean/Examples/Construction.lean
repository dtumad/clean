module

public import Clean.Air.TableBuild
public import Clean.Gadgets.Boolean

/-! # Data-aware construction with two concrete consumers

The reader checks an indexed memory lookup. The Boolean component reads a row-local hint,
while its semantic contract permits either Boolean output. Both construct physical rows and
tables using the generic completeness chain, with no SP1 or machine-specific dependency.
-/

@[expose] public section

namespace Examples.Construction

/-- A small field keeps the examples' address interpretation below the witness IR's u64 bound. -/
abbrev Fp := ZMod 97

instance : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- One indexed read-only memory entry. -/
structure Entry (F : Type) where
  address : F
  value : F
deriving ProvableStruct

/-- Lookup membership checks both the address and value against the fixed prover data. -/
def memoryTable : Table Fp Entry where
  name := "memory"
  Contains table entry := ∃ (_ : entry.address.val < table.size),
    entry.address = table[entry.address.val].address ∧
    entry.value = table[entry.address.val].value

/-- A valid read address names an existing entry whose stored address matches its index. -/
def ValidAddress (address : Fp) (data : ProverData Fp) : Prop :=
  ∃ (_ : address.val < (data.getTable memoryTable).size),
    address = (data.getTable memoryTable)[address.val].address

/-- The output is the value stored at the requested memory index. -/
def ReadSpec (address value : Fp) (data : ProverData Fp) : Prop :=
  ∃ (_ : address.val < (data.getTable memoryTable).size),
    value = (data.getTable memoryTable)[address.val].value

/-- Witness a value from fixed data and authenticate it with an actual lookup constraint. -/
def memoryReader : GeneralFormalCircuit Fp field field where
  main address := do
    let value ← witness (memoryTable.dataGet address.val).value
    lookup memoryTable ⟨address, value⟩
    return value
  Spec := ReadSpec
  ProverAssumptions address data _ := ValidAddress address data
  soundness := by
    circuit_proof_start [memoryTable, ReadSpec]
    obtain ⟨h_bound, _, h_value⟩ := h_holds
    exact ⟨h_bound, h_value⟩
  completeness := by
    circuit_proof_start [memoryTable, ValidAddress]
    obtain ⟨h_bound, h_address⟩ := h_assumptions
    refine ⟨h_bound, h_address, ?_⟩
    have h_value : env.get i₀ =
        ((env.data.getTable memoryTable)[input.val % 2^64]?.getD default).value := h_env
    rw [Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt input) (by decide : 97 < 2^64))] at h_value
    have h_index : input.val < (env.data.getTable memoryTable).size := h_bound
    exact h_value.trans (congrArg (fun row : Option (Entry Fp) => (row.getD default).value)
      (Array.getElem?_eq_getElem h_index))

/-- The memory reader as a physical flat-AIR component. -/
def memoryComponent : Air.Flat.Component Fp := ⟨memoryReader⟩

/-- The memory witness only depends on the input address and the fixed data. -/
theorem memory_computable : memoryComponent.circuit.base.ComputableWitnessesWithData := by
  change memoryReader.base.ComputableWitnessesWithData
  intro n input env env'
  simp only [memoryReader, circuit_norm, Operations.forAllFlat]
  intro h_agree h_input
  rw [h_agree.data_eq, h_input]

/-- Every valid addressed read generates a row satisfying the physical checks and semantic read. -/
theorem memory_row_valid (address : Fp) (data : ProverData Fp) (hint : ProverHint Fp)
    (h_address : ValidAddress address data) :
    let env := Environment.fromArray (memoryComponent.buildRow address data hint) data
    memoryComponent.operations.ConstraintsHold env ∧ memoryComponent.Spec env := by
  exact ⟨(memoryComponent.buildRow_constraintsHold address data hint memory_computable h_address).1,
    (memoryComponent.buildRow_spec_requirements address data hint memory_computable h_address
      trivial).1⟩

/-- A table of valid read addresses is constructed with all raw lookup constraints satisfied. -/
theorem memory_table_valid (addresses : List Fp) (data : ProverData Fp) (hint : ProverHint Fp)
    (h_addresses : ∀ address ∈ addresses, ValidAddress address data) :
    (Air.Flat.Table.build memoryComponent addresses data hint).Constraints :=
  Air.Flat.Table.build_constraints memoryComponent addresses data hint memory_computable h_addresses

/-- Read the scalar choice from the row-local hint; absent rows have the IR's zero default. -/
def hintValue (hint : ProverHint Fp) : Fp :=
  ((hint "choice" 1)[0]?.getD default)[0]

/-- A Boolean witness chosen by the prover; the checked relation permits both Boolean values. -/
def booleanChoice : GeneralFormalCircuit Fp unit field where
  main _ := do
    let value ← witness (Witgen.FExpr.hintGet "choice" 1 (.const 0) 0 : Witgen.FExpr Fp)
    assertBool value
    return value
  Spec _ output _ := IsBool output
  ProverAssumptions _ _ hint := IsBool (hintValue hint)
  ProverSpec _ output hint := output = hintValue hint
  soundness := by circuit_proof_all
  completeness := by
    circuit_proof_start [hintValue]
    simp_all [circuit_norm]

/-- The Boolean choice as a physical component with no constrained input cells. -/
def booleanComponent : Air.Flat.Component Fp := ⟨booleanChoice⟩

/-- The Boolean witness depends on the hint channel, which strengthened agreement preserves. -/
theorem boolean_computable : booleanComponent.circuit.base.ComputableWitnessesWithData := by
  change booleanChoice.base.ComputableWitnessesWithData
  intro n input env env'
  simp [booleanChoice, circuit_norm, Operations.forAllFlat,
    FormalAssertion.toSubcircuit, FlatOperation.forAll]
  intro h_agree
  rw [h_agree.hint_eq]

/-- A generated Boolean row has valid constraints and a Boolean semantic output. -/
theorem boolean_row_valid (data : ProverData Fp) (hint : ProverHint Fp)
    (h_hint : IsBool (hintValue hint)) :
    let env := Environment.fromArray (booleanComponent.buildRow () data hint) data
    booleanComponent.operations.ConstraintsHold env ∧ booleanComponent.Spec env := by
  exact ⟨(booleanComponent.buildRow_constraintsHold () data hint boolean_computable h_hint).1,
    (booleanComponent.buildRow_spec_requirements () data hint boolean_computable h_hint trivial).1⟩

/-- Each row can use its own Boolean hint while all rows share the same fixed data. -/
theorem boolean_table_valid (inputs : List (Unit × ProverHint Fp)) (data : ProverData Fp)
    (h_hints : ∀ input ∈ inputs, IsBool (hintValue input.2)) :
    (Air.Flat.Table.buildHinted booleanComponent inputs data).Constraints :=
  Air.Flat.Table.buildHinted_constraints booleanComponent inputs data boolean_computable h_hints

end Examples.Construction
