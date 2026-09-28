module

public import Clean.Examples.Construction
public import Clean.Circuit.WitnessExport
public meta import Clean.Examples.Construction
public meta import Clean.Circuit.WitnessExport

/-! Regression cases for generated rows, lookup data, and per-row hints. The executable
checkers below are proved equivalent to the components' actual raw checks and row widths. -/

@[expose] public section

namespace TestConstruction
open Examples.Construction

/-- One explicitly keyed table, with all other data keys empty. -/
def keyedRows {width : ℕ} (name : String) (rows : Array (Vector Fp width)) : ProverData Fp :=
  fun key n => if key = name then if h : width = n then h ▸ rows else #[] else #[]

/-- Three indexed memory records, including the largest canonical field value. -/
def memory : ProverData Fp := keyedRows "memory" #[#v[0, 11], #v[1, 42], #v[2, 96]]

/-- Different fixed data at the same addresses. -/
def changedMemory : ProverData Fp := keyedRows "memory" #[#v[0, 12], #v[1, 42], #v[2, 95]]

/-- A hint choosing one scalar field value. -/
def choiceHint (value : Fp) : ProverHint Fp := keyedRows "choice" #[#v[value]]

/-- An actual generated memory row, with the hint explicitly separate from fixed data. -/
def readRow (address : Fp) (data : ProverData Fp) : Array Fp :=
  memoryComponent.buildRow address (data:=data) (hint:=ProverHint.empty Fp)

/-- An actual generated Boolean row at a specified row-local hint. -/
def choiceRow (value : Fp) : Array Fp :=
  booleanComponent.buildRow () (data:=memory) (hint:=choiceHint value)

/-- Check the physical read-row width and its indexed memory lookup. -/
def checkRead (row : Array Fp) (data : ProverData Fp) : Bool :=
  row.size == 2 &&
    let address := row[0]?.getD 0
    let value := row[1]?.getD 0
    let entries := data.getTable memoryTable
    if h : address.val < entries.size then
      decide (address = entries[address.val].address ∧ value = entries[address.val].value)
    else false

/-- The read checker reflects the physical circuit checks, including the lookup's data. -/
theorem checkRead_iff (row : Array Fp) (data : ProverData Fp) :
    checkRead row data = true ↔ row.size = memoryComponent.width ∧
      memoryComponent.operations.ConstraintsHold (Environment.fromArray row data) := by
  rw [Air.Flat.Component.constraintsHold_iff]
  change checkRead row data = true ↔ row.size = 2 ∧
    memoryComponent.rowOperations.ConstraintsHold (Environment.fromArray row data)
  simp +instances [checkRead, memoryComponent, memoryReader,
    Air.Flat.Component.rowOperations, memoryTable, circuit_norm, Environment.fromArray,
    ProvableType.size, Lookup.Contains, Table.toRaw, ProverData.getTable]

/-- Check the physical Boolean row; no generation hint is part of the accepted relation. -/
def checkChoice (row : Array Fp) : Bool :=
  row.size == 1 && decide (IsBool (row[0]?.getD 0))

/-- The Boolean checker reflects the actual raw assertions and row width. -/
theorem checkChoice_iff (row : Array Fp) (data : ProverData Fp) :
    checkChoice row = true ↔ row.size = booleanComponent.width ∧
      booleanComponent.operations.ConstraintsHold (Environment.fromArray row data) := by
  rw [Air.Flat.Component.constraintsHold_iff]
  change checkChoice row = true ↔ row.size = 1 ∧
    booleanComponent.rowOperations.ConstraintsHold (Environment.fromArray row data)
  simp +instances [checkChoice, booleanComponent, booleanChoice,
    Air.Flat.Component.rowOperations, circuit_norm, Environment.fromArray, IsBool.iff_mul_sub_one,
    ProvableType.size, FormalAssertion.toSubcircuit, FlatOperation.constraints,
    FlatOperation.lookups]

/-- A mixed-hint table produced by the actual generic builder. -/
def mixedTable : Air.Flat.Table Fp :=
  Air.Flat.Table.buildHinted booleanComponent
    [((), choiceHint 0), ((), choiceHint 1), ((), choiceHint 0)] (data:=memory)

/-- Both boundary addresses have discharged semantic construction premises. -/
theorem memory_fixture_valid :
    (Air.Flat.Table.build memoryComponent ([0, 2] : List Fp) (data:=memory)
      (hint:=ProverHint.empty Fp)).Constraints := by
  have h_entry (a b : Fp) : (fromElements #v[a, b] : Entry Fp) = ⟨a, b⟩ := by
    rw [ProvableType.fromElements_eq_iff]
    simp only [toElements, ProvableStruct.structToElements_eq]
    rfl
  apply memory_table_valid (addresses:=[0, 2])
  intro address h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · simp [ValidAddress, memory, keyedRows, ProverData.getTable, memoryTable, h_entry,
      show size Entry = 2 from rfl]
  · simp [ValidAddress, memory, keyedRows, ProverData.getTable, memoryTable, h_entry,
      show size Entry = 2 from rfl,
      show (2 : Fp).val = 2 from by decide]

/-- The varying hints satisfy their own prover premises, yielding a valid physical table. -/
theorem mixed_fixture_valid : mixedTable.Constraints := by
  apply boolean_table_valid (inputs:=[((), choiceHint 0), ((), choiceHint 1), ((), choiceHint 0)])
  intro input h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Empty input lists construct an empty table satisfying the same raw relation. -/
theorem empty_fixture_valid :
    (Air.Flat.Table.buildHinted booleanComponent [] (data:=memory)).Constraints :=
  boolean_table_valid [] memory (by simp)

/-- The list-backed reference interpreter for the reader's actual witness operations. -/
def referenceReadRow (address : Fp) (data : ProverData Fp) : Array Fp :=
  (FlatOperation.dynamicWitnesses memoryComponent.rowOperations.toFlat
    (data:=data) (hint:=ProverHint.empty Fp) [address]).toArray

/-- The original empty-data calling convention retains its behavior. -/
example (hint : ProverHint Fp) (ops : List (FlatOperation Fp)) (input : Array Fp) :
    FlatOperation.witgen hint ops input =
      FlatOperation.witgen hint ops input (data:=fun _ _ => #[]) := rfl

/-- This consumer instantiates the generic array/list agreement at the same data and hint. -/
theorem readRow_reference (address : Fp) (data : ProverData Fp) :
    readRow address (data:=data) = referenceReadRow address (data:=data) :=
  FlatOperation.witgen_eq_dynamicWitnesses (ProverHint.empty Fp)
    memoryComponent.rowOperations.toFlat #[address] (data:=data)

/-- Cell equality alone cannot establish equality of data-reading witness programs. -/
theorem data_needs_agreement : ∃ env env' : ProverEnvironment Fp,
    env.get = env'.get ∧
    (Witgen.WitgenIR.ofFExpr (.dataGet "memory" 2 (.const 0) 1)).eval env ≠
      (Witgen.WitgenIR.ofFExpr (.dataGet "memory" 2 (.const 0) 1)).eval env' := by
  refine ⟨.fromArray #[] (data:=memory) (hint:=ProverHint.empty Fp),
    .fromArray #[] (data:=changedMemory) (hint:=ProverHint.empty Fp), rfl, ?_⟩
  intro h
  have h_value := congrArg (fun values : Vector Fp 1 => values[0]) h
  simp only [circuit_norm, ProverEnvironment.fromArray, memory, changedMemory,
    keyedRows] at h_value
  change (11 : Fp) = 12 at h_value
  exact (by decide : (11 : Fp) ≠ 12) h_value

/-- Cell equality alone cannot establish equality of hint-reading witness programs. -/
theorem hint_needs_agreement : ∃ env env' : ProverEnvironment Fp,
    env.get = env'.get ∧
    (Witgen.WitgenIR.ofFExpr (.hintGet "choice" 1 (.const 0) 0)).eval env ≠
      (Witgen.WitgenIR.ofFExpr (.hintGet "choice" 1 (.const 0) 0)).eval env' := by
  refine ⟨.fromArray #[] (data:=memory) (hint:=choiceHint 0),
    .fromArray #[] (data:=memory) (hint:=choiceHint 1), rfl, ?_⟩
  intro h
  have h_value := congrArg (fun values : Vector Fp 1 => values[0]) h
  simp only [circuit_norm, ProverEnvironment.fromArray, choiceHint,
    keyedRows] at h_value
  change (0 : Fp) = 1 at h_value
  exact zero_ne_one h_value

/-- Accepted and rejected cases evaluated on physical rows from the real builders. -/
def outcomes : List (String × Bool × Bool) :=
  [("first-address", true, checkRead (readRow 0 (data:=memory)) (data:=memory)),
   ("last-address", true, checkRead (readRow 2 (data:=memory)) (data:=memory)),
   ("changed-data-regenerated", true,
     checkRead (readRow 0 (data:=changedMemory)) (data:=changedMemory)),
   ("changed-data-old-row", false,
     checkRead (readRow 0 (data:=memory)) (data:=changedMemory)),
   ("input-layout", true, (readRow 2 (data:=memory))[0]?.getD 0 == 2),
   ("same-input-different-data", true,
     (readRow 0 (data:=memory))[0]? == (readRow 0 (data:=changedMemory))[0]?),
   ("data-changes-witness", true,
     (readRow 0 (data:=memory))[1]? != (readRow 0 (data:=changedMemory))[1]?),
   ("array-list-first", true, readRow 0 (data:=memory) == referenceReadRow 0 (data:=memory)),
   ("array-list-last", true, readRow 2 (data:=memory) == referenceReadRow 2 (data:=memory)),
   ("read-table-checks", true,
     (Air.Flat.Table.build memoryComponent ([0, 2] : List Fp) (data:=memory)
       (hint:=ProverHint.empty Fp)).table.all (checkRead · (data:=memory))),
   ("corrupt-read-value", false, checkRead #[0, 12] (data:=memory)),
   ("invalid-address", false, checkRead (readRow 3 (data:=memory)) (data:=memory)),
   ("empty-memory", false,
     checkRead (readRow 0 (data:=fun _ _ => #[])) (data:=fun _ _ => #[])),
   ("wrong-stored-address", false,
     checkRead #[0, 11] (data:=keyedRows "memory" #[#v[1, 11]])),
   ("short-read-row", false, checkRead #[0] (data:=memory)),
   ("long-read-row", false, checkRead #[0, 11, 0] (data:=memory)),
   ("hint-zero", true, checkChoice (choiceRow 0)),
   ("hint-one", true, checkChoice (choiceRow 1)),
   ("different-hints-one-table", true, mixedTable.table == [#[0], #[1], #[0]]),
   ("mixed-table-checks", true, mixedTable.table.all checkChoice),
   ("non-boolean-output", false, checkChoice #[2]),
   ("non-boolean-hint", false, checkChoice (choiceRow 2)),
   ("alternative-boolean-witness", true, checkChoice ((choiceRow 0).set! 0 1)),
   ("short-boolean-row", false, checkChoice #[]),
   ("long-boolean-row", false, checkChoice #[0, 1]),
   ("filtered-reader", true,
     FlatOperation.witgen (ProverHint.empty Fp)
       (FlatOperation.witnessOperationsOnly memoryComponent.rowOperations.toFlat)
       #[2] (data:=memory) == readRow 2 (data:=memory)),
   ("legacy-empty-data", true,
     FlatOperation.witgen (ProverHint.empty Fp) [] #[7] == #[7]),
   ("unrelated-data-key", true,
     checkRead (readRow 0 (data:=memory))
       (data:=fun key width => if key = "unrelated" then #[Vector.replicate width 9]
         else memory key width)),
   ("empty-table", true,
     (Air.Flat.Table.buildHinted booleanComponent [] (data:=memory)).table.isEmpty)]

/-- Print each observed result and fail immediately on an unexpected outcome. -/
def run : IO Unit := do
  for (name, expected, observed) in outcomes do
    IO.println s!"{name}: expected={expected}, observed={observed}"
    unless expected == observed do
      throw <| IO.userError s!"construction case failed: {name}"
  IO.println s!"PASS: {outcomes.length} construction cases"

#eval! run

#assert_exportable memoryReader
#assert_exportable booleanChoice

end TestConstruction
