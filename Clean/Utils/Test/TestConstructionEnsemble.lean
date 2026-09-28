module

public import Clean.Examples.ConstructionEnsemble
public import Clean.Utils.Test.TestConstruction
public meta import Clean.Examples.ConstructionEnsemble
public meta import Clean.Utils.Test.TestConstruction

/-! Regressions through the actual ensemble builder and its physical channel ledger. -/

@[expose] public section

namespace TestConstructionEnsemble

open Examples.Construction TestConstruction Air.Flat

def requests : ReadRequests Fp := ⟨⟨0, 11⟩, ⟨2, 96⟩⟩
def hints : List (ProverHint Fp) := [choiceHint 0, choiceHint 1, choiceHint 0]
def assembled : EnsembleWitness readEnsemble := buildReads requests memory hints

/-- The semantic premises of the concrete two-read fixture are kernel checked. -/
theorem fixture_statement : readEnsemble.Statement requests := by
  have h_entry (a b : Fp) : (fromElements #v[a, b] : Entry Fp) = ⟨a, b⟩ := by
    rw [ProvableType.fromElements_eq_iff]
    simp only [toElements, ProvableStruct.structToElements_eq]
    rfl
  apply buildReads_statement requests memory hints
  · simp [ValidAddress, requests, memory, keyedRows, ProverData.getTable, memoryTable,
      h_entry, show size Entry = 2 from rfl]
  · simp [ValidAddress, requests, memory, keyedRows, ProverData.getTable, memoryTable,
      h_entry, show size Entry = 2 from rfl, show (2 : Fp).val = 2 from by decide]
  · simp [ReadSpec, requests, memory, keyedRows, ProverData.getTable, memoryTable,
      h_entry, show size Entry = 2 from rfl, show (2 : Fp).val = 2 from by decide]
  · intro hint h
    simp only [hints, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Publishing a receipt adds no raw assertions or lookups to the read circuit. -/
theorem receipt_constraints (env : Environment Fp) :
    receiptComponent.operations.ConstraintsHold env ↔
      memoryComponent.operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff, Component.constraintsHold_iff]
  simp [Component.rowOperations, receiptComponent, receiptReader, memoryComponent, memoryReader,
    circuit_norm, GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, FlatOperation.constraints, FlatOperation.lookups]

/-- Evaluate all physical interactions. This ensemble has only the receipt channel. -/
def ledger (witness : EnsembleWitness readEnsemble) : List (Interaction Fp) :=
  witness.allTables.flatMap Table.interactions

/-- Check every message present, plus the field-characteristic count bound. -/
def checkLedger (interactions : List (Interaction Fp)) : Bool :=
  interactions.length < 97 &&
    interactions.all fun interaction => decide (balanceOf interactions interaction.msg = 0)

/-- Physical read rows from the actual generic builder. -/
def readRows : List (Array Fp) := (assembled.tables[0]'(by decide +kernel)).table

def booleanRows (witness : EnsembleWitness readEnsemble) : List (Array Fp) :=
  (witness.tables[1]'(by rw [← witness.same_length]; decide)).table

/-- Evaluate adversarial physical read rows through the same component's operations. -/
def changedLedger (rows : List (Vector Fp 2)) : List (Interaction Fp) :=
  let table : Air.Flat.Table Fp := {
    component := receiptComponent
    width := 2
    table := rows.map Vector.toArray
    data := memory
    uniform_width := by
      intro row h
      obtain ⟨row, _, rfl⟩ := List.mem_map.mp h
      exact row.size_toArray }
  assembled.verifierTable.interactions ++ table.interactions

def outcomes : List (String × Bool × Bool) :=
  [("ensemble-balance", true, checkLedger (ledger assembled)),
   ("ensemble-verifier-count", true,
     (ledger assembled).length == 4),
   ("ensemble-registration", true, assembled.tables.length == 2),
   ("ensemble-read-checks", true, readRows.all (checkRead · memory)),
   ("ensemble-mixed-hints", true, booleanRows assembled == [#[0], #[1], #[0]]),
   ("ensemble-boolean-checks", true, (booleanRows assembled).all checkChoice),
   ("wrong-public-value", false,
     checkLedger (ledger { assembled with publicInput := ⟨⟨0, 12⟩, ⟨2, 96⟩⟩ })),
   ("missing-receipt", false, checkLedger (changedLedger [#v[0, 11]])),
   ("duplicate-receipt", false, checkLedger (changedLedger [#v[0, 11], #v[2, 96], #v[0, 11], #v[2, 96]])),
   ("corrupt-receipt", false, checkLedger (changedLedger [#v[0, 12], #v[2, 96]])),
   ("regenerated-public-values", true,
     checkLedger (ledger (buildReads ⟨⟨0, 12⟩, ⟨2, 95⟩⟩ changedMemory hints))),
   ("non-boolean-ensemble-hint", false,
     (booleanRows (buildReads requests memory [choiceHint 2])).all checkChoice),
   ("alternative-boolean-ensemble-hints", true,
     checkLedger (ledger (buildReads requests memory [choiceHint 1, choiceHint 0])))]

def run : IO Unit := do
  for (name, expected, observed) in outcomes do
    IO.println s!"{name}: expected={expected}, observed={observed}"
    unless expected == observed do
      throw <| IO.userError s!"ensemble case failed: {name}"
  IO.println s!"PASS: {outcomes.length} ensemble cases"

#eval! run

#assert_exportable receiptReader
#assert_exportable readVerifier

end TestConstructionEnsemble
