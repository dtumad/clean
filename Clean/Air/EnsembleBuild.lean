module

public import Clean.Air.FlatEnsemble
public import Clean.Air.TableBuild

/-! # Explicit ensemble construction

Typed semantic inputs and row-local hints build every registered table at one shared data
value. The verifier has no witness cells, so its physical row is the same row constructed by
`Table.build`. Constraint proofs consume the formal circuits' computability and prover premises;
channel balance remains a separate global obligation.

The assembly and verifier bridges originate in dtumad/sp1-lean's `ToClean/Air/EnsembleBuild`.
-/

@[expose] public section

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

namespace Air.Flat
open Circuit

/-- **Assemble an ensemble witness from a list of built tables.** The caller supplies the tables in
the ensemble's own order, the shared committed prover data, and the public input; the one proof
obligation is that the tables' components are the ensemble's components, as a list equation. -/
def EnsembleWitness.ofTables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (data : ProverData F) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) : EnsembleWitness ens where
  tables := tables
  data := data
  publicInput := publicInput
  same_length := by rw [← hmap, List.length_map]
  same_circuits := by
    intro i hi
    have hi' : i < (tables.map (·.component)).length := by rw [hmap]; exact hi
    rw [← List.getElem_of_eq hmap hi', List.getElem_map]
  same_data := hdata

@[circuit_norm] lemma EnsembleWitness.ofTables_tables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (data : ProverData F) (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) :
    (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).tables = tables := rfl

@[circuit_norm] lemma EnsembleWitness.ofTables_data (ens : Ensemble F PublicIO) (tables : List (Table F))
    (data : ProverData F) (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) :
    (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).data = data := rfl

@[circuit_norm] lemma EnsembleWitness.ofTables_publicInput (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (data : ProverData F) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) :
    (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).publicInput =
      publicInput := rfl

/-- The assembled witness's full table list, verifier row included, in closed form. This is the
list `EnsembleWitness.Constraints` and the channel balances quantify over. -/
lemma EnsembleWitness.ofTables_allTables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (data : ProverData F) (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables)
    (hdata : ∀ table ∈ tables, table.data = data) :
    (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).allTables =
      (EnsembleWitness.ofTables ens tables data publicInput hmap hdata).verifierTable ::
        tables := rfl

/-! ## The verifier row is a built row -/

namespace Component

/-- **A circuit that generates no witness cells builds exactly the row it was seeded with.** The
generated array has the seed's size (`size_witgen` at `localLength = 0`) and agrees with it
at every index (`getElem?_witgen_of_lt`), so it *is* the seed. -/
theorem buildRow_of_localLength_zero (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) (hzero : c.circuit.localLength (varFromOffset c.Input 0) = 0) :
    c.buildRow input data hint = (toElements input).toArray := by
  have hlen : ((c.circuit.main (varFromOffset c.Input 0)).operations (size c.Input)).localLength
      = 0 := by
    rw [show ((c.circuit.main (varFromOffset c.Input 0)).operations (size c.Input)).localLength
      = (c.circuit.main (varFromOffset c.Input 0)).localLength (size c.Input) from rfl,
      c.circuit.localLength_eq, hzero]
  have hsize : (c.buildRow input data hint).size = (toElements input).toArray.size := by
    rw [buildRow, Circuit.size_witgen, Vector.size_toArray, hlen, Nat.add_zero]
  refine Array.ext hsize ?_
  intro i hi hi'
  have hbound : i < ((c.circuit.main (varFromOffset c.Input 0)).witgen hint (data:=data)
      (toElements input).toArray).size := hi
  have := Circuit.getElem?_witgen_of_lt (c.circuit.main (varFromOffset c.Input 0))
    hint (init := (toElements input).toArray) hi' (data:=data)
  rw [Array.getElem?_eq_getElem hbound] at this
  show ((c.circuit.main (varFromOffset c.Input 0)).witgen hint (data:=data)
    (toElements input).toArray)[i]'hbound = _
  simpa using this

end Component

/-- **Clean's hand-written verifier row is the row `Table.build` produces**, for any assembled
witness. An ensemble's verifier generates no witness cells by definition, so its built row is its
input row — which is exactly the array `EnsembleWitness.verifierTable` writes down. -/
theorem verifierTable_eq_build {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (hint : ProverHint F) :
    witness.verifierTable =
      Table.build ens.verifierTable [witness.publicInput] witness.data hint := by
  have hzero : ens.verifierTable.circuit.localLength
      (varFromOffset ens.verifierTable.Input 0) = 0 := ens.verifier_length_zero _
  rw [Table.ext_iff]
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show size PublicIO = ens.verifierTable.width
    rw [Component.width, GeneralFormalCircuit.size_eq, hzero, Nat.add_zero]
    with_unfolding_all rfl
  · show [(toElements witness.publicInput).toArray] = _
    rw [Table.build_table]
    -- the singleton is spelled at `ens.verifierTable.Input`, which is `PublicIO` only by unfolding
    -- `Ensemble.verifierTable`; `rw [List.map_cons]` cannot assign through that, so reduce the map
    -- by `show` and pass the row explicitly
    show _ = [ens.verifierTable.buildRow witness.publicInput witness.data hint]
    exact congrArg (fun r => [r])
      (Component.buildRow_of_localLength_zero ens.verifierTable witness.publicInput witness.data hint
        hzero).symm

namespace Ensemble

/-- Semantic inputs and row-local hints indexed by the ensemble's registered components. -/
abbrev RowInputs (ens : Ensemble F PublicIO) :=
  (i : Fin ens.tables.length) → List ((ens.tables[i]).Input F × ProverHint F)

/-- Construct every component table at the same fixed prover data. -/
def buildTables (ens : Ensemble F PublicIO) (inputs : ens.RowInputs) (data : ProverData F) :
    List (Table F) :=
  List.ofFn fun i => Table.buildHinted ens.tables[i] (inputs i) data

@[circuit_norm]
theorem buildTables_components (ens : Ensemble F PublicIO) (inputs : ens.RowInputs)
    (data : ProverData F) : (ens.buildTables inputs data).map (·.component) = ens.tables := by
  simp [buildTables, List.map_ofFn, Function.comp_def, circuit_norm]

@[circuit_norm]
theorem buildTables_data (ens : Ensemble F PublicIO) (inputs : ens.RowInputs)
    (data : ProverData F) : ∀ table ∈ ens.buildTables inputs data, table.data = data := by
  simp [buildTables, List.mem_ofFn, circuit_norm]

/-- Assemble all registered tables from semantic inputs. Balance is deliberately not a field
of the constructor: it is a separate property of the actual assembled interaction ledger. -/
def build (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (inputs : ens.RowInputs)
    (data : ProverData F) : EnsembleWitness ens :=
  EnsembleWitness.ofTables ens (ens.buildTables inputs data) data publicInput
    (ens.buildTables_components inputs data) (ens.buildTables_data inputs data)

@[circuit_norm]
theorem build_tables (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (inputs : ens.RowInputs) (data : ProverData F) :
    (ens.build publicInput inputs data).tables = ens.buildTables inputs data := rfl

@[circuit_norm]
theorem build_data (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (inputs : ens.RowInputs) (data : ProverData F) :
    (ens.build publicInput inputs data).data = data := rfl

@[circuit_norm]
theorem build_publicInput (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (inputs : ens.RowInputs) (data : ProverData F) :
    (ens.build publicInput inputs data).publicInput = publicInput := rfl

/-- All generated component rows and the public verifier satisfy their raw checks. The caller
supplies semantic prover premises, not validity proofs for the constructed rows. -/
theorem build_constraints (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (inputs : ens.RowInputs) (data : ProverData F) (verifierHint : ProverHint F)
    (h_computable : ∀ i : Fin ens.tables.length, (ens.tables[i]).circuit.base.ComputableWitnesses)
    (h_inputs : ∀ i : Fin ens.tables.length, ∀ input ∈ inputs i,
      (ens.tables[i]).circuit.ProverAssumptions input.1 data input.2)
    (h_verifier_computable : ens.verifier.base.ComputableWitnesses)
    (h_verifier : ens.verifier.ProverAssumptions publicInput data verifierHint) :
    (ens.build publicInput inputs data).Constraints := by
  rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
  constructor
  · rw [verifierTable_eq_build _ verifierHint]
    apply Table.build_constraints _ _ _ _ h_verifier_computable
    intro input h_input
    obtain rfl := List.mem_singleton.mp h_input
    exact h_verifier
  · intro table h_table
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h_table
    exact Table.buildHinted_constraints _ _ _ (h_computable i) (h_inputs i)

/-- The complete per-channel ledger, including the verifier and every registered table.
No balance or multiplicity bound is inferred merely from constructing the rows. -/
theorem build_interactions (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (inputs : ens.RowInputs) (data : ProverData F) (channel : RawChannel F) :
    (ens.build publicInput inputs data).interactionsWith channel =
      ens.verifierTable.operations.interactionValuesWith channel
        (Environment.fromInput publicInput data) ++
      (List.ofFn fun i : Fin ens.tables.length =>
        (inputs i).flatMap fun input => (ens.tables[i]).operations.interactionValuesWith channel
          (Environment.fromArray
            ((ens.tables[i]).buildRow input.1 data input.2) data)).flatten := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    build_tables, buildTables]
  rw [List.flatMap_def, List.map_ofFn]
  simp only [Function.comp_def, Table.buildHinted_interactions]
  congr 1
  simp [Table.interactionsWith, EnsembleWitness.verifierTable, Table.environment,
    build_publicInput, build_data]
  rfl

end Ensemble

end Air.Flat
