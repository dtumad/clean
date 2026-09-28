module

public import Clean.Circuit.WitnessGenerationData
public import Clean.Air.FlatComponent
public import Clean.Circuit.Foundations

/-! # Constructing valid physical rows and tables

`Component.buildRow` places semantic input cells before the circuit's generated witness cells.
`buildRow_constraintsHold` applies honest generation and the circuit's completeness proof at
one fixed data/hint environment. `buildRow_spec_requirements` additionally uses soundness and
the semantic assumptions. `Table.buildHinted` lifts these results to inputs with individual
row hints; `Table.build` is the constant-hint specialization.

Data is table-wide and hints are row-local generation inputs. Lookup containment reads data,
so transporting constraints to different data requires agreement on the used lookup tables.
The interaction characterization describes the physical ledger; it does not prove balance.

These additive interfaces are exercised by `Clean.Examples.Construction`. They do not certify
ensemble scheduling, padding, or termination. Adapted from dtumad/sp1-lean at `27148217`;
the construction consumes Clean's existing circuit completeness and soundness theorems.
-/

@[expose] public section

variable {F : Type} [FiniteField F]

/-! ## Environment congruence

`Expression.eval` reads only `env.get`. This is the granular fact behind "the committed `ProverData`
is a free choice": every part of a component's per-row statement that is phrased in evaluated
expressions transports across a change of `data`, and only the parts phrased in `env.data` — lookup
containment and channel guarantees/requirements — do not. -/

theorem Expression.eval_congr {env env' : Environment F} (h : env.get = env'.get)
    (e : Expression F) : Expression.eval env e = Expression.eval env' e := by
  induction e with
  | var v => simp only [Expression.eval, h]
  | const c => rfl
  | add x y ihx ihy => simp only [Expression.eval, ihx, ihy]
  | mul x y ihx ihy => simp only [Expression.eval, ihx, ihy]

namespace Operations

/-- `Operations.ConstraintsHold` transports across any change of environment that preserves the
cells, provided the lookups still hold. The lookup premise is exactly the part of `ConstraintsHold`
that reads `env.data`; it is vacuous for a lookup-free operation list
(`constraintsHold_congr_of_lookups_nil`). -/
theorem constraintsHold_congr {ops : Operations F} {env env' : Environment F}
    (h_get : env.get = env'.get)
    (h_lookups : ∀ l ∈ ops.lookups, l.Contains env → l.Contains env')
    (h : ops.ConstraintsHold env) : ops.ConstraintsHold env' :=
  ⟨fun e he => (Expression.eval_congr h_get e).symm.trans (h.1 e he),
    fun l hl => h_lookups l hl (h.2 l hl)⟩

/-- The usable form: `ConstraintsHold` transports across a change of committed `ProverData` that
agrees on the tables the operations actually look up. This is the exact extent to which the data is
a free choice — `Lookup.Contains` reads `env.data` at one key per lookup and nowhere else. -/
theorem constraintsHold_congr_of_data_agree {ops : Operations F} {env env' : Environment F}
    (h_get : env.get = env'.get)
    (h_data : ∀ l ∈ ops.lookups,
      env.data l.table.name l.table.arity = env'.data l.table.name l.table.arity)
    (h : ops.ConstraintsHold env) : ops.ConstraintsHold env' := by
  refine constraintsHold_congr h_get (fun l hl h_contains => ?_) h
  have h_entry : l.entry.map (Expression.eval env) = l.entry.map (Expression.eval env') := by
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_map, Expression.eval_congr h_get]
  simpa only [Lookup.Contains, ← h_data l hl, ← h_entry] using h_contains

/-- A lookup-free operation list's constraints depend on the environment's cells alone: the
committed `ProverData` is a free choice outright. -/
theorem constraintsHold_congr_of_lookups_nil {ops : Operations F} {env env' : Environment F}
    (h_get : env.get = env'.get) (h_lookups : ops.lookups = [])
    (h : ops.ConstraintsHold env) : ops.ConstraintsHold env' :=
  constraintsHold_congr h_get (by simp [h_lookups]) h

end Operations

/-- Evaluating an interaction reads only the environment's cells. -/
theorem AbstractInteraction.eval_congr {i : AbstractInteraction F} {env env' : Environment F}
    (h : env.get = env'.get) : i.eval env = i.eval env' := by
  simp only [AbstractInteraction.eval, Expression.eval_congr h]

namespace Operations

/-- The concrete interaction values a row emits depend on the environment's cells alone: the
committed `ProverData` is a free choice. (The *predicates* `Interaction.Guarantees`/`Requirements`
do take the data — but as an explicit argument, not through the environment.) -/
theorem interactionValues_congr {ops : Operations F} {env env' : Environment F}
    (h_get : env.get = env'.get) : ops.interactionValues env = ops.interactionValues env' := by
  simp only [interactionValues]
  exact List.map_congr_left fun i _ => AbstractInteraction.eval_congr h_get

/-- Per-channel version of `interactionValues_congr`. -/
theorem interactionValuesWith_congr {ops : Operations F} {channel : RawChannel F}
    {env env' : Environment F} (h_get : env.get = env'.get) :
    ops.interactionValuesWith channel env = ops.interactionValuesWith channel env' := by
  simp only [interactionValuesWith]
  exact List.map_congr_left fun i _ => AbstractInteraction.eval_congr h_get

end Operations

namespace ProvableType
variable {M : TypeMap} [ProvableType M]

omit [FiniteField F] in
/-- The value a row's cells decode to at a given offset depends only on those cells. -/
theorem valueFromOffset_congr (M : TypeMap) [ProvableType M] (offset : ℕ)
    {env env' : Environment F} (h : ∀ i < offset + size M, env.get i = env'.get i) :
    valueFromOffset M offset env = valueFromOffset M offset env' := by
  simp only [valueFromOffset]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_mapRange]
  exact h _ (by omega)

/-- The canonical row input variable reads only the cells below `size M` — the side condition of
`FormalCircuitBase.ComputableWitnessesWithData'`, discharged once for the AIR row layout. -/
theorem onlyAccessedBelow_varFromOffset_zero (M : TypeMap) [ProvableType M] :
    ProverEnvironment.OnlyAccessedBelow (size M) (F := F)
      (Eval.eval · (varFromOffset (F := F) M 0)) := by
  have h_eval : ∀ e : ProverEnvironment F,
      Eval.eval e (varFromOffset (F := F) M 0) = valueFromOffset M 0 e.toEnvironment :=
    fun e => by rw [eval_varFromOffset_prover]; rfl
  intro env env' h
  simp only [h_eval]
  exact valueFromOffset_congr M 0 fun i _ => h _ (by omega)

end ProvableType

namespace Air.Flat
namespace Component

/-! ## The row a component builds for one semantic input -/

/--
The physical AIR row a component builds for one semantic input: the `size Input` input cells,
followed by the cells the circuit's own witness generators compute, in emission order.

This is the row layout `Component` already fixes — `rowInput` decodes the first `size Input` cells,
`rowOperations` starts at offset `size Input` — so seeding array-backed witness generation with
`toElements input` makes the generated cells land exactly where `rowOperations` expects them.
-/
def buildRow (c : Component F) (input : c.Input F) (data : ProverData F) (hint : ProverHint F) :
    Array F :=
  (c.circuit.main (varFromOffset c.Input 0)).witgenWithData data hint (toElements input).toArray

lemma buildRow_def (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) :
    c.buildRow input data hint
      = (c.circuit.main (varFromOffset c.Input 0)).witgenWithData data hint
          (toElements input).toArray := rfl

/-- A built row is a row of the component's table: it has exactly the component's width. -/
theorem size_buildRow (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) : (c.buildRow input data hint).size = c.width := by
  rw [buildRow, Circuit.size_witgenWithData]
  simp only [Vector.size_toArray, width, GeneralFormalCircuit.size_eq]
  congr 1
  exact c.circuit.localLength_eq _ _

/-- The input cells survive witness generation: reading the built row back through the component's
own `rowInput` recovers the semantic input. The environment's committed data is irrelevant, so the
row may be read at a `ProverData` other than the one it was built with. -/
theorem rowInput_buildRow (c : Component F) (input : c.Input F) (data data' : ProverData F)
    (hint : ProverHint F) :
    c.rowInput (Environment.fromArray (c.buildRow input data hint) data') = input := by
  have h : (Vector.mapRange (size c.Input) fun i =>
      (Environment.fromArray (c.buildRow input data hint) data').get (0 + i))
      = toElements input := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_mapRange, Nat.zero_add]
    rw [buildRow, Circuit.getElem?_witgenWithData_of_lt _ _ _ (by simpa using hi)]
    simp
  rw [rowInput, valueFromOffset, h, ProvableType.fromElements_toElements]

/-- The environment a built row is read at, as a `ProverEnvironment` — the same environment
witness generation ran in, so the circuit's completeness theorem applies to it directly. -/
lemma proverEnvironment_buildRow_toEnvironment (c : Component F) (input : c.Input F)
    (data : ProverData F) (hint : ProverHint F) :
    (ProverEnvironment.fromArrayWithData (c.buildRow input data hint) data
      hint).toEnvironment = Environment.fromArray (c.buildRow input data hint) data := rfl

/-! ## The keystone: a built row satisfies the component's constraints -/

/--
**A component builds valid rows.** If the component's circuit has computable witnesses (Clean's
standard honest-prover side condition) and the semantic input satisfies the circuit's
`ProverAssumptions` at the data and hint the row is built with, then the built row satisfies the
component's full per-row assertion system: `ConstraintsHold` and `FullGuarantees`.

This is `GeneralFormalCircuit.original_full_completeness` transported onto the AIR row layout. The
chain is: `FormalCircuitBase.computableWitnessesWithData_implies` (with the row input variable reading only
cells below `size Input`) gives `Circuit.ComputableWitnessesWithData` at the row offset;
`Circuit.witgenWithData_usesLocalWitnesses` turns that into an honest environment carrying the
committed `data`; `original_full_completeness` fires; and `Component.constraintsHold_iff` /
`guarantees_iff` land the result on `Component.operations`.
-/
theorem buildRow_constraintsHold (c : Component F) (input : c.Input F) (data : ProverData F)
    (hint : ProverHint F) (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : c.circuit.ProverAssumptions input data hint) :
    c.operations.ConstraintsHold (Environment.fromArray (c.buildRow input data hint) data) ∧
      c.operations.FullGuarantees (Environment.fromArray (c.buildRow input data hint) data) := by
  set inputVar : Var c.Input F := varFromOffset c.Input 0 with h_inputVar
  set env : ProverEnvironment F :=
    ProverEnvironment.fromArrayWithData (c.buildRow input data hint) data hint with h_env
  -- the row input variable only reads cells below the row offset, so the circuit's
  -- `ComputableWitnessesWithData` obligation applies at that offset
  have h_computable' : (c.circuit.main inputVar).ComputableWitnessesWithData (size c.Input) :=
    FormalCircuitBase.computableWitnessesWithData_implies h_computable (size c.Input) inputVar
      (ProvableType.onlyAccessedBelow_varFromOffset_zero c.Input)
  -- witness generation against the committed data is therefore honest
  have h_uses : env.UsesLocalWitnesses (size c.Input)
      ((c.circuit.main inputVar).operations (size c.Input)) := by
    have h := Circuit.witgenWithData_usesLocalWitnesses (c.circuit.main inputVar) data hint
      (toElements input).toArray (by simpa using h_computable')
    simpa [h_env, buildRow, h_inputVar] using h
  -- the row decodes back to the semantic input
  have h_input : Eval.eval env inputVar = input := by
    rw [h_inputVar, ProvableType.eval_varFromOffset_prover]
    exact c.rowInput_buildRow input data data hint
  have h := c.circuit.original_full_completeness (size c.Input) env inputVar h_uses
    (by rw [h_input]; exact h_prover)
  exact ⟨(c.constraintsHold_iff _).mpr h.1, (c.guarantees_iff _).mpr h.2⟩

/-- A valid row produced by `buildRow` also satisfies the component's semantic specification and
all channel requirements.  This is the composition of honest witness generation with the
component's already-bundled soundness theorem; downstream table transports can use the semantic
boundary without reopening a circuit's witness implementation. -/
theorem buildRow_spec_requirements (c : Component F) (input : c.Input F)
    (data : ProverData F) (hint : ProverHint F)
    (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : c.circuit.ProverAssumptions input data hint)
    (h_assumptions : c.circuit.Assumptions input data) :
    let env := Environment.fromArray (c.buildRow input data hint) data
    c.Spec env ∧ c.operations.FullRequirements env := by
  dsimp only
  let env := Environment.fromArray (c.buildRow input data hint) data
  have built := c.buildRow_constraintsHold input data hint h_computable h_prover
  apply c.weakSoundness
  · change c.circuit.Assumptions (c.rowInput env) data
    rw [show env = Environment.fromArray (c.buildRow input data hint) data from rfl,
      c.rowInput_buildRow input data data hint]
    exact h_assumptions
  · exact built.1
  · exact built.2

/-- Constraints of a built row survive a change of the environment's committed data, for a
lookup-free component. Together with `buildRow_constraintsHold` this is what makes a table's shared
`ProverData` a free choice: the rows do not have to be rebuilt for it. -/
theorem constraintsHold_setData (c : Component F) {row : Array F} {data data' : ProverData F}
    (h_lookups : c.operations.lookups = [])
    (h : c.operations.ConstraintsHold (Environment.fromArray row data)) :
    c.operations.ConstraintsHold (Environment.fromArray row data') :=
  Operations.constraintsHold_congr_of_lookups_nil (env := Environment.fromArray row data)
    (env' := Environment.fromArray row data') rfl h_lookups h

/-- The interactions a built row emits do not depend on the environment's committed data at all. -/
theorem interactionValuesWith_setData (c : Component F) {row : Array F}
    {data data' : ProverData F} (channel : RawChannel F) :
    c.operations.interactionValuesWith channel (Environment.fromArray row data)
      = c.operations.interactionValuesWith channel (Environment.fromArray row data') :=
  Operations.interactionValuesWith_congr (env := Environment.fromArray row data)
    (env' := Environment.fromArray row data') rfl

end Component

/-! ## Assembling a whole table -/

namespace Table

/-- Assemble a flat-AIR table from a component, a list of semantic inputs **each paired with the
prover hint its own row is witnessed at**, and the committed prover data: one
`Component.buildRow` per input, at the component's width.

The committed `data` stays table-level — it is the shared lookup-table content the whole AIR agrees
on — while the hint is row-local, which is what it already was in `Component.buildRow`. -/
def buildHinted (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) : Table F where
  component := c
  width := c.width
  table := inputs.map fun input => c.buildRow input.1 data input.2
  data := data
  uniform_width := by
    intro row h_row
    simp only [List.mem_map] at h_row
    obtain ⟨input, _, rfl⟩ := h_row
    exact c.size_buildRow input.1 data input.2

@[circuit_norm] lemma buildHinted_component (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) : (buildHinted c inputs data).component = c := rfl

@[circuit_norm] lemma buildHinted_data (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) : (buildHinted c inputs data).data = data := rfl

@[circuit_norm] lemma buildHinted_table (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) :
    (buildHinted c inputs data).table = inputs.map fun input => c.buildRow input.1 data input.2 :=
  rfl

@[circuit_norm] lemma buildHinted_length (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) : (buildHinted c inputs data).length = inputs.length :=
  List.length_map ..

lemma buildHinted_environment (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) (row : Array F) :
    (buildHinted c inputs data).environment row = Environment.fromArray row data := rfl

/-- **A built table satisfies its constraints**, given the component's honest-prover side condition
once and the circuit's `ProverAssumptions` per semantic input *at that input's own hint*. -/
theorem buildHinted_constraints (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : ∀ input ∈ inputs, c.circuit.ProverAssumptions input.1 data input.2) :
    (buildHinted c inputs data).Constraints := by
  intro row h_row
  simp only [buildHinted_table, List.mem_map] at h_row
  obtain ⟨input, h_input, rfl⟩ := h_row
  exact (c.buildRow_constraintsHold input.1 data input.2 h_computable (h_prover input h_input)).1

/-- **A built table satisfies its channel guarantees**, under the same hypotheses. -/
theorem buildHinted_guarantees (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : ∀ input ∈ inputs, c.circuit.ProverAssumptions input.1 data input.2) :
    (buildHinted c inputs data).Guarantees := by
  intro row h_row
  simp only [buildHinted_table, List.mem_map] at h_row
  obtain ⟨input, h_input, rfl⟩ := h_row
  exact (c.buildRow_constraintsHold input.1 data input.2 h_computable (h_prover input h_input)).2

/-- The built table's interaction list on one channel, in closed form: the per-input evaluated
interaction lists, concatenated in input order. -/
theorem buildHinted_interactions (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) (channel : RawChannel F) :
    (buildHinted c inputs data).interactionsWith channel =
      inputs.flatMap fun input =>
        c.operations.interactionValuesWith channel
          (Environment.fromArray (c.buildRow input.1 data input.2) data) := by
  simp only [interactionsWith, buildHinted_table, buildHinted_component, buildHinted_environment,
    List.flatMap_map]

/-- The same, for all channels at once. -/
theorem buildHinted_interactionValues (c : Component F) (inputs : List (c.Input F × ProverHint F))
    (data : ProverData F) :
    (buildHinted c inputs data).interactions =
      inputs.flatMap fun input =>
        c.operations.interactionValues
          (Environment.fromArray (c.buildRow input.1 data input.2) data) := by
  simp only [interactions, buildHinted_table, buildHinted_component, buildHinted_environment,
    List.flatMap_map]

/-! ### The constant-hint special case

One hint for the whole table. Kept as its own `def` so that its layout lemmas stay `rfl`, and tied
to the general builder by `build_eq_buildHinted`, from which its three theorems are derived. -/

/-- Assemble a flat-AIR table from a component, a list of semantic inputs, the committed prover
data, and a **single** prover hint shared by every row: one `Component.buildRow` per input, at the
component's width. The constant-hint case of `buildHinted`. -/
def build (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) : Table F where
  component := c
  width := c.width
  table := inputs.map (c.buildRow · data hint)
  data := data
  uniform_width := by
    intro row h_row
    simp only [List.mem_map] at h_row
    obtain ⟨input, _, rfl⟩ := h_row
    exact c.size_buildRow input data hint

@[circuit_norm] lemma build_component (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) : (build c inputs data hint).component = c := rfl

@[circuit_norm] lemma build_data (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) : (build c inputs data hint).data = data := rfl

@[circuit_norm] lemma build_table (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) :
    (build c inputs data hint).table = inputs.map (c.buildRow · data hint) := rfl

@[circuit_norm] lemma build_length (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) : (build c inputs data hint).length = inputs.length :=
  List.length_map ..

lemma build_environment (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) (row : Array F) :
    (build c inputs data hint).environment row = Environment.fromArray row data := rfl

/-- **The single-hint builder is the constant-hint case of the general one.** Pairing every input
with the same hint builds the very same table — the three theorems below are this rewrite applied to
their general forms. -/
theorem build_eq_buildHinted (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) :
    build c inputs data hint = buildHinted c (inputs.map (·, hint)) data := by
  rw [ext_iff]
  refine ⟨rfl, rfl, ?_, rfl⟩
  simp only [build_table, buildHinted_table, List.map_map, Function.comp_def]

/-- **A built table satisfies its constraints**, given the component's honest-prover side condition
once and the circuit's `ProverAssumptions` per semantic input. -/
theorem build_constraints (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : ∀ input ∈ inputs, c.circuit.ProverAssumptions input data hint) :
    (build c inputs data hint).Constraints := by
  rw [build_eq_buildHinted]
  refine buildHinted_constraints c _ data h_computable fun ih h_ih => ?_
  obtain ⟨input, h_input, rfl⟩ := List.mem_map.mp h_ih
  exact h_prover input h_input

/-- **A built table satisfies its channel guarantees**, under the same hypotheses. -/
theorem build_guarantees (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) (h_computable : c.circuit.base.ComputableWitnessesWithData)
    (h_prover : ∀ input ∈ inputs, c.circuit.ProverAssumptions input data hint) :
    (build c inputs data hint).Guarantees := by
  rw [build_eq_buildHinted]
  refine buildHinted_guarantees c _ data h_computable fun ih h_ih => ?_
  obtain ⟨input, h_input, rfl⟩ := List.mem_map.mp h_ih
  exact h_prover input h_input

/-- The built table's interaction list on one channel, in closed form: the per-input evaluated
interaction lists, concatenated in input order. Downstream ledger and balance reasoning reads this
instead of unfolding the rows again. -/
theorem build_interactions (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) (channel : RawChannel F) :
    (build c inputs data hint).interactionsWith channel =
      inputs.flatMap fun input =>
        c.operations.interactionValuesWith channel
          (Environment.fromArray (c.buildRow input data hint) data) := by
  rw [build_eq_buildHinted, buildHinted_interactions, List.flatMap_map]

/-- The same, for all channels at once. -/
theorem build_interactionValues (c : Component F) (inputs : List (c.Input F)) (data : ProverData F)
    (hint : ProverHint F) :
    (build c inputs data hint).interactions =
      inputs.flatMap fun input =>
        c.operations.interactionValues (Environment.fromArray (c.buildRow input data hint) data) := by
  rw [build_eq_buildHinted, buildHinted_interactionValues, List.flatMap_map]

/-- **Every interaction a table emits is on one of its component's declared channels.**

Clean has the contrapositive shape — `interactionsWith_eq_nil_of_not_mem_channels` — and derives it
from `channels_subset` inline. The positive form is what a *whole-ledger* argument needs: given a
key, decide which channel it came from. Splitting it out costs nothing and makes the fact citable.

Gap against upstream: this is a two-line consequence of `channels_subset` that
`Clean/Air/FlatComponent.lean` proves inside another lemma rather than stating. -/
theorem channel_mem_channels_of_mem_interactions (table : Table F) :
    ∀ i ∈ table.interactions, i.channel ∈ table.component.circuit.channels := by
  rw [Table.forall_interactions_iff]
  intro _ _ i interactionMem
  rw [AbstractInteraction.eval_channel]
  simp only [Component.interactions_eq] at interactionMem
  refine table.component.circuit.channels_subset table.component.rowInputVar
    table.component.rowOffset ?_
  simp only [Operations.channels, List.mem_map]
  exact ⟨i, interactionMem, rfl⟩

end Table
end Air.Flat
