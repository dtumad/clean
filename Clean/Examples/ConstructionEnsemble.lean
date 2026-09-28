module

public import Clean.Examples.Construction
public import Clean.Air.EnsembleBuild

/-! An explicit assembly with real lookup reads, a public receipt consumer, and independent
Boolean hints. The data is fixed throughout construction; channel balance is proved separately. -/

@[expose] public section

namespace Examples.Construction

open Air.Flat

/-- A receipt promises the addressed value in the fixed memory data. -/
def receipts : Channel Fp Entry where
  name := "read-receipts"
  Guarantees entry data := ReadSpec entry.address entry.value data

/-- The reader publishes the semantic result proved by its bundled child circuit. -/
def receiptReader : GeneralFormalCircuit Fp field field where
  main address := do
    let value ← memoryReader address
    receipts.push ⟨address, value⟩
    return value
  Spec := ReadSpec
  ProverAssumptions address data _ := ValidAddress address data
  channelsWithRequirements := [receipts.toRaw]
  soundness := by
    circuit_proof_start [receipts, memoryReader]
    all_goals simp_all [circuit_norm]
  completeness := by
    circuit_proof_start [receipts, memoryReader]
    all_goals simp_all [circuit_norm]

@[reducible] def receiptComponent : Component Fp := ⟨receiptReader⟩

theorem receipt_computable : receiptReader.base.ComputableWitnesses := by
  intro n input env env'
  simp [receiptReader, memoryReader, circuit_norm, Operations.forAllFlat,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, FlatOperation.forAll]
  intro h_agree h_input
  rw [h_agree.data_eq, h_input]

/-- Two reads requested by the public instance. -/
structure ReadRequests (F : Type) where
  first : Entry F
  second : Entry F
deriving ProvableStruct

/-- The public verifier consumes both semantic receipts. -/
def readVerifier : GeneralFormalCircuit Fp ReadRequests unit where
  main requests := do
    receipts.pull requests.first
    receipts.pull requests.second
  Spec requests _ data := ReadSpec requests.first.address requests.first.value data ∧
    ReadSpec requests.second.address requests.second.value data
  ProverAssumptions requests data _ :=
    ReadSpec requests.first.address requests.first.value data ∧
      ReadSpec requests.second.address requests.second.value data
  soundness := by
    circuit_proof_start [receipts]
    simp_all
  completeness := by
    circuit_proof_start [receipts]
    simp_all

theorem readVerifier_computable : readVerifier.base.ComputableWitnesses := by
  intro n input env env'
  simp [readVerifier, circuit_norm, Operations.forAllFlat]

/-- The read table, an independent Boolean table, and the public verifier. -/
@[reducible] def readEnsemble : Ensemble Fp ReadRequests where
  tables := [receiptComponent, booleanComponent]
  channels := [receipts.toRaw]
  verifier := readVerifier
  verifier_length_zero := by intro input; simp [readVerifier, circuit_norm]

/-- Each component receives its own typed semantic inputs and row-local hints. -/
def readInputs (requests : ReadRequests Fp) (hints : List (ProverHint Fp)) :
    readEnsemble.RowInputs
  | ⟨0, _⟩ => [(requests.first.address, ProverHint.empty Fp),
      (requests.second.address, ProverHint.empty Fp)]
  | ⟨1, _⟩ => hints.map fun hint => ((), hint)
  | ⟨n + 2, h⟩ => False.elim (by change n + 2 < 2 at h; omega)

/-- All physical rows are produced by the generic ensemble builder. -/
def buildReads (requests : ReadRequests Fp) (data : ProverData Fp)
    (hints : List (ProverHint Fp)) : EnsembleWitness readEnsemble :=
  readEnsemble.build requests (readInputs requests hints) data

/-- Semantic address and hint premises suffice for every constructed row's raw checks. -/
theorem buildReads_constraints (requests : ReadRequests Fp) (data : ProverData Fp)
    (hints : List (ProverHint Fp))
    (h_first : ValidAddress requests.first.address data)
    (h_second : ValidAddress requests.second.address data)
    (h_reads : ReadSpec requests.first.address requests.first.value data ∧
      ReadSpec requests.second.address requests.second.value data)
    (h_hints : ∀ hint ∈ hints, IsBool (hintValue hint)) :
    (buildReads requests data hints).Constraints := by
  apply Ensemble.build_constraints _ _ _ _ (ProverHint.empty Fp)
  · intro i
    fin_cases i
    · exact receipt_computable
    · exact boolean_computable
  · intro i input h_input
    fin_cases i
    · simp only [readInputs, List.mem_cons, List.not_mem_nil, or_false] at h_input
      rcases h_input with rfl | rfl
      · exact h_first
      · exact h_second
    · obtain ⟨hint, h_hint, rfl⟩ := List.mem_map.mp h_input
      exact h_hints hint h_hint
  · exact readVerifier_computable
  · exact h_reads

/-- A fixed addressed entry has only one read value. -/
theorem ReadSpec.unique {address x y : Fp} {data : ProverData Fp}
    (hx : ReadSpec address x data) (hy : ReadSpec address y data) : x = y := by
  obtain ⟨_, hx⟩ := hx
  obtain ⟨_, hy⟩ := hy
  exact hx.trans hy.symm

/-- Publishing the receipt introduces no new witness cells or witness computations. -/
theorem receipt_buildRow (address : Fp) (data : ProverData Fp) (hint : ProverHint Fp) :
    receiptComponent.buildRow address data hint = memoryComponent.buildRow address data hint := by
  simp [Component.buildRow, receiptComponent, receiptReader, memoryComponent, memoryReader,
    Circuit.witgen, FlatOperation.witgen, FlatOperation.witgenStep, circuit_norm,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]

private theorem entry_elements {F : Type} (entry : Entry F) :
    toElements entry = #v[entry.address, entry.value] := by
  simp only [toElements, ProvableStruct.structToElements_eq]
  rfl

/-- The physical row emits precisely the semantic read receipt. -/
theorem receipt_row_ledger (entry : Entry Fp) (data : ProverData Fp) (hint : ProverHint Fp)
    (h_address : ValidAddress entry.address data)
    (h_read : ReadSpec entry.address entry.value data) :
    receiptComponent.operations.interactionValuesWith receipts.toRaw
      (Environment.fromArray (receiptComponent.buildRow entry.address data hint) data) =
        [receipts.pushedValue entry] := by
  rw [receipt_buildRow]
  have h_input := memoryComponent.rowInput_buildRow entry.address data data hint
  have h_spec := (memory_row_valid entry.address data hint h_address).2
  change (memoryComponent.buildRow entry.address data hint)[0]?.getD 0 = entry.address at h_input
  rw [Component.Spec, memoryComponent.rowInput_buildRow] at h_spec
  change ReadSpec entry.address (memoryComponent.rowOutput
    (Environment.fromArray (memoryComponent.buildRow entry.address data hint) data)) data at h_spec
  simp only [Component.rowOutput, memoryComponent, memoryReader, circuit_norm,
    Environment.fromArray] at h_spec
  have h_value := h_spec.unique h_read
  change (memoryComponent.buildRow entry.address data hint)[1]?.getD 0 = entry.value at h_value
  simp +instances [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, receiptComponent, receiptReader, memoryReader, circuit_norm,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, FlatOperation.interactions,
    entry_elements, AbstractInteraction.eval, ChannelInteraction.toRaw, Environment.fromArray,
    h_input, h_value]

/-- The physical public verifier consumes exactly the two public requests. -/
theorem readVerifier_ledger (requests : ReadRequests Fp) (data : ProverData Fp) :
    readEnsemble.verifierTable.operations.interactionValuesWith receipts.toRaw
      (Environment.fromInput requests data) =
        [receipts.pulledValue requests.first, receipts.pulledValue requests.second] := by
  have h_requests (F : Type) (req : ReadRequests F) :
      toElements req = #v[req.first.address, req.first.value, req.second.address, req.second.value] := by
    simp [toElements, ProvableStruct.structToElements_eq, circuit_norm, toComponents]
    rfl
  simp +instances [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, Ensemble.verifierTable, readVerifier, circuit_norm,
    AbstractInteraction.eval, ChannelInteraction.toRaw, Environment.fromInput, Environment.fromArray,
    entry_elements, h_requests]

/-- The independent Boolean table emits no receipts, whatever hints were used. -/
theorem boolean_receipts (env : Environment Fp) :
    booleanComponent.operations.interactionValuesWith receipts.toRaw env = [] := by
  simp [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, booleanComponent, booleanChoice, circuit_norm,
    FormalAssertion.toSubcircuit, FlatOperation.interactions]

/-- The assembled ledger includes the public verifier, both real reads, and the Boolean table. -/
theorem buildReads_ledger (requests : ReadRequests Fp) (data : ProverData Fp)
    (hints : List (ProverHint Fp))
    (h_first : ValidAddress requests.first.address data)
    (h_second : ValidAddress requests.second.address data)
    (h_reads : ReadSpec requests.first.address requests.first.value data ∧
      ReadSpec requests.second.address requests.second.value data) :
    (buildReads requests data hints).interactionsWith receipts.toRaw =
      [receipts.pulledValue requests.first, receipts.pulledValue requests.second,
       receipts.pushedValue requests.first, receipts.pushedValue requests.second] := by
  rw [buildReads, Ensemble.build_interactions, readVerifier_ledger]
  simp only [readEnsemble, List.length_cons, List.length_nil, List.ofFn_succ,
    readInputs, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.flatten_cons]
  simp [receipt_row_ledger _ data _ h_first h_reads.1,
    receipt_row_ledger _ data _ h_second h_reads.2, boolean_receipts]

/-- The two returned values balance their public requests with an explicit count bound. -/
theorem buildReads_balanced (requests : ReadRequests Fp) (data : ProverData Fp)
    (hints : List (ProverHint Fp))
    (h_first : ValidAddress requests.first.address data)
    (h_second : ValidAddress requests.second.address data)
    (h_reads : ReadSpec requests.first.address requests.first.value data ∧
      ReadSpec requests.second.address requests.second.value data) :
    (buildReads requests data hints).BalancedChannels := by
  intro channel h_channel
  obtain rfl := List.mem_singleton.mp h_channel
  change BalancedInteractions ((buildReads requests data hints).interactionsWith receipts.toRaw)
  rw [buildReads_ledger _ _ _ h_first h_second h_reads]
  constructor
  · left
    rw [ringChar.eq Fp 97]
    norm_num
  · intro message
    by_cases h_first : (toElements requests.first).toArray = message <;>
      by_cases h_second : (toElements requests.second).toArray = message <;>
      simp [balanceOf, Channel.pulledValue, Channel.pushedValue, h_first, h_second]

/-- The generic builder constructs a complete accepted witness from semantic read/hint premises. -/
theorem buildReads_statement (requests : ReadRequests Fp) (data : ProverData Fp)
    (hints : List (ProverHint Fp))
    (h_first : ValidAddress requests.first.address data)
    (h_second : ValidAddress requests.second.address data)
    (h_reads : ReadSpec requests.first.address requests.first.value data ∧
      ReadSpec requests.second.address requests.second.value data)
    (h_hints : ∀ hint ∈ hints, IsBool (hintValue hint)) :
    readEnsemble.Statement requests :=
  ⟨buildReads requests data hints, rfl,
    buildReads_constraints _ _ _ h_first h_second h_reads h_hints,
    buildReads_balanced _ _ _ h_first h_second h_reads⟩

end Examples.Construction
