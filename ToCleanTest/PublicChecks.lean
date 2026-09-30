module

public import ToClean.Circuit.VerifierAssertions
public import Clean.Air.Extraction.Rust
public import Clean.Examples.FibonacciVm.Circuit
public import Clean.Utils.Primes

/-! # Public assertion acceptance and extraction regression

The empty physical inventory isolates the public verifier: its raw ensemble statement must
still enforce all checks. This is a regression fixture, not an SP1 consumer migration.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]

def zeroCheckEnsemble (name : String) (n : ℕ) : Ensemble F (fields n) where
  tables := []
  unique_names := by simp
  channels := [(Verifier.zeroChannel name).toRaw]
  verifier := Verifier.zerosProgram name n

theorem zeroCheckEnsemble_statement (name : String) (n : ℕ) (input : (fields n) F) :
    (zeroCheckEnsemble (F := F) name n).Statement input ↔
      (2 * n < ringChar F ∨ ringChar F = 0) ∧ ∀ value ∈ input.toList, value = 0 := by
  constructor
  · rintro ⟨witness, same, constraints, balanced⟩
    have empty : witness.tables = [] := by
      apply List.length_eq_zero_iff.mp
      exact witness.same_length.symm
    have valid := balanced (Verifier.zeroChannel name).toRaw (by simp [zeroCheckEnsemble])
    simp only [EnsembleWitness.BalancedChannel, EnsembleWitness.interactionsWith,
      EnsembleWitness.verifierInteractionsWith, EnsembleWitness.tableContext,
      TableContext.interactionsWith, empty, List.flatMap_nil, List.append_nil] at valid
    change BalancedInteractions ((Verifier.zerosProgram (F := F) name n).circuitOperations.interactionValuesWith
        (Verifier.zeroChannel name).toRaw (.fromInput witness.publicInput witness.data)) at valid
    rw [Verifier.zerosProgram_balanced_iff,
      ProvableType.eval_fromInput_varFromOffset_zero] at valid
    exact same ▸ valid
  · intro valid
    let witness : EnsembleWitness (zeroCheckEnsemble (F := F) name n) :=
      { tables := []
        publicInput := input
        same_length := rfl
        same_circuits := by intro i hi; simp [zeroCheckEnsemble] at hi }
    refine ⟨witness, rfl, ?_, ?_⟩
    · simp [witness, EnsembleWitness.Constraints, EnsembleWitness.tableContext, TableContext.Constraints]
    · intro channel member
      have same : channel = (Verifier.zeroChannel name).toRaw := by
        simpa only [zeroCheckEnsemble, List.mem_singleton] using member
      subst channel
      simp only [EnsembleWitness.BalancedChannel, EnsembleWitness.interactionsWith,
        EnsembleWitness.verifierInteractionsWith, EnsembleWitness.tableContext,
        TableContext.interactionsWith, witness, List.flatMap_nil, List.append_nil]
      change BalancedInteractions ((Verifier.zerosProgram (F := F) name n).circuitOperations.interactionValuesWith
          (Verifier.zeroChannel name).toRaw (.fromInput input _))
      rw [Verifier.zerosProgram_balanced_iff, ProvableType.eval_fromInput_varFromOffset_zero]
      exact valid

end Air.Flat

namespace PublicChecks

/-- Fibonacci public state and nine independently checked public cells. -/
abbrev Input := ProvablePair fieldTriple (fields 9)

/-- Retain Fibonacci's semantic verifier and require every extra public cell to be zero. -/
def verifier : Verifier.Program (F pBabybear) Input where
  main input := do
    fibonacciVerifier.main input.1
    Verifier.checkZeros "public-checks" input.2.toList
  Spec input data := fibonacciVerifier.Spec input.1 data ∧ ∀ value ∈ input.2.toList, value = 0
  soundness := by
    intro env guarantees
    simp only [Verifier.operations_bind, Verifier.Operations.circuitOperations,
      Verifier.Operations.interactions, List.map_append, Operations.FullGuarantees,
      Operations.interactions_append, List.forall_mem_append] at guarantees
    constructor
    · simpa [circuit_norm, explicit_provable_type] using
        (fibonacciVerifier (p := pBabybear)).soundness env guarantees.1
    · have checks := (Verifier.checkZeros_guarantees _ _ env).mp guarantees.2
      simpa [circuit_norm, explicit_provable_type] using checks

/-- Keep all three physical Fibonacci components and append only the fresh check channel. -/
def ensemble : Air.Flat.Ensemble (F pBabybear) Input where
  tables := (fibonacciEnsemble (p := pBabybear)).ensemble.tables
  unique_names := (fibonacciEnsemble (p := pBabybear)).ensemble.unique_names
  channels := (fibonacciEnsemble (p := pBabybear)).ensemble.channels ++
    [(Verifier.zeroChannel "public-checks").toRaw]
  verifier := verifier

end PublicChecks

/-- Generate the regression directly through Clean's upstream Rust exporter. -/
def main (args : List String) : IO Unit := do
  let config : Air.Flat.WitnessGeneration.Config (F pBabybear) unit :=
    { modes := [], padding := [], fuel := 4 }
  let output := match args with
    | [] => Air.Flat.Extraction.Rust.ensembleToRust "PublicChecksProgram"
        (Air.Flat.zeroCheckEnsemble (F := F pBabybear) "public-checks" 9) config
    | ["fibonacci"] => Air.Flat.Extraction.Rust.ensembleToRust "CheckedFibonacciProgram"
        PublicChecks.ensemble (FibonacciWitness.config (p := pBabybear) 100000)
    | _ => .error "expected no arguments or fibonacci"
  match output with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
