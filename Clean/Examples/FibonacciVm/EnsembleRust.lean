module

public import Clean.Air.Extraction.Rust
public import Clean.Examples.FibonacciVm.Circuit
public import Clean.Utils.Primes

@[expose] public section

/-- Exercise indexed preprocessing through the real emitter and backend regression. -/
def indexedConfig : Air.Flat.WitnessGeneration.Config (F pBabybear) unit :=
  let config := FibonacciWitness.config (p := pBabybear) 100000
  { config with modes := config.modes.map fun mode => match mode with
    | .preallocated mode => .preallocated { mode with handlers := mode.handlers.map fun handler =>
        { handler with rowIndex := some (.val (.proverInputGet (.const 0))), rowIndex_valid := by rfl } }
    | mode => mode }

def main : IO Unit := do
  match Air.Flat.Extraction.Rust.ensembleToRust
      "FibonacciEnsembleProgram"
      (fibonacciEnsemble (p := pBabybear)).ensemble
      indexedConfig with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
