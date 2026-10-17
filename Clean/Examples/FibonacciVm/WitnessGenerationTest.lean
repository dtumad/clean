module

public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Backends.Program
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Examples.FibonacciVm.Ensemble
public meta import Clean.Backends.Program
public meta import Clean.Utils.Primes

@[expose] public section

namespace Air.Flat.WitnessGenerationTest

open Air.Flat.WitnessGeneration

def steps : ℕ := 32

def publicInput : fieldTriple (F pBabybear) :=
  let state := fibonacci steps
  (steps, state.1, state.2)

def result : Except String (List ℕ × ℕ × ℕ × Bool × Bool) :=
  match FibonacciWitness.generate publicInput 1000 with
  | .error error => .error (toString error)
  | .ok witness =>
      match witness.tables with
      | _ :: _ :: bytes :: _ =>
          let multiplicities := bytes.table.map fun row => row[1]?.getD 0
          .ok (
            witness.tables.map (·.length),
            multiplicities.sum.val,
            (multiplicities.map FiniteField.val).max?.getD 0,
            constraintsHold witness,
            channelsBalanced witness)
      | _ => .error "ensemble has no byte table"

/--
The verifier seed automatically creates 32 Fibonacci rows; their pulls create 32 distinct addition rows; byte range checks are accumulated in the 256 fixed byte rows.
-/
example : result = .ok ([32, 32, 256], 32, 2, true, true) := by native_decide

def derivedBytesData : Bool :=
  match FibonacciWitness.generate publicInput 1000 with
  | .error _ => false
  | .ok witness =>
      let rows := witness.data "bytes" 2
      rows.size == 256 && match rows[42]? with
        | some row => row[0] == (42 : F pBabybear)
        | none => false

/-- The byte component exports its complete `(value, multiplicity)` input rows. -/
example : derivedBytesData = true := by native_decide

def dynamicComponentData : Bool :=
  match FibonacciWitness.generate publicInput 1000 with
  | .error _ => false
  | .ok witness =>
      let rows := witness.data "fibonacci" 4
      rows.size == 32 && match rows[0]? with
        | some row => row[0] == 1 && row[1] == 0 && row[2] == 0 && row[3] == 1
        | none => false

/-- Demand-generated components expose their complete inputs just like fixed components. -/
example : dynamicComponentData = true := by native_decide

def repeatedSteps : ℕ := 400

def repeatedPublicInput : fieldTriple (F pBabybear) :=
  let state := fibonacci repeatedSteps
  (repeatedSteps, state.1, state.2)

def repeatedResult : Except String (List ℕ × Bool × Bool) :=
  match FibonacciWitness.generate repeatedPublicInput 2000 with
  | .error error => .error (toString error)
  | .ok witness => .ok (
      witness.tables.map (·.length),
      constraintsHold witness,
      channelsBalanced witness)

/-- Repeated addition pulls coalesce after the period of Fibonacci modulo 256. -/
example : repeatedResult = .ok ([512, 512, 256], true, true) := by native_decide

/-- Zero minimum rows preserve empty dynamic tables without changing fixed inventory. -/
def emptyDynamicResult : Except String (List ℕ × Bool × Bool) := do
  let config := FibonacciWitness.config (p := pBabybear) 20
  let config := { config with components := config.components.map fun (name, generation) =>
    (name, { generation with padding := { generation.padding with minimumRows := 0 } }) }
  match Air.Flat.WitnessGeneration.generate (fibonacciEnsemble (p := pBabybear))
      config (0, 0, 1) () with
  | .error error => .error (toString error)
  | .ok witness => .ok (
      witness.tables.map (·.length), constraintsHold witness, channelsBalanced witness)

example : emptyDynamicResult = .ok ([0, 0, 256], true, true) := by native_decide

/-- Fixed inventories retain the exporter's positive-height requirement. -/
def emptyFixedRejected : Bool :=
  let component := bytesComponent (p := pBabybear)
  match hfixed : component.fixedColumns with
  | none => false
  | some fixed =>
    match validateGeneration {
      component with
      fixedColumns := some { fixed with height := 0 }
      Assumptions := component.circuit.Assumptions
      circuit_assumptions_of_assumptions := by intros; assumption
      fixed_width_le_input := by
        have h := component.fixed_width_le_input
        rw [hfixed] at h
        exact h
    } {
      mode := .preallocated {
        rows := 0
        input := .ofFExprs #v[.const 0]
        input_valid := by rfl
        handlers := []
      }
      padding := { input := #[0, 0], minimumRows := 0 }
    } with
    | .error (.emptyFixed _) => true
    | _ => false

example : emptyFixedRejected = true := by native_decide

def invalidPublicInput : fieldTriple (F pBabybear) := (10, 42, 42)

def invalidRejected : Bool :=
  match FibonacciWitness.generate invalidPublicInput 20 with
  | .error _ => true
  | .ok _ => false

/-- A final state not reached within the configured fuel fails generation. -/
example : invalidRejected = true := by native_decide

def configErrors : List String :=
  let config := FibonacciWitness.config (p := pBabybear) 1000
  let ensemble := (fibonacciEnsemble (p := pBabybear)).ensemble
  [{ config with components := config.components.drop 1 },
    { config with components := config.components ++ config.components.take 1 },
    { config with components :=
      ("unknown", { mode := FibonacciWitness.fibMode, padding := { input := #[] } }) ::
        config.components }]
  |>.map fun (config : Config (F pBabybear)) => match config.align ensemble with
    | .error error => toString error
    | .ok _ => ""

/-- Generation metadata is looked up by component name; missing, duplicate, and unknown entries are rejected. -/
example : configErrors = [
    "component 'fibonacci' has no generation config",
    "component 'fibonacci' has multiple generation configs",
    "generation config names unknown component 'unknown'"] := by native_decide

def noData : ProverData (F pBabybear) := fun _ _ => #[]

def extractedFirstRow : Except String (Array (F pBabybear)) := do
  let program ← Backends.lower
    (fibonacciEnsemble (p := pBabybear))
    (FibonacciWitness.config (p := pBabybear) 1000)
    |>.mapError toString
  let some component := program.components[0]?
    | throw "extracted program has no Fibonacci component"
  component.completeRow #[1, 0, 0, 1] noData

/-- The typed extraction semantics execute the same row-local witness IR as the source circuit. -/
example : extractedFirstRow = .ok #[1, 0, 0, 1, 1] := by native_decide

end Air.Flat.WitnessGenerationTest
