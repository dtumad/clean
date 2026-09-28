import Clean.Air.WitnessGeneration

/-! Compatibility regressions for the scheduler's canonical row interpreter. These are
interpreter tests; they do not certify the scheduler or its final data environment. -/

namespace TestSchedulerGenerator

abbrev Fp := ZMod 97
instance : Fact (Nat.Prime 97) := ⟨by decide⟩

def data : ProverData Fp := fun _ n => #[Vector.replicate n 11]
def hint : ProverHint Fp := fun _ n => #[Vector.replicate n 1]
def channel : Channel Fp field where
  name := "receipt"
  Guarantees _ _ := True

def table : Table Fp field where
  name := "memory"
  Contains _ _ := True

def program : Circuit Fp (Var field Fp) := do
  let value ← witness (Witgen.FExpr.dataGet "memory" 1 (.const 0) 0 : Witgen.FExpr Fp)
  assertZero (value - value)
  lookup table value
  let choice ← witness (Witgen.FExpr.hintGet "choice" 1 (.const 0) 0 : Witgen.FExpr Fp)
  channel.push (value + choice)
  return value + choice

theorem filtered_agrees :
    FlatOperation.witgen hint
      (FlatOperation.witnessOperationsOnly (program.operations 1).toFlat) #[7] (data := data) =
      program.witgen hint #[7] (data := data) :=
  FlatOperation.witgen_witnessOperationsOnly hint (program.operations 1).toFlat #[7]

def run : IO Unit := do
  let generated := program.witgen hint #[7] (data := data)
  unless generated == #[7, 11, 1] do
    throw <| IO.userError "canonical generation lost input, data, or hint"
  let filtered := FlatOperation.witgen hint
    (FlatOperation.witnessOperationsOnly (program.operations 1).toFlat) #[7] (data := data)
  unless filtered == generated do
    throw <| IO.userError "filtering changed generated cells"
  unless program.witgen hint #[7] == #[7, 0, 1] do
    throw <| IO.userError "legacy empty-data call changed"
  IO.println "PASS: scheduler adapter data, hints, input prefix, filtering, and default-data regressions"

#eval run

end TestSchedulerGenerator
