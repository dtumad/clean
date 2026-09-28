import Clean.Utils.Test.TestConstructionEnsemble

open Examples.Construction TestConstruction

/-- Run the adoption example and print the actual generated physical rows. -/
def main : IO Unit := do
  IO.println "field=97; memory row width=2; Boolean row width=1"
  IO.println s!"memory-first={(readRow 0 (data:=memory)).map ZMod.val}"
  IO.println s!"memory-last={(readRow 2 (data:=memory)).map ZMod.val}"
  IO.println s!"changed-memory-first={(readRow 0 (data:=changedMemory)).map ZMod.val}"
  IO.println s!"mixed-hint-rows={mixedTable.table.map (·.map ZMod.val)}"
  TestConstruction.run
  TestConstructionEnsemble.run
