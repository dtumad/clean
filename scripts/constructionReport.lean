import Clean.Utils.Test.TestConstruction

open Examples.Construction TestConstruction

#check @FlatOperation.witgen_eq_dynamicWitnesses
#check @FlatOperation.witgen_witnessOperationsOnly
#check @Circuit.witgen_usesLocalWitnesses
#check @Air.Flat.Component.buildRow_constraintsHold
#check @Air.Flat.Component.buildRow_spec_requirements
#check @Air.Flat.Table.buildHinted_constraints
#check @Air.Flat.Table.buildHinted_interactions
#check @memory_row_valid
#check @memory_table_valid
#check @boolean_row_valid
#check @boolean_table_valid
#check @checkRead_iff
#check @checkChoice_iff
#check @memory_fixture_valid
#check @mixed_fixture_valid
#check @empty_fixture_valid
#check @readRow_reference
#check @data_needs_agreement
#check @hint_needs_agreement

#print ValidAddress
#print ReadSpec
#print hintValue

#print axioms FlatOperation.witgen_eq_dynamicWitnesses
#print axioms FlatOperation.witgen_witnessOperationsOnly
#print axioms Circuit.witgen_usesLocalWitnesses
#print axioms Air.Flat.Component.buildRow_constraintsHold
#print axioms Air.Flat.Component.buildRow_spec_requirements
#print axioms Air.Flat.Table.buildHinted_constraints
#print axioms Air.Flat.Table.buildHinted_interactions
#print axioms memory_computable
#print axioms memory_row_valid
#print axioms memory_table_valid
#print axioms boolean_computable
#print axioms boolean_row_valid
#print axioms boolean_table_valid
#print axioms checkRead_iff
#print axioms checkChoice_iff
#print axioms memory_fixture_valid
#print axioms mixed_fixture_valid
#print axioms empty_fixture_valid
#print axioms readRow_reference
#print axioms data_needs_agreement
#print axioms hint_needs_agreement
