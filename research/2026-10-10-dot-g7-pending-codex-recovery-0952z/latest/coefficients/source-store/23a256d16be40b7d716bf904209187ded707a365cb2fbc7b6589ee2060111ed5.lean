import G7EffectiveFullEpochCoefficients

/-! Explicit owned declaration audit for the frozen executable coefficient chain.
The semantic Real/MvPolynomial interpreters are intentionally noncomputable;
only standard proof axioms are permitted. Code generation is checked separately. -/

#print axioms GProgram.G7.EffectiveSourceEnumeration.boolEnumeration
#print axioms GProgram.G7.EffectiveSourceEnumeration.optionEnumeration
#print axioms GProgram.G7.EffectiveSourceEnumeration.treeCodeEnumeration
#print axioms GProgram.G7.EffectiveSourceEnumeration.wellLabelledDecidable
#print axioms GProgram.G7.EffectiveSourceEnumeration.decodeAdmissibleTree
#print axioms GProgram.G7.EffectiveSourceEnumeration.decodeAdmissibleTree_surjective
#print axioms GProgram.G7.EffectiveSourceEnumeration.treeEnumeration
#print axioms GProgram.G7.EffectiveSourceEnumeration.locationEnumeration
#print axioms GProgram.G7.EffectiveSourceEnumeration.snapshotEncoding
#print axioms GProgram.G7.EffectiveSourceEnumeration.snapshotDecidableEq
#print axioms GProgram.G7.EffectiveSourceEnumeration.snapshotEnumeration
#print axioms GProgram.G7.EffectiveSourceEnumeration.decode
#print axioms GProgram.G7.EffectiveSourceEnumeration.decode_eq
#print axioms GProgram.G7.EffectiveSourceEnumeration.forestValidDecidable
#print axioms GProgram.G7.EffectiveSourceEnumeration.directedReachDecidable
#print axioms GProgram.G7.EffectiveSourceEnumeration.descendsDecidable
#print axioms GProgram.G7.EffectiveSourceEnumeration.sourceValidDecidable
#print axioms GProgram.G7.EffectiveSourceEnumeration.codeEnumeration
#print axioms GProgram.G7.EffectiveSourceEnumeration.view
#print axioms GProgram.G7.EffectiveSourceEnumeration.view_eq
#print axioms GProgram.G7.EffectiveSourceEnumeration.viewDecidableEq
#print axioms GProgram.G7.EffectiveSourceEnumeration.project
#print axioms GProgram.G7.EffectiveSourceEnumeration.selectedEnumeration
#print axioms GProgram.G7.EffectiveSourceEnumeration.enumeratedExistsDecidable
#print axioms GProgram.G7.EffectiveSourceEnumeration.findRepresentative
#print axioms GProgram.G7.EffectiveSourceEnumeration.findRepresentative_view
#print axioms GProgram.G7.EffectiveSourceEnumeration.project_findRepresentative
#print axioms GProgram.G7.EffectivePopulationCoefficients.sourceState
#print axioms GProgram.G7.EffectivePopulationCoefficients.place
#print axioms GProgram.G7.EffectivePopulationCoefficients.encode
#print axioms GProgram.G7.EffectivePopulationCoefficients.encodeActual
#print axioms GProgram.G7.EffectivePopulationCoefficients.choiceEnumeration
#print axioms GProgram.G7.EffectivePopulationCoefficients.merger
#print axioms GProgram.G7.EffectivePopulationCoefficients.merger_eq
#print axioms GProgram.G7.EffectivePopulationCoefficients.coefficients
#print axioms GProgram.G7.EffectivePopulationCoefficients.enumeration_perm
#print axioms GProgram.G7.EffectivePopulationCoefficients.coefficients_perm_kernelExpr
#print axioms GProgram.G7.EffectivePopulationCoefficients.coefficients_polynomial
#print axioms GProgram.G7.EffectivePopulationCoefficients.actual_population_coefficients
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.single
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.product
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.embedExpr
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.polynomial
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.eval_polynomial
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_nil
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_single
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_append
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_product
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_flatMap
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_enumerate
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_embedExpr
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.populationSelected
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.populationSelected_actual
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.restrictGenealogy
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.panelState
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.panel
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.lift
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.join
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.index
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.joinSelected
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.panel_eq
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.joinSelected_eq
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.fullCoefficients
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.fullCoefficients_actual
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.epochCoefficients
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.actual_full_epoch_coefficients

-- Explicit coverage of proof-only executable/legacy adapters added in repair.
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_cons
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.value_product_row
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.restrictGenealogy_eq
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.sourceState_eq
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.place_eq
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.project_eq
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.panelState_eq
#print axioms GProgram.G7.EffectiveFullEpochCoefficients.index_eq
