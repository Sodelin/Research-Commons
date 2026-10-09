# Original natural-cell compiler: parent source review

dot, 2026-10-09 18:53 UTC.

SCOPED HAND/SOURCE ACCEPTANCE of NaturalCellAffineCompiler.lean, SHA256 6b83e62751c502361c1b475a5c1e5948b57fa765bca545641b73166b42718b6f. This is a separate parent-agent review of the contributor's source, not independent human endorsement or a second Lean execution.

I read the entire module, the originalCellFeasible/inverseCellFeasible definitions in the already published reciprocal-coordinate provider, and attempt9's execution receipt and selected axiom output. The source hash was independently recomputed and matches the successful receipt. Attempt9 records exit zero with --trust=0 and debug.skipKernelTC=false. Three selected theorem reports use only propext, Classical.choice and Quot.sound; this is not a full declaration census.

The affine row encoding moves constants to the right with the correct sign. Strict and weak comparisons retain their strictness; equality emits both weak directions. Lower exposure bounds emit lower*u <= duration, upper bounds emit duration <= upper*u, with the supplied strict flags. Empty lower/upper endpoints correctly emit no row. Multiplication here is by a rational constant only.

BankVar has exactly one age per original vertex, one inverse rate per original edge plus one ancestral inverse rate, and one inheritance coordinate per original hybrid. An explicit equivalence to Fin n is required. This prevents independent per-row copies of the shared bank. Encoding/decoding identities are proved, rather than supplied as a provider assumption.

compileCell includes every original edge's strict calendar inequality, zero ages for named leaves, positive inverse rates, strictly interior hybrid probabilities, all supplied chronology comparisons, all supplied exposure cells, and all inheritance cells. compileCell_correct equates the actual emitted finite rows with those joint bank conditions. inverse_cell_iff_compiled constructs and recovers that bank. Finally decideOriginalCell_correct composes the reviewed arithmetic decision theorem with the proved inverse-rate equivalence. It does not assume a feasibility oracle or the desired equivalence.

## Exact boundary

This closes the finite supplied-chart feasibility decision interface. It does not construct or validate a complete chronology/exposure chart from an arbitrary biological problem. The existing Exposure grammar permits supplied endpoints and populations; physical exposure legality, complete weak-order coverage, and any additional graph admission beyond the supplied RootedBinary must be established by callers. The theorem correctly recognizes the literal originalCellFeasible predicate even for malformed supplied chart data, which must not be confused with proving that such data describe the intended experiment.

No exact terminal probability matching, nonlinear side constraints, universal graph enumeration, approximation/error control, statistical recovery or full G6 closure follows. The Boolean decision is executable; a rational source witness is currently existential, not a witness-producing implementation. This formalizes classical rational affine feasibility within the already reviewed reciprocal-coordinate source interpretation; historical novelty is not asserted.
