# Reflect original CHART fields into the existing ordered compiler

This is a source contract, not another parser/compiler or an executed check.
Reuse the exact native protocol/natural_cell bodies at4e556c4ae6225d18fabf30bc7d3347a468749ebc
and the existing G6NaturalCellInverseRates/NaturalCellAffineCompiler/
G6NaturalCellOrderedCompiler pins in evidence/EXISTING-G6-ORDERED-CELL-REVIEW.json.
The checked generic bank layout is already integrated; the captured Code,
captured-field and aggregate ordered-emission relations are still required.
The unchanged NativeCellFormReflection source now has four selected hosted
complete-type/standard-axiom audits; its exact original-definition projection
and submitted-source hash were independently reconstructed. See
evidence/CELL-FORM-REFLECTION-HOSTED-REVIEW.json. This closes the generic
form-constructor correspondence at that hosted scope, not Rust refinement.

| Native field | Existing typed field | Required exact relation |
| --- | --- | --- |
| Node index V:i | AgeAtom.node v | Preserve the original vertex index through the captured Code |
| Fixed canonical RC1 rational Q:q | AgeAtom.fixed q | Preserve the exact rational value and raw request identity |
| AGE LT / LE / EQ | AgeComparison.strict / weak / equal | Keep left/right order; EQ emits forward weak row then reverse weak row |
| Population E:i | some e | One original edge occurrence, shared across every referring exposure |
| Population A | none | The SAME ancestral inverse-rate slot for every exposure |
| EXPOSURE younger/older | Exposure.younger/older | Duration is older minus younger, including fixed/node mixtures |
| LE:q / LT:q endpoint | RationalBound q false / true | The strictness Boolean is preserved |
| NONE endpoint | Option.none | Emit no endpoint row; do not replace saturation by a finite bound |
| COIN i interval | coins (decoded original hybrid i) | A supplied physical parent1/gamma convention is still required; no automatic LAW G identification |

Both implementations form a row for f REL g using coefficient f.coeff-g.coeff,
bound g.constant-f.constant and the original strictness flag. For a lower
exposure bound q, emit q*u REL duration; for an upper bound, emit
duration REL q*u. The positive inverse rate u is shared and later reconstructs
rho=1/u; it is not the physical rate itself. The original interval_div_iff/
interval_rate_iff facts need that positivity, already part of the complete
source-cell constraints. Bounds/fixed cuts may be negative; adding positivity
or a lower<=upper input filter would change the supplied cell semantics.
An inconsistent cell is handled by the finite solver, not silently repaired.

## Lists must match native record order

Use the native integer occurrence order, not an arbitrary complete Fintype list.

- Edges: Fin ne in increasing original EDGE ID.
- Taxa: Fin ntaxa in original LEAF ID. If X is generic, require the actual
  taxonOrder:X≃Fin ntaxa and map its inverse over that list.
- Populations: the SAME edge-ID list mapped to some, followed by ONE none.
- Hybrids: original HYBRID ID order, mapped through idOrder.symm then decodedIDs;
  reuse that exact list in both open coin bounds and the extra coin-interval block.
- Chronology/exposures: Fin c_count / Fin x_count in original record order.
  Equal or repeated row VALUES remain repeated; do not deduplicate IDs or rows.

The explicit taxon order affects emitted ROW order even though it does not
change the bank-coordinate layout. The original hybrid-ID order affects both
columns and all three hybrid row blocks; enumerating the hybrid subtype by
vertex number can reorder them. For literal Code (Fin ntaxa) (Fin nh), both
original label orders can be identities when the captured-array relation proves
that choice. No additional Rust API is needed.

The aggregate target is
`decodeRows D (GParity.Chart.emitRows reflectedInput) =
compileCellList N layout ... chronology exposures coins`, using the EXACT
complete occurrence lists above, the reflected fields and row dimension D.
The original Chart.emitRows assigns unit bookkeeping vectors after all eight
blocks. encodeRow instead starts with empty weights. Compare decoded affine
semantics (and prove coefficient lengths), not complete wire Row equality
including those bookkeeping vectors. decodeRows preserves every ordered row
and ignores internal weights. The externally supplied Farkas multiplier vector
is separate and must preserve its full length and duplicate-row positions.
The Rust/native-to-Chart relation and this aggregate equality remain unproved;
the four checked primitive correspondences do not assert them. Only then use
compileCellList_toFinset for hemit. The original
positive wire check retains exact witness/row dimensions. Farkas also requires
the complete multiplier length and original duplicate-row positions. Their conclusions concern that supplied
cell; source menu coverage, nonlinear readouts, physical origin and all-size
NO remain separate. Missing proof of captured fields/meaning/refinement stays UNKNOWN/unavailable;
declared absent endpoints remain valid NONE.
No new suite, native/CI execution, dispatch, key or writer admission follows.

## Preserve derived rational size

Original protocol.rs at4e556c4 bounds RAW request rational numerator/denominator
to256bits (rational, lines37-52). Exact row subtraction/scaling can exceed that
bound. For example, let a=2^129 and b=a-1: both denominators are valid inputs,
while 1/b-1/a=1/(a*b) has a258bit denominator. This is an arithmetic/source
deduction, not a newly executed fixture or test.

The original CHART checker recompiles and compares its whole canonical MATRIX
prefix (chart_prefix279-290; check426-428). It does NOT reparse derived matrix
entries as raw AFFINE input. Certificate WITNESS/WEIGHTS/EVAL vectors use
rational(token,false), not the256bit input restriction (parsed_vector379-382).
The entire certificate retains the4MiB frame bound (constant12; check392).
Preserve exact rationals and the original framing; do not round, truncate or
route this derived matrix through the raw AFFINE codec. A transport/resource
refusal supplies no source-level mathematical NO or native admission.

## Exact result binding and separate transport limits

The original checker recompiles the same captured chart and matches its full
canonical request/BANK/MATRIX/cap prefix before reading a decision. SAT binds
the complete dimension-sized assignment and row-sized EVAL vector, checks all
original rows AND the direct chart interpretation, and recomputes every EVAL.
UNSAT binds the complete row-sized multiplier vector, checks nonnegativity,
zero combined coefficients and the original negative-bound/positive-strict
condition, then recomputes BOUND/STRICT. Its later nonzero strict-weight test
agrees with positivity because the earlier checker already rejected negatives.
UNKNOWN is not accepted as a certificate. These are source comparisons, not
native execution/refinement or source/readout admission.

The4MiB certificate bound is enforced by protocol::check. CHART execute356-370
has no final output-length gate; LAW's separate gate326-330 must not be assumed
to protect CHART. No overflowing execution was run or established here. Keep
the exact original resource/refusal outcome; do not infer successful bounded
production from the checker limit or the projected-row cap.

A conservative SOURCE/ARITHMETIC bound does cover the raw request plus original
compiled matrix prefix: each original coefficient is0,+/-1 or +/-one input
endpoint; a bound is0/1, an input rational or a difference of two fixed cuts.
Input256bit rationals give coefficient tokens<=514 ASCII characters using the
loose decimal_digits<=bit_count bound. Fixed-cut differences have numerator
<=513bits/denominator<=512bits, hence tokens<=1027characters. With32columns,
128rows,65536request bytes and4096fixed-prefix allowance, the total is at most
2,311,040bytes, below4MiB. This is an UNFORMALIZED deduction from the original
eight row blocks, NOT a Lean theorem, executed experiment or bound on projected
weights, the chosen witness, EVAL vector or final certificate.

The unchanged unified runtime and MCP request_json envelope each admit only
262144 UTF8 bytes, including literal JSON escaping and fields. The bridge's
runtime-result-file cap is8MiB. None overrides the direct RC1 request65536/
certificate4MiB limits, and canonical native_bridge still accepts only AFFINE
and LAW. Larger direct results do not become usable check requests by naming
the outer task. The exact source pins/call sites and remaining boundaries are
recorded in evidence/EXISTING-G6-ORDERED-CELL-REVIEW.json under
native_request_matrix_certificate_binding. No runtime/API/whitelist or writer
admission was changed.
