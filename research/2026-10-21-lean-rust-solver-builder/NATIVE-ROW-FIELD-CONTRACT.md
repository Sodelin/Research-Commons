# Reflect original CHART fields into the existing ordered compiler

This is a source contract, not another parser/compiler or an executed check.
Reuse the exact native protocol/natural_cell bodies at4e556c4ae6225d18fabf30bc7d3347a468749ebc
and the existing G6NaturalCellInverseRates/NaturalCellAffineCompiler/
G6NaturalCellOrderedCompiler pins in evidence/EXISTING-G6-ORDERED-CELL-REVIEW.json.
The checked generic bank layout is already integrated; the captured Code,
field reflection and actual ordered-emission relation are still required.

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

The target is equality between the reflected native coefficient/bound/strictness
LIST and encodeRows(compileCellList ... exact lists ... exact typed fields).
The cross-language reflection is an explicit remaining relation, not asserted
by this notation. Only then use compileCellList_toFinset for hemit. The original
positive wire check retains exact witness/row dimensions. Farkas also requires
the complete multiplier length and original duplicate-row positions. Their conclusions concern that supplied
cell; source menu coverage, nonlinear readouts, physical origin and all-size
NO remain separate. Missing proof of captured fields/meaning/refinement stays UNKNOWN/unavailable;
declared absent endpoints remain valid NONE.
No new suite, native/CI execution, dispatch, key or writer admission follows.
