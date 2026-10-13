# Six-copy COMMON fixture handoff

The [source-pinned fixture](astra-common6-fixture-2240.json) fixes four taxa
`[A,B,C,D]`, directed pair `(A,B)` and level `k=1`. It supplies a balanced
seven-vertex, six-edge tree with an explicit taxon-to-leaf table. The full
padded row has six distinct external copy IDs:

| Native sample index | External copy ID | Taxon / native leaf ID |
| --- | --- | --- |
| 0 | `selected:B` | B / 1 |
| 1 | `selected:A1` | A / 0 |
| 2 | `baseline:A` | A / 0 |
| 3 | `baseline:B` | B / 1 |
| 4 | `baseline:C` | C / 2 |
| 5 | `baseline:D` | D / 3 |

This is a supplied bijection on copy IDs and an explicit taxon allocation,
never an inferred graph mapping. The original edge occurrences remain in their
listed order. The primary tree has no hybrid, so its parent-order check is
vacuous; the separately pinned existing parallel-edge example provides that
optional control. Its RC1 `G:0` weights `incoming[0]`, whereas the selected
source-bank adapter computes the complementary parent-one probability without
reordering edges or complementing forced bits.

The existing RC1 parser and `law::Request::validate` reject six copies; this
handoff does not claim an executable COMMON6 extension. The JSON includes a
literal candidate request in the inherited LAW grammar, with all three limits
kept at their inherited maxima. An isolated future profile must explicitly
authenticate its changes to the header sample cap, sample ordinal cap and
request validator. Budget exhaustion remains UNKNOWN.

The intended exercise computes the **complete six-copy joint rooted terminal
law** and its unrooted pushforward. All six IDs must remain present in every
terminal tree. The exact probability polynomials should sum to 1; evaluation
at the pinned strictly interior rational formal survivals should preserve
nonnegativity and mass 1. These are expected checks, not observed results.

Only after the complete joint computation, passively prune to sample indices
0 and 1 and suppress unary nodes. Every terminal tree maps to the single
unordered two-copy tree `(0,1)`, so its event probability is 1. The original
comb coefficient is `2^1/(2!·1!)=1`, and the exponent is `choose(1,2)=0`; the
normalized first moment is consequently 1. This fixture alone supplies no
nonzero annihilating certificate, target recovery or support bound. Dropping
baseline copies before computing the joint output is not this fixture's test.

The existing `ordinary_path_coefficients` contract already covers sizes through
64 and exact rational exponents `choose(h,2)`. Its six-root exponents are
`0,1,3,6,10,15`; the root-completion history denominator is 2700. The coefficient
routine may be reused with its original history multiplicities. Standalone
`forest::coordinate` labels are one-based, while LAW sample/tree IDs are
zero-based; no implicit label conversion is licensed.

`X:0,...,X:5` are formal survival variables. Their exact rational assignment is
separate from physical rate/calendar binding and source admission. The fixture
does not establish an unknown target's existence, a protected-source encoding,
certificate acquisition, parser-to-Lean refinement or universal native
correctness. The one empty-mask configuration is kept explicit; no correlation
or protected constraint is silently invented.

Only bounded source reads and hash comparisons were performed. No decoder was
implemented, no compiler or test ran, and no output table was generated. The
native lane owns any isolated COMMON6 implementation and guarded execution;
the Lean lane owns publication and remote readback.
