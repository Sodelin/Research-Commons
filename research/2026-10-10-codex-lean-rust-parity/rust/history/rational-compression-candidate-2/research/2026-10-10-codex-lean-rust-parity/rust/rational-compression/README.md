# Private exact rational compression

This additive crate ports the attributed exact Fraction first-pivot/first-free
elimination in [the saved review](../../design/review_g6_source_generators.py).
It preserves one mass and geometric-tail vector for a common family of supplied
rational survival atoms. Array indices remain original atom identities, including
when values repeat. Zero weights are removed; an all-zero family yields an empty
certificate. The supported cap is M=2,3,4.

The [reviewed contract](../notes/G6-RATIONAL-COMPRESSION-CONTRACT-2-20261010T1632Z.md)
specifies the exact request, canonical result, original-index certificate and
resource handling. Default limits are 64 original atoms, 8,192 cumulative matrix
cells and 4,096 rational bits. Domain validation precedes resource decisions.
Moment matrices are charged before coordinates are generated; every arithmetic
operand and result is checked against the explicit bit cap. Request/result frame
bounds are 64 KiB/4 MiB. Controlled runs also require process limits.

The private executable accepts stdin with no arguments or `solve`, or
`solve --request FILE`. `check --request FILE --certificate FILE` checks exact
mass/tail equations, original indices, positive weights and raw request binding
without running elimination. Solver exits are COMPRESSED=0, UNKNOWN=2, ERROR=1;
checker exits ACCEPT=0, REJECT=1. Canonical output uses sorted compact ASCII JSON
and one LF. UNKNOWN acceptance checks framing only. Producer work and resource
exhaustion are never certified by the checker.

The checker requires the exact fields for each result variant, so explicit null
extras are rejected. Before parsing certificate integers for gcd normalization,
it derives a conservative decimal-length bound from the requested rational-bit
budget, then checks exact numerator/denominator bits. It can reject a certificate
on its own resource bound; this does not prove the rational equations false.

The accepted Lean mathematical consumer is separate from JSON/parser/producer
refinement. This component does not construct a positive source network, identify
rational atoms with generally transcendental calendar survival values, or promote
source admission. It has no application command and changes no accepted runtime.
Build caches and the private ELF are stored outside the repository.
