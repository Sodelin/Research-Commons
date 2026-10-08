# Exact primitive library/probe contract

Contributor/publisher: CLOUD-GMP-INTERVAL-SOL-2354Z.
Status: IMPLEMENTED; ACTUAL BUILD AND FINITE DIFFERENTIAL PASS,
8 October 2026; independent source review pending.

`certified_forward_gmp::RationalInterval` stores canonical exact `mpq_class`
closed endpoints `lo` and `hi`. It rejects reversed endpoints. It exposes
point/scalar casting, addition, subtraction, negation, four-product extrema,
nonzero scalar division, width, containment, intersection, signed-endpoint
dyadic floor/ceiling and unit meet. A disjoint unit meet refuses through the
same reversed-interval constructor, matching Python.

`exp_neg(ForwardInput x, ForwardInput bits)` distinguishes GMP integer,
rational and nonexact Python-type tags. It first refuses noninteger/nonrational
x, then checks negative x and integer precision 8..192, before either shortcut.
Bool/float/string tags are not silently coerced. Valid computation uses GMP
rationals only and reproduces each source dyadic/unit rounding stage.

The streaming `interval_probe` reads whitespace-separated commands and writes
one JSON record per line. Interval commands use integer or n/d text; exponential
commands use typed `i:`, `q:`, `b:`, `f:` or `s:` tokens. Results include canonical
`lower`, `upper`, `width`, or an exact Boolean/rational result. Refusals include
their source exception class/message. Parsing errors are marked as parser
phase and are separate from the forward primitive's contract.

Probe resource limits: at most 65,536 bytes per input line and 8,192 characters
per numeric payload (excluding `i:`/`q:` type tags); dyadic shifts at most
65,536. These are transport/parser
limits, not reduced-rational bit limits inside interval/`exp_neg`. The direct
library accepts arbitrary-size valid GMP rationals; its exponential precision
and Taylor cap are exactly the source's 8..192 and512. Execution budgets are
external to the primitive and recorded with actual tests.

Scope ends at these primitives. No full330-feature, nine-parameter inverse,
data fit, likelihood, optimizer, confidence or biological readout result follows.

Probe operations: `point`; `add`, `sub`, `mul`, `intersects` with two intervals;
`neg`, `width`, `unit` with one interval; `div`, `contains`, `add_scalar`, `radd`,
`sub_scalar`, `rsub`, `mul_scalar`, `rmul` with one interval and a scalar;
`dyadic` with one interval and integer precision; and `exp` with two typed
tokens. Endpoints/scalars admit optional-minus decimal integers and n/d with
positive decimal denominator (no leading denominator zero). Primitive refusals
carry `phase: primitive`; transport refusals carry `phase: parser`. Parsing
must finish before the forward primitive is called, so malformed transport
tokens are outside the source primitive's refusal-order comparison.

Python's LRU cache is a performance detail; this backend does not add a cache.
Exact deterministic results and source mathematical bounds are unchanged.
