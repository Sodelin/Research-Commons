# Independent source-fit rooted reference

This is a new consumer of the existing October 1 full-joint genealogy compiler,
not a new law engine. Static source and syntax inspection passed on October 10;
the scheduler must execute the checker before any independent-check flags are
accepted. No compiler, native producer, legacy compiler, or backend was executed
by this review.

The frozen checker is [source_fit_reference.py](source_fit_reference.py), SHA256
`0eedff2d9ab21514e3788ae5f9310e33bd57d8ce86e4cf038bb08520ccd99fc6`.
Its dependencies are:

| Source | SHA256 |
| --- | --- |
| [certificate_check.py](certificate_check.py) | `ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24` |
| [chart_check.py](chart_check.py) | `3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a` |
| [October 1 law_compiler.py](../../2026-10-01-g7-continuous-design/law_compiler.py) | `eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7` |

The prepared backend must contain SymPy **1.14.0** and mpmath **1.3.0**. These
version checks do not prove the interpreter or package runtime; the bounded
adapter records their observed paths and initializer digests separately.

The Python API is `verify_response(raw_request, raw_response, exit_code=None)`.
The CLI is `--request PATH --certificate PATH --exit-code CODE`; checker exit 0
means the reported verification succeeded, and exit 1 means it failed. Its JSON
schema is `source_fit_reference_check_v1`. For isolated execution, capture the
four authenticated byte buffers, register the base and chart modules, execute
the checker with its `__main__` guard disabled, call
`install_baseline(captured_original_bytes)`, then call `main()`. The captured
baseline must not be reread through a mutable provider path. The standalone
loader authenticates the same baseline bytes before loading it.

Input is the bounded `source_fit_request_v1` DTO, with at most four copied
labels, exact canonical rational survival/old-gamma values, original graph and
edge occurrence IDs, one COMMON or INDEPENDENT mechanism, and explicit limits.
Duplicate/unknown fields, noninteger counts, invalid dimensions and noncanonical
rationals are rejected. JSON `-0` has the existing semantic value zero. Algebraic
descriptors remain unsupported for independent evaluation.

For a natural, nonempty, ancestrally completed TABLE, the checker validates the
typed semantic request echo, scientific false gates, explicit natural program
and effective limits, and exact satisfaction of every supplied equation at one
shared assignment. It calls the pinned inherited full-joint compiler and
compares every coefficient of every rooted whole-edge polynomial, then every
rational probability and exact polynomial normalization. It retains the declared
copy-to-global-label embedding, including integer IDs above 2^53.

Only safe internally generated names reach the inherited symbolic compiler.
Hybrid names preserve the declared sorted hybrid ID order, incoming edges retain
their original occurrence order, and old `g` means probability of incoming 0.
The reference therefore compares the readout after original gamma is replaced
by `1 - g_old`. Caller vertex/copy strings never become symbolic expressions.

Successful TABLE verification sets `independent_all_coefficients_checked`,
`independent_probabilities_checked`, `supplied_trace_arithmetic_checked`, and
`baseline_called` to true. `provider_work_checked`,
`bank_metadata_independently_checked`, resource-exhaustion, source admission,
source/observation provenance, timed readout, evaluated full-Code law, universal
native refinement and full-solver claims stay false. Bank metadata and native
replay retain their separate checks. Satisfying a supplied trace does not prove
that it was generated from the stated source or observations.

UNKNOWN/UNSUPPORTED responses receive bounded framing and input-echo checks
only; operational error frames explicitly report that an input echo was not
checked. They publish no partial table or mathematical exclusion. Reference
execution failure must prevent a requested independent TABLE check from being
silently reported as a successful native-only result.

The first scheduled acceptance should reuse the three saved native tables and
compare their complete coefficients, then challenge a balanced coefficient
change, an input/bank swap, a probability-only change, type-confused fields and
status/exit mismatches. A separate four-copy request is the meaningful generic
extension; its native and inherited reference executions remain scheduler work.
