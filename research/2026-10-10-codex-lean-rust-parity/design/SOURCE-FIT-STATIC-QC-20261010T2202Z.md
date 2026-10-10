# Supplied-fit bank and frontend: static integration review

Contributor: `/root/solver_design`; 10 October 2026, 22:02 UTC.
Evidence class: independent source review, **no compiler, native solver, test,
old compiler or backend execution**. Result: PASS for the exact captured bank
and frontend version; execution and any later readout remain separate gates.
The [machine capture](SOURCE-FIT-STATIC-QC-20261010T2202Z.json) records source
hashes and preserves the frontend under its evidence directory.

The new consumer checks one supplied rational assignment against every supplied
sparse equation, then constructs one symbolic physical bank. This repairs a real
representation gap between the inherited fitter and rational Calendar DTO: the
inverse rate `duration / (-log(x))` remains symbolic. Caller-supplied equations
are not authenticated as the observation equations of the given source.

| Reviewed component | Exact source SHA256 |
| --- | --- |
| [Bank](../rust/src/source_fit_bank.rs) | `e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a` |
| Frontend DTO and bind | `f70759172deaf6944b946bbe01a198f8f98ace82ee1ae5033c3dd720232dc8a0` |
| Frontend executable source | `64fef430d8584ceb992d547a46dfa71e6ca80505fee3b854375d82d4381badbe` |

The bank preserves original edge occurrences and one shared assignment across
rows. It converts old `g=P(parent0)` to original `gamma=1-g=P(parent1)` without
complementing forced occurrence bits. Its height calendar and positive-duration
relations agree with the inherited fitter. Each active interval uses the same
edge atom `x^(delta/duration)`. Fractional powers retain an exact unique-positive-
root constraint; integer powers can be evaluated rationally. No logarithm,
algebraic root or cut coordinate is rounded into the rational Calendar request.
The temporary unit-rate calendar is used for agenda production only; its proxy
physical bindings are discarded.

Two review findings were corrected before this capture. Decimal numerator and
denominator bit lengths are now checked against the existing absolute 65536-bit
bound **before** `Rational::new` performs gcd normalization. Bank internal errors
and file/read execution failures now have separate statuses from invalid input.
The frontend bounds raw requests to 64 KiB, rejects unknown and duplicate DTO
fields, enforces exact integer/array and canonical sparse-rational input, and
uses the inherited Context validation before source allocation. Successful bank
serialization binds the complete normalized semantic request stored privately
inside the bank. The incoming DTO schema and normalized bank schema are distinct
representations; raw-byte provenance is an additional wrapper responsibility.

`check` reproduces the canonical result and compares every byte. It is a replay
checker, including for operational UNKNOWN or UNSUPPORTED responses, not an
independent arithmetic or exhaustion proof. Both successful and unsuccessful
bank responses keep source admission, observation-fit provenance, timed readout,
certificate validity and full-solver verification false. Satisfying a zero
equation cannot promote any of those claims.

The inherited `actual_population_coefficients` theorem evaluates survival at
`exp(-pairRate*t)`. The native ordered merger recurrence includes its factor
`1/2`; summing all ordered destination fibres gives the older compiler's
unordered-pair rate-one convention. There is no additional rate or probability
normalization in this connection. The accepted finite original-population and
word comparisons support their literal cases; they do not establish a universal
native refinement.

The next readout must explicitly request completed ROOTED_UNRANKED genealogy,
sum full ordered-state fibres, substitute one original-gamma bank, combine equal
rational edge exponents, and only then demand integral surviving exponents.
The global numeric embedding must be inverted to recover local copy names before
comparison with the old string-tree convention. The saved large/permuted labels
are a useful challenge. Surviving fractional exponents or used inactive/ancestral
coordinates must remain unsupported. Gamma specialization for forced controls
can compare the register-forgetting genealogy marginal; it does not preserve the
original latent-register distribution, which is drawn naturally once. A
label-forgetting randomized mixture is likewise distinct from the master
labelled-program observation law.

The bank's five controls and frontend's three controls are authored source at
this snapshot, not executed results. The old saved-witness Fraction capture is
attributed reference arithmetic only. The later observer, frontend hook, native
build, source-observation equation generator and timed-history carrier are not
accepted by this note. Frozen maps and accepted artifacts were not edited.
