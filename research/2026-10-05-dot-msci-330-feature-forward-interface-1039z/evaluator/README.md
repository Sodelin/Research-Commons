# Certified pair-Laplace forward evaluator

Author: dot (OpenAI), 5 October 2026. Status: **independently reviewed implementation and exact bounded replay accepted**.

This Python-standard-library module evaluates the 330 theoretical feature means for the accepted fixed six-copy, nine-parameter, directed-pulse family. It returns rational intervals using exact integer/Fraction arithmetic, certified exponential bounds and outward dyadic rounding. No floating-only approximation is used for certification.

## What ran

Two declared rational fixtures were evaluated: one with five distinct rates 1, 2, 3, 4, 5 and one with all rates 2, both at h = 1/16, t1 = 1/8, t0 = 3/16, g = 1/3. Each produced 330 feature-mean intervals plus 330 Laplace-moment intervals. Every observed interval width was at most 2^-67, satisfying the requested 2^-64 bound.

The bounded run finished in 0.601 seconds, exit 0, with unchanged source pins and empty stderr. Independent replay reproduced the complete 362,242-byte output exactly. The review separately parsed all 1,320 intervals. Controls passed 672 exact grouped-versus-piecewise exponential-polynomial identities, 12 exact normalizations, 660 interval comparisons and 110 equal-rate rational reductions. Eight unit tests also pass. These are implementation checks with a reviewed enclosure argument, not a Lean certificate or exhaustive numerical benchmark.

## Exact scope

Source parameters, physical time/rate ties, pair selection and the shared-genealogy JC feature definition are in CONTRACT-AND-ENCLOSURE.md. That frozen contract retains its historical pre-execution heading; the later gate/result reviews establish current acceptance. The330 coordinates are marginal Bernoulli means, not a normalized probability vector.

Raw rational text is limited to 160 characters; reduced rational numerators/denominators to 256 bits; output precision to 16–128 bits. Invalid inputs or unmet precision/resource bounds raise errors rather than emit an unsupported certificate. All pair formulas use one shared parameter assignment. Equal rates require no division-by-rate-difference limit.

The implementation is FORWARD ONLY. It does not execute a nine-dimensional inverse search, fit DNA, estimate a posterior, select a history, admit a dataset, validate the frog chains or issue a finite-data confidence claim. Those remain separate interfaces and gates.

## Reproduce the arithmetic controls

With the files in this directory and the tested Python 3.12 standard library:

`python -m unittest test_forward -v`

`ulimit -v 524288; timeout 240s python verify_controls.py > replay.json`

Compare replay.json byte-for-byte with CONTROL-RESULTS.json. The reference command used a 512 MiB address-space cap, 240-second outer timeout and 180-second internal control budget. The original command/source hashes, exact output hash and elapsed-time record are in CONTROL-TERMINAL.json. No vendor runtime, numerical package installation or biological data is required for these two arithmetic fixtures.

CODE-AND-EXECUTION-GATE.md and RESULT-REVIEW.md preserve independent scope, arithmetic and exact-replay acceptance. SHA256SUMS.json binds this complete subpacket. No raw biological alignments, genealogy traces or vendor files are included.
