# Source-admitted adaptive whole-policy instance

The complete inherited four-taxon/one-original-hybrid source image admits a
two-step policy whose second real action depends on the first exact response.
It preserves one original source/parameter assignment through the full history,
has PATH cost [2 calls, 2 configurations, 1 original site], and returns actual Q
on every reachable real-valued response. This is an executable G7 instance with
complete identity-based coverage, not general adaptive-policy synthesis.

Read `WHOLE-POLICY-SEMANTICS.md` for the exact source, history, legality and
target contracts. `ADAPTIVE-POLICY-CERTIFICATE.json` stores all nine joint source
rows with shared variables and the positive-factor target identities.
`verify_adaptive_certificate.py` checks them using only exact Python Fractions;
it trusts the separately accepted source-image census/surjection provider and
does not use a QE verdict. Five tampered certificates are rejected.

`execute_adaptive_policy.py` supplies the two actions and target, validates the
accumulated history, constructs an original source witness, and recompiles BOTH
observations under one assignment. Its current input encoding accepts rational
response vectors; the complete-real certificate covers irrational weights too.
Other input encodings and unsupported scientific admission return UNKNOWN.

Install the pinned versions in `requirements.txt`, then run:

    python3 verify_adaptive_certificate.py --tamper-controls
    python3 test_adaptive_policy.py
    python3 execute_adaptive_policy.py examples/complete-two-step.json --output result.json

The delivered replay contains all nine images under both common and independent
mechanisms, 18 actual shared-source recompilations, two different reachable
actions, explicit same-first-response/different-Q witnesses, and 11 negative
controls. The Wolfram 15.0.1 raw receipt separately returns True for all nine
real-domain legality/target checks. This receipt has SAME_BACKEND trust; the
Fraction identity checker supplies the narrower independent algebraic check.

The 546-source provider is unchanged from manifest
3c11ea185f573e6bf47d62a2dde96bd6215aa8eac4073b361f3571557793cbf1;
its full source-image certificate has SHA-256
2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8.
The source/compiler files are the unchanged reviewed base closure identified in
`BASE-SOURCE-BINDING.json`. Public primary hand contract: Sodelin/Research-Commons,
`research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md`.

The fixed interior one-call policy already wins this restricted source image.
This two-step result demonstrates full response-dependent execution rather than
a new mathematical theorem or a tighter call bound. No empirical fitting,
generic recursive CAD closure, Lean verification or global unknown-size
termination is claimed. The next decisive implementation obligation is generic
source-admitted adaptive selector assembly with complete reachable coverage;
bounded-case expansion is not a substitute for that gate.
