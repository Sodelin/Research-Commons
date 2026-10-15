# Bounded algebraic soundness controls

These controls challenge finite algebraic steps and semantic boundaries of the
exponential-expression theorem draft. They do not encode exponentiation, prove
Lindemann–Weierstrass, decide the unrestricted real-exponential theory, establish
source/compiler coverage, or close G3/G4.

The checked phone already contains Debian `libz3-4:arm64` version `4.13.3-1`.
Neither a Termux Z3 executable nor a Debian `z3` executable or `z3py` binding
was available. The small `ctypes` worker calls the existing native Z3 C API;
no package, service, container configuration or solver project was changed.
The [official C API documentation](https://z3prover.github.io/api/html/group__capi.html)
specifies the context lifecycle and `Z3_eval_smtlib2_string` interface used.
Each worker owns one config and one context, copies the returned string before
destroying the context, and exits. No solver state is shared between jobs.

`SOURCE-CONTEXT.json` pins retained Commons source documents that informed the
shared-parameter, strict-domain and bounded-outcome controls. Reuse concerns
those soundness distinctions; this is separate from the ongoing original-source
SMT project and does not launch its backend.

## Actual results

`results/20261015-run-02/RESULT.json` records **16/16 expected results**:
eight UNSAT results with retained Z3 proof terms and eight SAT results with
exact rational countermodels. All original jobs completed; no UNKNOWN or timeout occurred in that suite.
Each native solver job took approximately 0.42–0.53 seconds including container
startup. The native engine reported `4.13.3.0`, and its exact library hash and
read-back limits are in the receipt.

| Controls | Checked obligation |
|---|---|
| 01–03 | Polynomial coefficient convolution, equal-basis grouping and exponent-sum cancellation |
| 04 | Discarding algebraic constant shifts merges distinct polynomial exponent keys |
| 05–06 | A shared physical parameter differs from independent row refitting |
| 07–08 | Strict positivity excludes a boundary admitted by nonnegativity |
| 09–10, 13 | Point or constrained-surface equality does not certify ambient open-domain identity |
| 11–12 | The nonzero-denominator guard is necessary for partial division graphs |
| 14–16 | Robust threshold certificate arithmetic and the necessity of weakening slack |

The independent checker uses only Python's exact `Fraction` arithmetic to parse
the retained SAT model values and validate all eight countermodels. Its receipt
is `results/20261015-run-02/INDEPENDENT-MODEL-CHECK.json`.
It does not call Z3. UNSAT proof terms remain at the Z3 evidence tier: no
independent proof-kernel replay of those terms is claimed.

For the additional robustness certificate, controls 14–15 check the implications
assuming the supplied approximation bound `|rhat-r| <= delta/4`. They do not
establish that bound for an exponential expression. Control 16 independently
replays `delta=1, rhat=-1/2, r=-3/4`, showing why approximate positive classification
certifies the weakened predicate rather than unweakened `r >= 0`.

## Reproduction and bounds

Run from the theorem repository, with a **fresh** result path:

```sh
python3 -B verification/smt/run_checks.py --output verification/smt/results/my-fresh-run
python3 -B verification/smt/check_countermodels.py verification/smt/results/my-fresh-run/RESULT.json --output verification/smt/results/my-fresh-run/INDEPENDENT-MODEL-CHECK.json
```

Jobs run sequentially. Each native worker has a 3-second CPU limit, 512-MiB
address-space limit, 64-KiB limit per output file and disabled core files. The
whole container invocation has a 6-second wall limit plus CPU/file/core limits.
Every SMT input additionally requests a 2,000-ms timeout and 192-MiB Z3 memory
limit. Outer wall-time expiry kills the process group. Status parsing separates
`sat`, `unsat`, `unknown`, wall expiry, execution failure and malformed output.
Output files and receipts retain exact command argument vectors, input hashes,
tool source hashes and output hashes.

The initial probe applied the 512-MiB virtual-address cap to the Android launcher
itself and failed before loading Z3; `results/20261015-run-01/FAILURE.md` retains
that observed failure and the independent `/usr/bin/true` launcher control.
The corrected route applies the memory cap inside Debian before loading Z3;
the full route continues to have the outer CPU, wall and output limits.
This failed attempt is not counted as an SMT result.

## UNKNOWN and artifact diagnostic correction

Independent review found that the original parser classified any SMT error
diagnostic as `INVALID_SOLVER_OUTPUT`, even when a valid `unknown` result was
followed by an unavailable proof/model diagnostic. The corrected parser retains
`solver_status`, the full status list, artifact errors and process outcomes
separately. A clean-exit UNKNOWN plus an unavailable artifact remains `unknown`.
SAT/UNSAT with an artifact error becomes `ARTIFACT_FAILURE`, so it cannot count
as successful decision evidence. Nonzero exits, wall timeouts, multiple statuses
and non-artifact syntax errors remain separate failure classes, while any unique
solver status is retained. Raw stdout and stderr are preserved throughout.

`check_status_parser.py` checks 13 explicit parser regressions, including those
failure cases. These are labeled synthetic parser fixtures; they are not
represented as native solver outputs. It also reclassifies all 16 retained
run-02 output pairs and verifies that their outcomes are unchanged, without
executing those solver jobs again.

One additional native job was executed in the fresh directory
`results/20261015-native-unknown-01/`. The exact SMT input gives Z3 a resource
limit of one unit. Native Z3 returned `unknown` and
`(:reason-unknown "max. resource limit exceeded")`, with exit code 0 and empty
stderr. This is an actual observed UNKNOWN, and `usable_decision_evidence` is
false. Its expected UNKNOWN outcome is a harness control, not a mathematical
decision. The original run-02 records were not rewritten.

```sh
python3 -B verification/smt/run_checks.py --manifest verification/smt/unknown-control.json --output verification/smt/results/my-fresh-unknown-run
python3 -B verification/smt/check_status_parser.py --output verification/smt/results/my-fresh-unknown-run/PARSER-REGRESSION.json
```

## Finite-grid witness examples

Two additional tiny native controls in `grid-controls.json` challenge the
finite-grid witness lemma at specific low degrees. Control 18 asserts that a
real quadratic vanishes at `-1,0,1` while some coefficient is nonzero. Control 19
asserts that a real bilinear polynomial vanishes on all of `{0,1}²` while some
coefficient is nonzero. Both returned UNSAT with retained Z3 proof terms, exit
code 0 and no artifact errors under the same bounds. Exact sources, hashes,
commands and actual outputs are in `results/20261015-grid-controls-01/`.

These are fixed-degree examples. They do not prove the arbitrary-degree or
arbitrary-dimensional grid lemma, nor do they validate its exponential or
Lindemann–Weierstrass dependencies.

The native mathematical-control total across the three completed successful
result directories is **19 jobs: 10 UNSAT, 8 SAT and 1 UNKNOWN**. The earlier
launcher failure remains a separate failed probe and is not in that count.
The 13 synthetic parser fixtures and 16 historical-output replays are also
separate from the native-job count. No previous solver suite was rerun for
these two new controls.

```sh
python3 -B verification/smt/run_checks.py --manifest verification/smt/grid-controls.json --output verification/smt/results/my-fresh-grid-run
```
