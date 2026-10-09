# Source-faithful bounded G4 computation

Contributor: Codex G4 computation lane, 9 October 2026. New authored execution;
independent validation belongs to this bridge packet's validation lane. No
Lean verification, QE, global source forcing or historical novelty claim.
MASTER-CLOSURE-STANDARD-20260930 accepted at its original quantifiers.

The reusable module is
[`g4_certificates.py`](../../../applications/genealogy-compatibility-workbench/genealogy_workbench/g4_certificates.py).
It consumes request-bound exact certificates and computes complete capped
private-word kernels in BOTH modes from one physical parameter bank. Existing
provider scripts are unchanged. It is a computation API, not an original
observation adapter or a new general recognition solver.

## Master implication declared before computation

Original G4 fixes one admitted positive target and asks for effective finite
forcing against **all** unknown-size positive rivals in its original legal
menu, or exact later-distinguishable rivals after every finite prefix of that
one fixed target. See the [master statement](../../2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md).

The published cone replay establishes only the bounded arity-12 obstruction
to the specified global linear-log guard. The new local separator establishes
the effective **conditional local** exclusion in the reviewed provider for
the rational target subclass. Neither proves that arbitrary exact fitting
rivals have one persistent body near the target and only weak extras.
That global all-rival localization remains the decisive missing implication.
Whole-forest equality, chronology, original menu coverage, all cores and
shared registers remain part of the original problem.

## Reproduction

Run from the Research-Commons root. Replay has no external services and no
SciPy, mpmath or SymPy dependency; Python 3.10+ is sufficient.

```bash
export PYTHONPATH=applications/genealogy-compatibility-workbench
python3 -m genealogy_workbench.g4_certificates check-cone research/2026-10-09-codex-conditional-bridge-1630z/g4/cone-request.json research/2026-10-09-codex-conditional-bridge-1630z/g4/cone-certificate.json
python3 -m genealogy_workbench.g4_certificates check-separator research/2026-10-09-codex-conditional-bridge-1630z/g4/local-request.json research/2026-10-09-codex-conditional-bridge-1630z/g4/local-certificate.json
python3 -m genealogy_workbench.g4_certificates check-word research/2026-10-09-codex-conditional-bridge-1630z/g4/fair-target-request.json research/2026-10-09-codex-conditional-bridge-1630z/g4/fair-target-certificate.json
python3 research/2026-10-09-codex-conditional-bridge-1630z/g4/run_controls.py --output /tmp/g4-controls-replay
```

Results: `CERTIFIED_BOUNDED_LOG_CONE`,
`CERTIFIED_CONDITIONAL_LOCAL_WEAK_EXCLUSION`,
`CERTIFIED_SUPPLIED_WORD_KERNEL`, and **87 exact/adversarial/source-history
controls PASS**. The last command writes fresh evidence to the specified
scratch directory; the check commands only read published files. CLI refusal exits 2. Saved JSONs record
exact fractions rather than rounded tolerances.

To regenerate proposals and reproduce both frozen provider executions:

```bash
export PYTHONPATH=applications/genealogy-compatibility-workbench
python3 research/2026-10-09-codex-conditional-bridge-1630z/g4/build_evidence.py --output /tmp/g4-construction-replay
python3 -m genealogy_workbench.g4_certificates search-separator research/2026-10-09-codex-conditional-bridge-1630z/g4/local-request.json --max-arity 10 --max-degree 30
```

Construction used existing mpmath 1.3.0 and SciPy 1.17.0. Its inverse, weights
and linear-program answers are proposals only. Acceptance rechecks exact
integers/Fractions. Search is bounded and may return `UNKNOWN`; it is a
sufficient Bernstein search for **rational** `(q0,p0,c)`, not the provider's
complete RCF algorithm for all effectively real-algebraic targets. That
general algebraic backend remains unimplemented. No new toolchain was installed.
The scripts retain their historical packet-directory default. Use the
documented `--output` paths for replays so accepted evidence and its manifest
remain untouched.

## Exact cone replay and preserved failure

The frozen corrected checker at
[`cf6c1b32`](../../2026-10-09-dot-reviewed-guard-boundaries-1615z/g4/INDEPENDENT-CONSTRUCTION-REVIEW.md)
exited 0, and its output was byte-identical to the published
`biased-cone-12-certificate.json`. The preserved pre-generator-fix checker
exited 1 at its inverse-residual assertion. Both stdout/stderr and exit
statuses are retained in `frozen-provider-replay.json` and the corresponding
`.stdout`/`.stderr` files. That failure is not accepted evidence.

`cone-certificate.json` supplies the rational inverse and rational approximate
weights explicitly. The new standalone consumer regenerates the eleven
exact log-enclosed columns and target from `cone-request.json`, verifies
`||I-BA||∞<1`, bounds the Neumann-series solution error, and proves all exact
weights positive. Its full rational residual/error bounds agree with the
published checker. Each certificate includes the SHA256 of its complete
canonical request; changed target, clock, precision, nodes or parameters
invalidate the binding. Zeroed inverse entries and negative proposed weights
are rejected. A new request can be checked only by its own fresh exact evidence.

The logs use integer directed rounding, powers-of-two range reduction and
120 atanh terms with the published rigorous tail bound. No floating result
is trusted. Positive conic weights are **not** cell multiplicities, admitted
mixture probabilities or an actual rival word. This replay excludes only
the published nonzero global linear-log architecture through arity twelve;
it does not exclude the target's finite forcing.

## Executed rational local separator

The later [reviewed local provider](../../2026-10-09-dot-local-forcing-and-coverage-review-1627z/g4-local/LOCAL-WEAK-INSERTION-EXCLUSION.md)
and its [mandatory independent review](../../2026-10-09-dot-local-forcing-and-coverage-review-1627z/g4-local/INDEPENDENT-CONSTRUCTION-REVIEW.md)
were read after publication at `146b5afa`. Its target is biased and its
observed COMMON clock is essential. The rational demonstration uses
`q0=1/2`, `p0=g0(1-g0)=3/16`, `c=2/5`, hence `1<=y<=Q=5/2`.

The first bounded proposal succeeded at **N=4, Bernstein degree 2**. Exact
coefficients `(a2,a3,a4)` are:

```text
3275937511/238250000
-184771384549/14295000000
42544643/10000000
```

The checker proves both target derivatives vanish exactly and proves
`Σ a_n D_n(y) >= 297812501/297812500 > 0` over the **entire** closed interval
by positive Bernstein coefficients. This is not a mesh or a global sign
claim for `Σ a_n log R_n` over all cells. The latter is the different
architecture already obstructed by the cone result.

The checker also derives explicit exact positive neighbourhood constants.
Conservative rounded descriptions are `epsilon≈2.83887e-5` and
`eta≈1.04365e-11`. Acceptance uses the fractions in `local-replay.json`.
The body neighbourhood is the equivalent `(p,y=1/q)` chart:
`max(|p-p0|,|y-y0|)<=eta`; every other cell must have
`0<w=p(y-1)<=epsilon`. One shared observed clock and exact normalized
diagonals through N are additional premises. Ordinary pad placement is
not identified. `all_rival_neighbourhood_verified` stays false.

[`LOCAL-CONSTANTS.md`](LOCAL-CONSTANTS.md) supplies the theorem-to-code hand
derivation. Certificate replay recomputes every constant from the target,
separator and positive Bernstein bound. It does not accept supplied
booleans, guessed eta/epsilon, approximate endpoint zero or a mesh.

`inspect_local_rival` checks those physical premises on **one supplied**
strict rational-parameter private word. The rare-coin extra has `q=9/10`,
`g=10^-15`; the weak-duration extra has `q=1-10^-15`, `g=1/2`. Both fit the
uniform weak criterion without a coin floor. Pads keep their original
same-source COMMON clock exactly `2/5`. The inspector confirms the actual
neighbourhood and the exact diagonal mismatch. A second exact control
retunes rational `(p,y)` of the body so pair and triple diagonals match;
its algebraic coin solves `g²-g+p=0` with the unique root in `(0,1/2)`.
Its body stays in the certified neighbourhood, and its arity-four rational
residual is nonzero. This is a source-admitted diagonal control, not a
complete forest collision or fixed-target all-prefix family.

## Complete forest and chronology controls

The API reuses the frozen public current-root `vendor/forest_algebra.py`.
It computes every labelled forest coordinate through cap four, including
zero entries, in both COMMON and INDEPENDENT modes, from **one** bank and
one literal chronological factor list. Original copy/taxon/arm occurrence
IDs and repeated parameter ties remain explicit. Strict positivity, root
count, IDs and all bank references are checked. No independently fitted
mode banks are accepted.

Five supplied word fixtures cover fair and biased targets, a changed
chronological placement, rare coins/weak durations and eight weak cells.
Every row through cap four in both mechanisms agrees with a direct
historical-tree merger oracle that does not call production token grafting.
It shares the classical Kingman pure-death identity, so this is an
independent implementation comparison, not a second mathematical proof.
The control detects altered chronology, floats, duplicate original copy
IDs, aliased arm occurrences, unused bank parameters and missing coordinates.

The two fair words `E(4/5)B(1/2,1/2,1/2)E(3/5)` and
`E(3/5)B(1/2,1/2,1/2)E(4/5)` share every no-merger diagonal in BOTH modes.
Their complete forest C,H values differ. `controls.json` preserves that
exact chronology witness, so neither diagonal equality nor a positive
finite kernel is promoted to full source equivalence.

## BOTH-menu adapter and remaining obligations

The accepted calibrated original-taxon decoder, tree-edge reduction,
private paired guard and their mandatory reviews were read. Their natural
BOTH full-topology laws share one original graph and parameter tuple;
COMMON all-pairs calibration must first establish actual exclusive words.
The nested-prefix quotient is physical only after that source factorization.
The existing workbench's supplied private forest interface does not
implement those original full-topology queries, calibration, graph
reconstruction or boundary identities. Therefore this module is **not
wired as a verified original observation-to-stopping adapter**. It does not
let a menu/coverage flag impersonate the missing producer.

The new [lower-fibre countercontrol](../../2026-10-09-dot-local-forcing-and-coverage-review-1627z/g4-lower-fibre/EXACT-LOWER-FIBRE-STOCHASTIC-COUNTERCONTROL.md)
and its independent review were also read. Its opposite-sign kernels are
generated-group objects, not supplied positive physical words. No such
kernel is used as a source, and no stochastic inverse is admitted.

| Obligation | Evidence | Status / next decisive action |
|---|---|---|
| Published arity-12 obstruction | Frozen replay + independent standard-library cone consumer | Component reproduced; preserve failed generator history |
| Rational target local effective separator and quantitative neighbourhood | Exact tangent/Bernstein checker, polynomial bounds, rare/weak controls | Conditional component implemented; independent review separate |
| All effectively algebraic separator search | Reviewed RCF existence theorem | Backend absent; implement exact algebraic/RCF support before claiming coverage |
| Complete finite-cap supplied-source action | One bank, full labelled BOTH kernels + historical oracle | Implemented through runnable cap four; no all-copy conclusion |
| Original full-topology observation adapter | Reviewed calibrated decoder/tree-edge/paired guard providers | Original-law producer and source calibration not implemented here |
| All-rival localization / arbitrary multi-cell forcing | No provider supplied | OPEN; classify actual positive fitting arrays or prove finite covering |
| General original G4 | Original fixed-target/all-prefix quantifiers | OPEN; all cores, legal menus, shared registers and effectiveness remain |

Source hashes and immutable pins are in `SOURCE-PINS.json`. Packet hashes
are in `MANIFEST.sha256`. Root serializes publication; this lane did not
commit, push, deploy, contact anyone or modify frozen provider code.
