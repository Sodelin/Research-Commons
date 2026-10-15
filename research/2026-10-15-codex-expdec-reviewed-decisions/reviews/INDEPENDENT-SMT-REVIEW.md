# Independent review of the bounded SMT controls

Reviewer: Codex subagent `commons_bridge`, independently delegated by the
EXPDEC root. Date: 15 October 2026. Scope: the authored finite algebraic
controls, native-call wrapper and existing execution receipts. This is a
scoped engineering and elementary-mathematics review, not a security scan or
independent native execution. No solver, container, compiler or device job was
launched by the reviewer.

## Verdict

**The recorded 16-result run passes the stated finite algebraic controls.**
All eight UNSAT instances have elementary hand proofs given below. All eight
retained SAT assignments satisfy the actual asserted formulas by exact
rational arithmetic. The eight UNSAT outputs contain Z3 proof terms; the
records correctly disclaim independent proof-kernel replay. These controls
do not establish transcendence, exponential identities, correctness of a
production expression parser/normalizer or source compiler, conditional
real-exponential decidability, or the G3/G4 masters.

**One reporting defect was found in the reviewed runner:** an explicit
`unknown` followed by an unavailable proof/model diagnostic is classified as
`INVALID_SOLVER_OUTPUT`, losing the solver's `unknown` status. Every query
unconditionally requests a post-check artifact. This does not affect the
present successful run and cannot turn UNKNOWN into SAT/UNSAT, but it limits
the claimed distinction among failure outcomes. Root was notified; the
reviewer did not edit owned scripts.

## Exact reviewed evidence

The reviewed receipt is
`verification/smt/results/20261015-run-02/RESULT.json`, SHA256
`e6332806ad67c033da8eb0cdf9cba3ab6940eb5ce99f9efbe161490eca57ca74`.
It records source HEAD `58a84f0acf2809304363cb4926cee97190f6f422` at execution
and separately authenticates the actual authored files, including working
tree content. Do not assume the recorded HEAD alone contains every executed
source byte.

The following recorded SHA256 values match the independently recomputed
current file hashes:

| File | SHA256 |
|---|---|
| `run_checks.py` | `be32321936889e7971a85b2339d2e1298d2ecd66ae534a5f7d7d8ef4783cfbc8` |
| `z3_c_api_worker.py` | `e5b6ec118cfe827595292499b691de47f6af2703f1a584bfe2fb83bc4edb07a2` |
| `obligations.json` | `704322e756741f288efa74f898ccf2cf6e2637e9824c97f42bddb09d46116f2e` |
| `check_countermodels.py` | `a93fcdfc5201107e33060bb36bce362170bdf2e8f1ecdad7baae8c49df584dc3` |

The reviewer recomputed and matched **all 16 query hashes, all 16 stdout
hashes and all 16 stderr hashes** against the receipt. Every recorded stderr
is empty, every process exits zero, and every `wall_timeout` is false. The
16 IDs are distinct and exactly match the manifest. The recorded per-job
elapsed range is 0.421047–0.521144 seconds. Read the outputs themselves,
including the eight exact assignment lists and the eight proof prefixes;
there was no inferred or fabricated native result.

The separate independent model-check receipt authenticates the same main
receipt hash and its checker source hash. Its parser uses decimal/rational
syntax as exact `Fraction` values, rather than converting through binary
floating point. The reviewer also manually checked each assignment against
the actual SMT formulas, rather than relying on its `all_valid` field.

## Eight independent elementary UNSAT arguments

The solver is asked to satisfy the negation of an identity/implication in
each case. These arguments prove the exact encoded contradictions.

| ID | Independent hand argument |
|---|---|
| `01-product-convolution` | Distributivity gives `(a0+a1*x)*(b0+b1*x) = a0*b0 + (a0*b1+a1*b0)*x + a1*b1*x*x` for all real assignments. Its asserted negation is false. |
| `02-coefficient-grouping` | Both sides expand to `a0*U+a1*x*U+b0*U+b1*x*U`. The unrestricted real symbol `U` makes this a ring identity, with no exponential axiom required. |
| `03-exponent-sum-cancellation` | `x*x+2*x+(-2)*x=x*x`. Its negation is impossible. This checks exponent-polynomial arithmetic, not the exponential product law. |
| `05-shared-parameter` | Equality of one `theta` to both `1/3` and `2/3` implies `1/3=2/3`, hence `1=2`. Positivity constraints do not resolve that contradiction. |
| `07-strict-domain` | `theta=0` and `theta>0` imply `0>0`. |
| `11-division-guard` | From `d != 0` and `z*d=n`, cancellation in the real field gives `z=n/d`, contradicting the asserted inequality. SMT's totalization of division at zero is irrelevant because the nonzero guard is present. |
| `14-delta-true-certificate` | `|rhat-r| <= delta/4` gives `r >= rhat-delta/4`. Together with `rhat >= -delta/2`, this gives `r >= -3*delta/4 > -delta` for `delta>0`, contradicting the asserted `r < -delta`. |
| `15-delta-false-certificate` | The same approximation bound gives `r <= rhat+delta/4 < -delta/4 < 0`, contradicting the asserted `r >= 0`. |

These are independent hand arguments, not machine replay of Z3's proof
language. The actual outputs contain eight syntactically printed `(proof`
sections, between 506 and 4495 bytes for their complete stdout files. The
runner's `proof_term_present` flag is only a substring check; the reviewer
does not elevate it into proof-kernel acceptance.

## Eight SAT witnesses and what they demonstrate

| ID | Retained exact values | Independent interpretation |
|---|---|---|
| `04-constant-shift-key` | `x=0`, `Q0=0`, `Q1=1` | The asserted distinct exponent polynomials are unequal. Their normalized nonconstant parts are both `x^2`; discarding the intercept would lose this distinction. The SMT input itself does not execute a normalizer or apply `exp`. |
| `06-refitted-parameters` | `theta_1=1/3`, `theta_2=2/3` | Both are strictly inside `(0,1)` and satisfy the two equations separately. Together with UNSAT control 05, this genuinely exposes replacing one shared tuple by separate row fits. It is a small logical control, not a biological source realization. |
| `08-relaxed-domain` | `theta=0` | Satisfies `theta>=0` and violates strict positivity, exactly exposing boundary admission by relaxation. |
| `09-single-point-equality` | `a=1`, `b=0`, `x=0` | The nonzero polynomial `a*x+b=x` vanishes at this single point. |
| `10-open-interval-witness` | `x=1/2` | Lies in `(0,1)` and is nonzero, witnessing failure of that polynomial's identity on the interval. |
| `12-omitted-division-guard` | `n=0`, `d=0`, `z=42` | Satisfies the weakened graph `z*d=n`, even though intended partial real division `0/0` is undefined. This genuinely tests omission of the graph's definedness guard. It intentionally asserts no totalized SMT division value at zero. |
| `13-surface-versus-open` | `a=1`, `b=-1`, `x=y=0` | Satisfies all asserted surface and polynomial constraints. The fixed polynomial is `x-y`, whose restriction to the entire surface `x=y` vanishes by substitution; it is nonzero off that surface. The solver supplies a point on the surface, while the all-surface statement is elementary hand reasoning. |
| `16-delta-slack-counterexample` | `delta=1`, `rhat=-1/2`, `r=-3/4` | Approximation error is `1/4`, and `rhat=-delta/2` selects the approximate positive branch. Yet `r<0`; only the weakened condition `r>=-delta` follows. This is an actual countermodel to promoting that branch to exact truth. |

The requested failure cases are therefore exercised by exact retained
witnesses, not just by naming guard/shared-tuple/slack concerns. Controls
14–16 assume the approximation bound; they do not verify that an
exponential-expression evaluator establishes such a bound.

## Resource and native-interface review

The supported launch path is the existing `proot-distro login
linux-levels-debian -- /usr/bin/python3 -B ...` route. It is passed as an
argument vector, without a shell. Jobs run sequentially; the runner does not
spawn a service, retry without limits or fall back to another unbounded
solver. Output uses fresh files, and an existing output directory is refused.

Before starting the child, the runner installs hard CPU (3 seconds), regular
output-file-size (65536 bytes) and zero-core limits in its child setup.
It starts a new session and waits with a six-second timeout. On expiry, it
signals the process group with SIGKILL and reaps the child. The wall wait
starts after `Popen` returns; this is a subprocess wait deadline, rather than
a separately supervised absolute deadline covering every possible failure
inside process creation. Nothing in the fixed launch path knowingly detaches
a descendant from that group.

The memory cap is deliberately applied inside Debian. The worker sets hard
CPU, 536870912-byte address-space, output-size and zero-core limits before
`ctypes.CDLL` loads Z3. A failed `setrlimit` raises and stops the worker;
there is no catch-and-continue path that silently loads an unbounded solver.
The outer Android/PRoot startup does not have this address-space cap, as the
documents accurately explain. CPU/address-space limits are per process,
not aggregate CPU/RSS limits for a whole arbitrary descendant tree.

The engine probe reads back hard/soft CPU, address-space and file-size limits:
`[3,3]`, `[536870912,536870912]`, `[65536,65536]`. It reports native Z3
`4.13.3.0` and library SHA256
`cb5320742a56e44ed0d86e14acc4b44a8862ca2a9a1af894dc0ad1862ff7fb6e`.
Those are retained runtime observations. No resource-exhaustion job was
run by this reviewer, so the probe plus source support the limit claims;
they are not a stress test of every platform enforcement boundary.

Every reviewed SMT input requests `:timeout 2000` and
`:memory_max_size 192`. These are additional Z3 requests, not the only
limits. All inputs are small local authored files. The worker rejects an
input over 16384 bytes or containing NUL, sets explicit ctypes signatures,
checks null config/context/output returns and destroys its context in a
`finally` block. With `c_char_p` result decoding, the output is copied while
the context is still live. The config is destroyed after creating the
context. No independent native library ABI verification was performed.

The initial launcher-cap failure is preserved at `results/20261015-run-01/`.
Its `FAILURE.md` candidly says original failed-probe metadata was not saved;
the empty outputs cannot establish its exit code. The separate `/usr/bin/true`
control's `-6` return is reported in that historical narrative, not in a
structured execution receipt independently authenticated here. It is
appropriately excluded from the sixteen solver outcomes.

## Reporting defect: UNKNOWN plus artifact error

In the reviewed `run_checks.py`, lines 75–84 parse standalone status lines,
then prioritize wall expiry and nonzero exit, then reject any `(error ` text
before selecting the single parsed status. Every UNSAT-intended input ends
with `(get-proof)`; every SAT-intended input ends with `(get-value ...)`.
If the solver instead returns UNKNOWN, that unconditional artifact request
may add an unavailable-proof/model diagnostic.

The reviewer ran a **pure Python parser control**, with no native call:

```text
unknown
(error "proof is not available")
```

The current branch records `INVALID_SOLVER_OUTPUT`, although its parsed
status list is exactly `["unknown"]`. This is a demonstrated classification
behavior on a synthetic payload; no actual native UNKNOWN is claimed to
have occurred in run 02. If the native library instead exits nonzero on a
diagnostic, the current result becomes `EXECUTION_FAILURE`, likewise
preserving failure but losing a separate UNKNOWN field.

Recommended scoped fix: preserve the parsed solver status separately from
execution/artifact validity, and retain artifact diagnostics; or make proof
and model requests conditional on the result. Keep malformed output,
nonzero exit, timeout and UNKNOWN distinct. Do not treat UNKNOWN as meeting
an expected SAT/UNSAT obligation. A small pure-output classification check
can verify this without rerunning the native sixteen-job workload.

Two smaller limitations are worth preserving as scope, not current blockers:
the runner records stderr but does not classify zero-exit stderr diagnostics,
and its proof-presence flag does not validate a proof's structure or linkage.
All current stderr files are empty and all eight native statuses are
independently supported by the elementary arguments above.

## Review boundary

Written only `reviews/INDEPENDENT-SMT-REVIEW.md`. No owned script was edited,
no file was staged or committed, no Commons/peer message was sent, and no
native execution was repeated. The current successful result is accepted at
the finite-control evidence tier. Future runner/source fixes need their own
source identity and appropriately scoped verification; historical receipts
should remain unchanged.

## Addendum: corrected classifier and publication preparation

This addendum supersedes the earlier outstanding-classifier-defect status.
Independently inspected committed successor
`b72886fed188a8adb7db5a50ba3ad44b44fcb47d` and its retained receipts, without
rerunning Z3. The original sixteen-job receipt is unchanged at SHA256
`e6332806ad67c033da8eb0cdf9cba3ab6940eb5ce99f9efbe161490eca57ca74`.

| Successor artifact | Independently recomputed SHA256 |
|---|---|
| `verification/smt/run_checks.py` | `2095bdebc51de5d0cf63c796a07a375ef95d416cf7a64c4babc77b223c37ecd3` |
| `verification/smt/check_status_parser.py` | `1f4b7f170768783bd055df2d6d7924dfb890958c0fe4331887c3ee69a6de6c30` |
| `results/20261015-native-unknown-01/PARSER-REGRESSION.json` | `dceae80ed499c0cf1196bdbe154723413b8e4454422ca3dbcc66eac93dacfa6b` |
| `results/20261015-native-unknown-01/RESULT.json` | `197c08cc86b4f1b351d98d83019613ffe91388b4516d9981a5249e1613ecc012` |
| Native UNKNOWN stdout | `ca08938fa20117bd08ac679d32c002f97d2f95f93b34e3358272b78b7608cb38` |
| `scripts/publish_commons_packet.py` at the reviewed commit | `2c250ae26096dbd1021a893c1ced2b719f20a520fc256bfb5a7e7291b9a49f48` |

The corrected `classify_result` preserves a uniquely parsed solver status
separately from execution outcome and proof/model availability. Clean UNKNOWN
with a recognized unavailable-artifact diagnostic remains `actual=unknown`;
nonzero exit or wall expiry retain `solver_status=unknown` but keep their
execution-failure/timeout outcome. A separate syntax error remains invalid,
and SAT/UNSAT plus an artifact error becomes `ARTIFACT_FAILURE` with
`usable_decision_evidence=false`. Recognized stderr diagnostics now
participate in classification. This corrects the demonstrated defect.

Executed only offline Python inspection: independently recomputed the
classification of all thirteen saved synthetic fixtures and all sixteen
retained historical stdout/stderr pairs using the new function. Every
fixture classification matches the saved record, and all sixteen historical
statuses remain unchanged. Also matched both checker/parser source hashes,
the new native receipt's authored-source hashes and its query/output hashes.

The separately recorded native resource control sets `:rlimit 1` and asks
whether `x*x=2`; its retained stdout is exactly a native `unknown` followed
by `(:reason-unknown "max. resource limit exceeded")`. Its receipt reports
exit zero, no wall timeout, 0.621992 seconds and
`usable_decision_evidence=false`. The reviewer inspected and authenticated
this result, but did not repeat the native execution. This is a genuine
recorded resource-limited UNKNOWN, not evidence that `x*x=2` is
mathematically undecidable. The existing hard process limits remain present.

The publication helper received a narrow read-only check, not a security
audit. It reads selected files from an exact committed source snapshot;
selection excludes coordination/status/team and runtime-state directories.
It includes authored theorem/research/review/SMT evidence. JSON execution
exports recursively remove `command_argv`, retain original/published hashes
in an export map and rerun only the exact rational model checker against the
exported receipt. The historical pre-repair runner is separately retrieved
at `5990906`; its SHA256 matches the original tested runner. No private
routing-pattern match remained in the 79 selected committed payload files
after the in-memory export transformation. This is a bounded source review
and explicit pattern check, not a guarantee that regex matching detects
every possible private datum.

For publication, the helper obtains current main, creates a tree based on
that main's tree with changes confined to its own packet prefix, creates a
single-parent commit and requests `force:false`. A raced non-fast-forward
update is retried against fresh main, rather than forced. It computes the
entire intended packet subtree hash locally, reads back the published
subtree object ID through GraphQL and compares them, then independently
reads back the theorem's bytes. Git tree identity covers all file/blob
identities and modes; this is stronger than checking only one visible file,
although it does not download every published body again.

**No publication blocker was found for the inspected unused destination:**
authenticated GitHub lookup for
`research/2026-10-15-codex-expdec-reviewed-decisions` returned HTTP 404.
One reuse limitation was communicated to root: the reviewed helper does not
itself refuse an already-existing packet prefix. Its current additive use
therefore assumes that prefix is absent. A later publication should verify
absence again or add an explicit existing-prefix refusal, preserving
immutable earlier contributions. This review did not publish a packet or
modify the helper. Later source changes need their own hash pin.
