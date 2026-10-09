# Conditional zero-score certificate consumer

Contributor: Codex formal lane, 9 October 2026. **Compiler status: contributor FRESH KERNEL PASS** for both additions and the
complete owned-declaration audit; see `compiler-attempt-3/receipt.json`. Independent
replay is separately scheduled by the validation lane.
No original source provider or general G3 recognizer has been constructed.

The additions live in the existing `unifiedLean` Lake package:

- `../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/G3/ConditionalZeroScoreBound.lean`
- `../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/G3/ConditionalZeroScoreConsumer.lean`

The latest accepted selected assembly is the 181-module snapshot at frozen
`916e02a1d51d79cdffd300b9d8313df2608b08bc`, run 37749239915. Its existing
verification recipe assembles this baseline Lake package with the cloud source
additions. None of its 181 selected sources, target list, old receipts, Lake
registration or runtime pin was changed; these are two additive modules, not a
new all-package verification claim.

## Theorem map

| Hand-proof step | Lean declaration | Exact scope |
|---|---|---|
| Rational delta is positive and at most epsilon | `delta_pos`, `delta_le_epsilon` | Positive rational epsilon/sigma and nonnegative rational M |
| M delta is at most sigma/2 | `modulus_margin` | Rational arithmetic; covers M=0 |
| Positive finite weights cannot hide positive cells at exact zero | `cells_zero_of_weighted_endpoint_zero` | All weights strictly positive, all cells nonnegative, finite exact sum zero |
| Uniform weak-cell estimate gives a duration gap | `weak_cell_score_positive`, `zero_score_duration_gap` | Positive p/t; no lower coin floor; quantitative modulus is a premise |
| Equal-arm beta has rational loss | `equal_arm_pair_loss` | Actual pair formula and exp-duration comparison are explicit provider premises |
| Pair survival bounds the count | `geometric_budget`, `independent_product_count` | Nonnegative factors, ordinary factor at most one, exact chronological product and observed floor |
| Safe rational ceiling | `bound_reciprocal`, `rational_count_ceiling`, `expression_le_ceiling`, `ceiling_le_iff`, `zero_length` | `ceil[2(1+delta)/(b delta)]`; zero cells included |
| All physical slots obey the bound | `PieceCertificate.slot_count_bound` | Same finite weighted source certificate, INDEPENDENT or BOTH only |
| Every fitting source lies on a bounded piece | `WholeFibreProvider.every_fitting_source_bounded` | Explicit all-core cover, excluded-core soundness, all-fitting-piece cover, actual length and fixed-piece numeric identities |

The product budget is proved algebraically:
`(1-a)^L (1+L a) <= 1`, so `b <= s <= (1-a)^L` gives `L <= 1/(b a)`.
This supplies the same safe integer bound as the hand proof without evaluating
logs or exponentials. It does not itself verify an actual source kernel.

## Typed boundary and missing providers

`NumericData` has four rational fields `b`, `epsilon`, `sigma`, `M` and proof
fields for strict positivity/nonnegativity. `PieceCertificate` requires proofs
of the additive score identity, global nonnegativity on its cells, positive slot
weights, exact endpoint annihilation, normalized weak-cell modulus, actual
equal-arm pair law, analytic exp-duration estimate, chronological survival law
and observed same-source survival floor. JSON booleans do not inhabit these Lean
proof obligations.

`WholeFibreProvider` quantifies over every source fitting the **original** joint
observations. It requires all-core and all-fitting-piece coverage and excludes
cores only through a sound proof. Its certificate's lengths are tied to the
externally supplied actual physical source length, and its numeric data to one
fixed tuple for each finite core/piece. These identities prevent a freely chosen
certificate count or per-source changing constants from masquerading as the
effective source bound. The separate `SourceFaithful` predicate and `source_faithfulness` proof field
require all certificate data to come from that original source; their original
scientific interpretation must be supplied externally. This is an abstract
contract, without an instantiation
of the original scientific source type, observation compiler or full-source
backend.

Remaining decisive obligations: construct a source-faithful actual equal-arm
provider at its reviewed calibration/menu contract; establish the score and
uniform analytic estimates; derive the resource floor from the supplied joint
fibre; produce complete finite core/piece coverage; compile the bounded catalogue
with legal ordinary merging and all protected/shared constraints; verify original
joint feasibility with a complete backend. A conditional hypothesis is not a
certificate-producing algorithm. The reviewed COMMON additive-score coverage
obstruction in `2026-10-09-dot-local-forcing-and-coverage-review-1627z/g3-common/`
also prevents treating this as a universal COMMON score frontend.

## Reproducible verification

Pinned compiler: Lean v4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, binary SHA256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Pinned Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`, including its exact
committed `lake-manifest.json` and all eight dependency revisions.

On Linux x86-64 with Python 3, Git, curl, tar and zstd already available, a clean
machine can provision and build only the selected pinned imports in scratch:

```bash
python3 research/2026-10-09-codex-conditional-bridge-1630z/formal/provision_pinned.py \
  --scratch /tmp/g3-proof-runtime --evidence /tmp/g3-proof-provision-evidence
python3 research/2026-10-09-codex-conditional-bridge-1630z/formal/verify_lean.py \
  --lean-bin /tmp/g3-proof-runtime/lean-4.33.1-linux/bin \
  --mathlib /tmp/g3-proof-runtime/mathlib \
  --scratch /tmp/g3-proof-replay-scratch --evidence /tmp/g3-proof-replay-evidence
```

The provisioning script downloads and checks the exact compiler archive, fetches
the exact Mathlib commit and its committed dependency revisions, saves every
executed command/result, and performs a bounded source build. It refuses an
existing repository with revision drift. It does not run `lake update`, install
global packages or depend on a public Mathlib cache server. Its pin-reuse path
was actually executed with `--skip-build`; see `provision-pin-recheck/`. The
individual clean download/fetch/extract/build steps were executed in this lane
as described in the preserved logs; a fresh execution of the consolidated script
on another machine has not been claimed.

With this lane's already provisioned dependencies, the actual successful command
was:

```bash
python3 research/2026-10-09-codex-conditional-bridge-1630z/formal/verify_lean.py \
  --lean-bin /workspace/scratch/formal-runtime/lean-4.33.1-linux/bin \
  --mathlib /workspace/scratch/formal-runtime/mathlib \
  --evidence research/2026-10-09-codex-conditional-bridge-1630z/formal/compiler-attempt-3
```

Provisioning must use the **committed** Mathlib dependency revisions. Fetch the
Mathlib commit above, check it out detached, then parse its `lake-manifest.json`
and fetch/check out each package's recorded `rev` into `.lake/packages/<name>`.
Do not run `lake update` in the Mathlib root: its symbolic input revisions can
advance the dependencies. The selected source-build command, from that Mathlib
directory, is:

```bash
PATH=/workspace/scratch/formal-runtime/lean-4.33.1-linux/bin:$PATH \
LEAN_NUM_THREADS=4 timeout 600 lake build \
  Mathlib.Data.Rat.Floor Mathlib.Data.Real.Basic \
  Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset \
  Mathlib.Tactic.Linarith Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
```

The successful run elaborated the bound module in 3.567 seconds, the provider
consumer in 1.346 seconds and the complete audit in 1.738 seconds, all exit zero.
Its inventory covers 146 owned declarations and 69 theorem entries **including
generated structure/inductive theorems**, with zero owned axioms and zero
nonstandard axiom rows. The union of actual proof dependencies is exactly
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`,
`Lean.ofReduceBool` or `Lean.trustCompiler` appears in the owned inventory.
The main pinned dependency source build completed successfully (988 Lake jobs);
the separately added product-order import also completed (819 jobs including
reuse). Kernel warnings are lint notices, preserved literally.

The runner freezes both source files in a fresh scratch context, compiles
serially with `-j1 -M4096 -Ddebug.skipKernelTC=false`, and invokes an adapted,
attributed complete owned-declaration audit from the existing public
`package/scripts/AuditTemplate.lean`. It rejects any owned axiom or axiom outside
`propext`, `Classical.choice`, and `Quot.sound`, and saves exact commands, exit
codes, object/source/log hashes and the full inventory. It does not recompile
the original 181 modules.

Preserved provisioning failures: the first direct Mathlib `lake update` advanced
the dependency input revisions and caused syntax failures during the subsequent
source build; that attempt is not authenticated pinned Mathlib verification.
Its logs remain under `logs/mathlib-update.*`, `logs/mathlib-source-build.*` and
`logs/mathlib-cache.*`. The original manifest and all dependencies were then
restored exactly in scratch. The official alternate legacy cache returned zero
of 968 selected artifacts (exit zero is not successful dependency availability),
preserved under `logs/mathlib-cache-pinned-alternate.*`. A fresh source build of
the corrected pinned dependencies passed within its 600-second cap, with separate
`logs/mathlib-source-build-pinned.*`.

The reviewed mathematical input remains attributed to dot's
`2026-10-09-dot-reviewed-guard-boundaries-1615z/g3/` proof, independent hand review
and INDEPENDENT survival-floor addendum. Their hand acceptance is distinct from
this contributor's source execution, independent replay and kernel verification.

The first two new-module compiler attempts failed elaboration and are preserved
in `compiler-attempt-1/` and `compiler-attempt-2/`; only attempt 3 supplies the
acceptance receipt. Their fixes concern a multiplication-cancellation lemma and
rational-to-real cast normalization. Existing frozen providers were untouched.

The compiled objects are in the scratch directory named by the successful
receipt. Source and object identities are frozen in that receipt and summarized
in `source-manifest.json`; a published source packet is distinct from retained
local compiled artifacts.
