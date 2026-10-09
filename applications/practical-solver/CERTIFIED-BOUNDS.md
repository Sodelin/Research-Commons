# Exact same-source bounded integration

The optional adapter reuses dot's existing original-source solver, its finite
architecture census and its semantic certificate checker. It supports an
actual source witness and exclusion within a declared complete finite registry.
The conditional count arithmetic is executable, but its source-provider and
retained-core catalogue bridge remain unfinished. General G3/G4 remain open.

Run the conditional arithmetic example with the default Python:

```sh
python3 -B applications/practical-solver/certified_bounds.py \
  --request applications/practical-solver/examples/certified-bounds/conditional-count-unknown.json \
  --output /tmp/conditional-count-1
```

It computes delta=1/2 and the safe conditional bound 24. It returns `UNKNOWN`
with `UNKNOWN_PROVIDER_VERIFIER_UNAVAILABLE`. The example's slot, floor and
derivation hash are explicitly unverified placeholders. Exact arithmetic does
not establish that this source has the assumed score, floor or coverage.

The launcher also exposes `run.py certified-bounds --request ... --output ...`.
The direct module API is `consume(request, fresh_workdir, python_executable=None)`;
`read_request(path)` rejects duplicate fields and malformed JSON. Fresh output
includes the complete input, result, execution receipts, backend evidence and
semantic checker output. Default host Python in the authored run lacked
NetworkX and Z3, so the backend example returned `UNKNOWN_BACKEND_UNAVAILABLE`
with `solver_called=false`.

Provision the inherited exact backend in new scratch using Python 3.11–3.13,
POSIX resource support and the frozen package's dependency pins:

```sh
python3 -m venv /tmp/conditional-source-venv-1
/tmp/conditional-source-venv-1/bin/python -m pip install \
  -r research/2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package/requirements.txt
python3 -B applications/practical-solver/certified_bounds.py \
  --request applications/practical-solver/examples/certified-bounds/finite-witness.json \
  --python-executable /tmp/conditional-source-venv-1/bin/python \
  --output /tmp/conditional-source-witness-1
```

The inherited runtime is authenticated and copied into the fresh output
directory. Backend children receive a minimal environment, a 30-second CPU
cap, 45-second wall timeout, 512-MiB address-space limit and 16-MiB per-file
limit. Provisioning needs public package downloads; subsequent examples use
local files. Missing or mismatched pinned dependencies, time limits and failed
semantic checks produce `UNKNOWN`. The optional Rust signed-nine component in
the main numerical app is a cover diagnostic; it supplies no original-source
feasibility or bounded-catalogue binding.

| Example | Authored checked result | Exact scope |
|---|---|---|
| `finite-witness` | `CERTIFIED_SOURCE_WITNESS` | One admitted positive source fits the complete supplied law |
| `shared-row-exclusion` | `CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS` | Contradictory rows exclude all six graph/mode entries of the declared finite class |
| `strict-positivity-exclusion` | `CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS` | Boundary-only solutions are excluded by strict positivity |
| `bounded-witness` | `CERTIFIED_SOURCE_WITNESS` | Positive witness with incomplete original registry |
| `bounded-exhaustion` | `UNKNOWN` | No witness within the explicit zero-extra-hybrid budget |
| `conditional-count-unknown` | `UNKNOWN` | Conditional rational arithmetic; no verified source provider |

Each example lives under `examples/certified-bounds/`. CLI exit codes are 0
for the two certified scoped outcomes, 2 for `UNKNOWN`, and 1 for refusal.
Software exact recomputation is the certificate tier here. No Lean theorem
about the Python engine or independent proof-kernel check of general Z3
exclusions is claimed. Linear contradiction certificates are independently
recomputed; other exclusions retain the inherited same-backend replay tier.

## Supported request class

The wrapper schema is `same_source_certified_bounds_v1`. Its operation is
`finite_registry`, `bounded_search` or `conditional_count`, and `source_request`
contains the unchanged inherited source request. The first two operations
support exact rational unranked rooted laws, unrooted split systems and joint
quartet systems on the original admitted binary rooted-LSA, outer-labelled
planar, cut-child galled sources. Parallel edge occurrences, incoming parental
bits, original labels and positive natural parameters retain their meaning.
Clocks are freely positive and edge-specific. Every response row uses one
graph, one candidate mechanism and one physical assignment, including all
finite randomized-program operations.

Adapter resource caps are 2–4 taxa, at most two total hybrid IDs, eight sampled
copy labels per row, 32 rows/program operations, 30 seconds, 1,000 sources and
10,000 SMT milliseconds. All three limits must be explicit. Probabilities,
program weights and count parameters use exact integer or p/q strings. The
unchanged upstream parser and checker perform actual source admission. Tied
clocks, arbitrary shared physical constraints, algebraic observation inputs,
calendar readers and statistical admission require their original encoders.

`finite_registry` requires `registry.complete=true`. Its exclusion covers
exactly the declared n, complete original-ID registry and candidate mechanisms.
`bounded_search` requires `registry.complete=false` and an explicit
`max_extra_hybrids` from 0 to 2. Finite exhaustion never gives an unrestricted
NO. Original controlled IDs are preserved when candidate unmarked IDs are
added by the inherited bounded-search routine.

The inherited `mechanisms: ["independent", "common"]` searches a union of
candidate mechanism models. It does not jointly observe the two mechanisms
on one physical source. A natural BOTH-menu provider needs its genuine paired
compiler, which this backend does not implement.

## Conditional count interface and remaining obligations

`conditional_count` takes `count_certificate` with schema
`conditional_independent_zero_score_v1`, mode `INDEPENDENT` or `BOTH`, a hash
binding the complete source request, and distinct physical `slots`. Each slot
supplies b, epsilon, sigma, M, exact rational `endpoint_score="0"` and a
`survival_floor_evidence` descriptor citing supplied row indices, provider ID,
artifact SHA256 and complete request SHA256. Optional `provider_evidence`
uses the same descriptor. Those descriptors identify submitted evidence;
they are not verified proofs. There is currently no accepted executable
provider verifier and no caller-extensible provider registry.

The exact arithmetic computes
`delta=min(epsilon,sigma/(2*(M+1)))` and
`ceil(2*(1+delta)/(b*delta))`. It checks strict b/epsilon/sigma positivity,
M nonnegativity and the rational ceiling inequalities. It rejects approximate
or positive endpoint scores, absent floor derivations, boolean providers,
changed source hashes, duplicate physical slots and incompatible modes.
Unverified floor/coverage descriptors leave the result `UNKNOWN`.

The missing mathematical verifier must establish all-core/piece coverage,
actual equal-arm source admission, chronology, a nonnegative additive score
using the same physical tuple, positive-weighted exact endpoint annihilation,
a uniform weak-cell modulus and an input-derived uniform INDEPENDENT survival
floor. The missing catalogue compiler must then preserve all protected sites,
original IDs, shared registers, physical relations and every supplied row when
translating the distinct slot bounds into finite original architectures.
No slot bound is substituted for `max_extra_hybrids`.

The reviewed COMMON Poisson obstruction shows that regular globally
nonnegative additive zero scores cannot supply universal coverage on a known
original COMMON NO family. The conditional BOTH/equal-arm theorem remains
valid at its stated domain. See the [source obstruction](../../research/2026-10-09-dot-local-forcing-and-coverage-review-1627z/g3-common/COMMON-POISSON-ZERO-SCORE-OBSTRUCTION.md)
and the [implementation evidence packet](../../research/2026-10-09-codex-conditional-bridge-1630z/bounded/README.md).
