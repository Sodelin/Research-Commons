# Source-pinned bridge to the retained calendar-law compiler

Date: 15 October 2026. Contributor: Codex subagent `commons_bridge`, delegated
by the phone EXPDEC theorem task. This is a read-only source audit and
hand-derived application. It is not Dot's selection of the main paper, an
adopted biological profile, implementation, independent mathematical acceptance,
or a compiler execution receipt. Existing mathematical, compiler and device
owners retain their scopes.

## Result and citation correction

**Observed source:** the retained joint-law manuscript already proves and
implements exact equality of two supplied rational calendar-metric genealogy
states. Its compiler emits a much narrower language than arbitrary
exponential expressions: finite sums of rational constants times exponentials
of rational affine functions of all observed merger times. There are no
nested exponentials, hidden merger integrations, matrix diagonalizations or
root searches in this density compiler.

**Hand-derived consequence:** the same finite event compilation, using exact
real-algebraic arithmetic in place of rational arithmetic, gives a terminating
full-law equality decision for two supplied real-algebraic states under the
same observation and positive-rate model. Theorem 1 of the local draft
supplies its symbolic identity step. This is an extension of an attributed
existing theorem, not a new all-source recognition result. The existing
Python code has not been extended to algebraic arithmetic.

**Observed citation error:** the local draft links the delivery note at commit
`653ed43e1a9eab2b359f028dc0bd109db62fbbf8`. Authenticated GitHub contents lookup
returned HTTP 404 for that path at that commit. The source packet is present
there. A valid direct citation is its
[PROOFS.md, Section 4.5, Theorem 8](https://github.com/Sodelin/Research-Commons/blob/653ed43e1a9eab2b359f028dc0bd109db62fbbf8/research/2026-09-30-astra-joint-law-1744z/PROOFS.md#45-an-exact-full-metric-equality-decision-for-supplied-rational-states).
The [delivery note](https://github.com/Sodelin/Research-Commons/blob/c3f9e5b60e83719902da8636dfa0fd208a2d41b4/communications/2026-09-30-astra-joint-law-1744z-delivery.md)
exists at the inspected current pin; its Git blob is
`f422ece8824bb9ef2057da3a63ca5150bcedeb13`.

The word “accepted” in the historical acceptance-note filename describes the
author's accepted continuation assignment. The source README and manuscript
explicitly report submitted hand proofs, executed author controls and pending
independent acceptance. That filename is not a review certificate.

## Authenticated source identities

The inspected current Commons commit was
`c3f9e5b60e83719902da8636dfa0fd208a2d41b4`.
Read [AGENTS.md](https://github.com/Sodelin/Research-Commons/blob/c3f9e5b60e83719902da8636dfa0fd208a2d41b4/AGENTS.md)
(blob `f4f80a489253adf55c8e165bb68ce6a506ae7ca0`) and
[START-HERE.md](https://github.com/Sodelin/Research-Commons/blob/c3f9e5b60e83719902da8636dfa0fd208a2d41b4/START-HERE.md)
(blob `fc0092a4518d071b57711d13b82ccfcba88c01c1`). Inspected the relevant
current-scope tail and current coordination, not every historical theorem in
the 662,734-byte
[CURRENT-SCOPE.md](https://github.com/Sodelin/Research-Commons/blob/c3f9e5b60e83719902da8636dfa0fd208a2d41b4/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md)
(blob `4da217ec6547f25e920a607aa81c8ee0cb343498`).

The following five packet bodies were fetched through authenticated `gh api`
at `653ed43e1a9eab2b359f028dc0bd109db62fbbf8`. Their byte counts, SHA256 and
Git blob SHA1 were recomputed in memory. Recomputed blob SHA1 matched the
GitHub contents API's `sha` for every row.

| Source | Bytes | Git blob SHA1 | Independently recomputed SHA256 |
|---|---:|---|---|
| [PROOFS.md](https://github.com/Sodelin/Research-Commons/blob/653ed43e1a9eab2b359f028dc0bd109db62fbbf8/research/2026-09-30-astra-joint-law-1744z/PROOFS.md) | 41499 | `05dde869aec887fea1900e13f3a298b46aafa700` | `2fc9ca9866619a911873253768aa5370ce84cf3c14e28c2a3bbf8f215c9e45fe` |
| [metric_law.py](https://github.com/Sodelin/Research-Commons/blob/653ed43e1a9eab2b359f028dc0bd109db62fbbf8/research/2026-09-30-astra-joint-law-1744z/metric_law.py) | 14643 | `afe23b39a014e5e1b161c3529455aa7d8272cdc0` | `2bc42eb488654a43b01e353fd4e7822713c2883d292dc1f1815fb5691d02527e` |
| [joint_kernel.py](https://github.com/Sodelin/Research-Commons/blob/653ed43e1a9eab2b359f028dc0bd109db62fbbf8/research/2026-09-30-astra-joint-law-1744z/joint_kernel.py) | 11361 | `eff83bd5edd7eb433be4ad5ea9a24d1335a780ed` | `89f3a0725b3bc9db736f1c49069e228032bc863051d663493c9b14c2de8a20c2` |
| [checks.json](https://github.com/Sodelin/Research-Commons/blob/653ed43e1a9eab2b359f028dc0bd109db62fbbf8/research/2026-09-30-astra-joint-law-1744z/checks.json) | 7915 | `2731e25050beb0d70f08f6dd8680f3940cc9176d` | `740db422c357efc03de236a3221395285370072492ed703c3dd946fb4ff46570` |
| [manifest.json](https://github.com/Sodelin/Research-Commons/blob/653ed43e1a9eab2b359f028dc0bd109db62fbbf8/research/2026-09-30-astra-joint-law-1744z/manifest.json) | 2085 | `0ab9621f0658328e8124b32e5308af0e83101b3a` | `585262705ea679bb87eb19ca47a5bdc321a05c0060f7b004be71ea56e94f4f93` |

These are file-integrity checks. No mathematical result follows merely from
a matching hash. The retained packet is attributed to GPT-6 Astra Pro,
`ASTRA-JOINT-LAW-20260930-1744Z`; its manuscript credits classical
coalescent-history calculations and prior gene-topology computation.

## Actual input and output grammar

**Observed in `metric_law.py`:**

- `Network` carries finitely many node ages, a finite tuple of population
  edges, and one ancestral `root_rate`. Each edge has an ID, parent, child,
  positive pair-coalescence rate, and an inheritance probability only when
  entering a hybrid. `rational` explicitly rejects floats and booleans;
  numerical inputs are coerced to `fractions.Fraction` (lines 19–22, 40–45).
- Graph validation requires one binary root, ordinary tree/hybrid degrees,
  distinct contemporaneous leaves at age zero, strict parent-age greater
  than child-age on every edge, positive rates, and complementary interior
  inheritance probabilities at every hybrid (lines 63–90).
- The constructor calls `validate()` with `require_source=False`.
  LSA-root, cut-child galledness and outer-labeled planarity are calculated,
  but rejection for failure of these extra biological restrictions and
  `n >= 4` occurs only with `validate(require_source=True)` (lines 91–115).
  The arithmetic equality checker does not itself establish that canonical
  biological admission has been requested and passed.
- Modes are exactly `ind` and `com`. The former branches over all parental
  choices independently for each currently surviving lineage; the latter
  makes one parental choice for all active lineages at that hybrid. Hidden
  routes are summed while the entire joint state is retained (163–187).
- A complete ranked history lists `n-1` merges of currently live disjoint
  clade bitmasks. No intermediate merger is integrated out (203–226).
- The emitted expression is represented by a dictionary
  `(b,c_1,...,c_(n-1)) -> a`, meaning
  `a * exp(b + sum_j c_j*t_j)`. Every key entry and value is rational
  (132–159, 267–271). There is no nonconstant polynomial multiplier in this
  particular compiler, although Theorem 1 admits those multipliers.
- `joint_kernel.py` is a separate topology compiler with rational
  `x_e = exp(-t_e)` inputs. It must not be treated as having rational metric
  ages or rates. This distinction is explicit in `rooted_law` (134–147) and
  PROOFS Section 2.2. Rational pair survival generally has a transcendental
  logarithmic length.

For one current state, let `k_e` be the number of live ancestors on population
edge `e`. Its total merger hazard is

\[
\Lambda=\sum_e\binom{k_e}{2}r_e.
\]

`_survive` adds `Lambda*(previous_time-current_time)` to the affine exponent.
`_gene_event` rejects a merger unless its two ancestors share a population
and otherwise multiplies by that edge's rate. `_node_event` moves or branches
the state with its correct inheritance weight. Every action uses only finite
sums/products of input numbers and affine time expressions. Once the last
gene merger occurs, summing the remaining state weights is correct: all
unobserved later routing has conditional total probability one. This last
point is explicitly justified in PROOFS Theorem 8.

## Histories, calendar cells and full-law coverage

**Observed source and hand-checked reading:** `equal_metric_laws` forms the
sorted union of the two models' positive internal-node ages. If it has `m`
distinct entries, there are `m+1` open demographic intervals. It enumerates
every complete ranked labeled binary history and every weakly increasing
`n-1` tuple of interval indices (`combinations_with_replacement`, 302–310).
The implied cell also has `0 < t_1 < ... < t_(n-1)`.

Each such interval-index tuple has a nonempty open full-dimensional ordered
cell. Multiple gene times assigned to one demographic interval remain
strictly ordered inside that interval. Consequently the total history/cell
count, before early distinction or resource limits, is

\[
\left(\prod_{k=2}^{n}\binom{k}{2}\right)
\binom{m+n-1}{n-1}.
\]

Demographic ages repeated at different nodes appear once as a boundary. Edge
ages are strictly ordered along every directed edge, so distinct nodes at
the same age cannot be ancestor and descendant. Their instantaneous routing
acts on disjoint active populations; the code's deterministic node order
does not introduce an extra chronological mechanism.

The density is with respect to ordinary `(n-1)`-dimensional Lebesgue measure
for each discrete ranked history. Under this exact model, every merger wait
is continuous with a finite rate, demographic routing does not force a gene
merger, and there are finitely many events. Thus merger-at-boundary and
simultaneous-merger events have probability zero. The positive unbounded
ancestral population completes all finitely many lineages almost surely.
PROOFS Theorem 8 states these facts explicitly. There is no unrepresented
atomic or lower-dimensional law component under this contract.

This closes the cell-to-full-law step for this model. A theorem about another
observation that includes forced coalescences, censoring atoms, deterministic
times or singular charts must give its own complete reference-measure
decomposition. The absence of atoms here cannot be transferred by changing
the model description alone.

## Exact identity procedure and relation to the draft

**Observed retained procedure:** subtract the two dictionaries and combine
identical full exponent tuples, discarding zero rational coefficients.
Distinct slope vectors are independent as exponential functions on any open
cell. At a fixed slope, a rational sum of exponentials of distinct rational
intercepts is zero only when all grouped rational coefficients vanish.
The original proof reduces the latter statement to transcendence of
`exp(1/D)` for a common positive denominator `D` (PROOFS 4.5).

This matches the local theorem's two groupings. For affine `Q`, its normalized
`R=Q-Q(0)` is exactly the slope vector, and its `c=Q(0)` is the intercept.
The draft replaces the rational-intercept transcendence argument by
Lindemann–Weierstrass, which also admits real-algebraic intercepts and
coefficients. Its polynomial exponent argument covers a strictly larger
symbolic language; that generality is not required to describe the retained
compiler.

A cell is an open ordered region, rather than the rational box used in the
local theorem statement. This causes no gap: find a nonempty rational box
inside the cell using exact comparison with its algebraic boundaries. Each
compiled exponential polynomial is entire real analytic. Identity on this
box is equivalent to identity everywhere for that formula, and hence to
identity on the cell. For a nonidentity, the draft's rational witness search
can be restricted to that box.

`different` currently returns a symbolic nonzero density difference with its
history, interval indices and exact boundaries; it does not return an
evaluated probability difference. A rational-time point and certified
nonzero interval would be an additional witness feature supplied by the
draft's mathematical algorithm, not a feature observed in the Python API.

The existing defaults are finite guards. Complete mathematical termination
uses `max_cells=None` and `max_terms=None`. Budget exhaustion returns
`unknown`, never equality. The implementation's term guard is checked at
completed transitions; it is not an operating-system time or memory limit.

## Derived application corollary

**Hand-derived, no implementation or independent acceptance claimed.**

Let two supplied finite dated binary population networks have the same
sampled labels, one sampled gene per distinct contemporaneous leaf at age zero
in the same calendar origin, positive
constant pair rates on every population edge and on the unbounded ancestral
population, instantaneous mode-correct INDEPENDENT or COMMON inheritance,
and strict chronological edges. Suppose every age, rate and inheritance
probability is an effectively encoded real-algebraic number, with strict
positivity and complementary probabilities verified exactly.

Then equality of their complete rooted labeled calendar-metric genealogy
laws is decidable by a terminating exact algorithm. A negative answer can
include a ranked history, a nonempty open calendar cell, a rational tuple of
strictly ordered merger times in that cell and a certified interval excluding
zero for the difference of their cell densities at that tuple.

**Proof.** Exact algebraic ordering constructs the finite common calendar
partition. The retained finite state/history enumeration and event updates
use algebraic sums and products, so every emitted coefficient, intercept
and slope remains algebraic. Apply local Theorem 1 to the density difference
on an interior rational box of each cell. Full tuple cancellation decides
identity; a nonidentity yields the stated witness. Full law equality is
equivalent to identity on all these cells because they cover the law up to
the null events just justified. All enumerations are finite for the two
given input networks. No uniform graph-size bound is used. QED.

At a nonzero witness point, continuity implies an open set of nonzero density
difference, hence a genuine law difference; disagreement of isolated density
values alone would not justify that conclusion for arbitrary densities.

This extension supplies the arithmetic step for algebraic **supplied**
states. It does not decide existence over arbitrary real parameters, search
all finite graph sizes with a terminating NO answer, compare all nonalgebraic
competitors, establish empirical observations, or adopt a broader model.

## Transfer obligations that remain separate

| Proposed transfer | Exact obligation or boundary |
|---|---|
| Rational source API to algebraic source API | Supply effective algebraic representations, equality/order and arithmetic in every validation/key operation; preserve all history/route/cell semantics. The corollary is mathematical; `Fraction` code remains rational-only. |
| Arbitrary symbolic density compiler to Theorem 1 | Prove that every output has finitely many `P exp(Q)` terms with real-algebraic polynomial data, with a complete chart/reference-measure cover. Numeric approximations to arbitrary reals are not admissible exact coefficients. |
| Matrix-exponential formula to Theorem 1 | Justify a real exponential-polynomial expansion, including repeated eigenvalues and all polynomial Jordan factors, and encode its constants effectively. Merely knowing a finite matrix exists proves analyticity, not this real-exponential grammar. A general real matrix can have nonreal eigenvalues. |
| Retained full genealogy compiler to a marginal-time CTMC implementation | The retained compiler lists all gene mergers and directly multiplies survival terms, so it needs no spectral reduction. A different compiler integrating unobserved transitions needs a separate correctness argument. For a pure-coalescence epoch, ordering by lineage count makes its generator triangular with real nonpositive algebraic diagonal; this suggests a suitable Jordan expansion, but that expansion is not implemented or verified here. |
| Boundary/deterministic/singular observations | Show either that their mass is zero under the exact model or explicitly compile every atom and singular stratum. Use common injective charts and one justified reference measure; include chart-density/Jacobian effects. If substitution/Jacobians leave the grammar, prove an additional reduction. An ambient open-box test alone cannot compare singular laws. |
| Unknown parameters at fixed template | Supply a finite formula for the required equality/feasibility predicate with one shared admitted physical tuple. Polynomial-time exponents do not make arbitrary exponential feasibility an unconditional real-closed-field decision problem. The draft's unrestricted logical extension remains conditional. |
| Unknown finite source size | Supply source-specific finite presentation, positive/negative certificate coverage or a computable complete bound. A terminating two-supplied-state comparator provides none of those conclusions. |
| Canonical biological admission | Request and establish the exact source validation, not just positive probabilities or an arithmetic identity. The checker default allows broader dated binary DAGs; current master hypotheses and owners remain controlling. |
| Main-paper insertion | Obtain Dot's exact manuscript pin, intended grammar/predicate/domain and owner instruction. None has been confirmed by this audit. |

The broader logical boundary is already preserved in
[EXPONENTIAL-PROOF-CERTIFICATES-AND-SOURCE-COVERAGE.md](https://github.com/Sodelin/Research-Commons/blob/c3f9e5b60e83719902da8636dfa0fd208a2d41b4/research/2026-10-09-dot-full-attempt-wave-0542z/g3-certificates/EXPONENTIAL-PROOF-CERTIFICATES-AND-SOURCE-COVERAGE.md)
(Git blob `a11bff90e34a97ef59af0c85816aecc30484804d`). Even a granted
real-exponential truth decision does not supply the missing source-specific
separator/coverage theorem. No rediscovery or completion of general G3/G4
is claimed.

## Evidence level and current coordination boundary

**Observed:** authenticated source reading, exact file hashes, the retained
algorithm bodies, historical recorded controls, and the citation's 404.
**Hand-derived:** the algebraic-parameter corollary, count of enumerated
history/cell pairs and the application of the draft's identity theorem.
**Unverified:** historical novelty, independent acceptance of this extension,
an algebraic implementation, new solver outcomes and Dot's paper binding.

The retained `checks.json` records 3276 completed metric-equality cells,
three exact inequality controls, two hand density controls and ten input or
budget guards. Those are the original author's historical execution records,
not new runs performed by this audit. No compiler, SMT query, Lean build,
numerical job or service/device change was performed here.

The current [dot checkpoint](https://github.com/Sodelin/Research-Commons/issues/1#issuecomment-6190661206)
recognizes a separately authorized bounded SMT evaluation and preserves
general G3, finite legal-INDEPENDENT G4, shared physical parameters and
compiler ownership/HOLD. Current runtime/source ownership is separately
recorded in [the integration-owner reply](https://github.com/Sodelin/Research-Commons/issues/1#issuecomment-6190437171).
This local read-only audit changes none of those permissions or selections.
No Commons mutation or peer message was sent by this subagent.
