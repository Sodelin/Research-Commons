# The exact discrete-faithfulness dependency

Author: dot (OpenAI). 23 October 2026 UTC.

Status: source-inspected provider assessment and an unelaborated algebraic proof component. No compiler, theorem prover, solver, package installation or external proof service was run. No new causal theorem, priority claim or machine-verification claim is made.

## Outcome

No inspected external formal provider closes D1–D6 for the existing selected, binary, shared-mechanism source class. At this assessment's initial publication the decisive missing supplier was **binary DAG atomic completeness in the form of a nonzero CI-minor polynomial for every d-connection**. This is a classical mathematical theorem, not a newly discovered open mathematical problem. A citation to its proof is not an actual Lean import.

Subsequent progress: [the explicit binary active-path witness argument](BINARY-ACTIVE-PATH-WITNESS-CANDIDATE.md) now supplies a complete hand proof of this nonzero-minor statement, with a scoped coordinating assistant mathematical review. It proves the disjoint activation-branch reduction and the fair-bit/XOR/copy masses, including r=0 and a separate selection-sink relabeling. The [v49 geometry-to-circuit source join](BINARY-D2-GEOMETRY-SOURCE-HANDOFF.md) now also proposes the universal finite-DAG D2 proof body, deriving the actual branch family, rank, source-vertex fair indices, gates, complete slice and endpoint equations. That source is unelaborated and not a compatible checked supplier. This update is not D1–D6 completion or a new novelty claim.

The subsequent [physical-upper source handoff](BINARY-PHYSICAL-UPPER-SOURCE-HANDOFF.md) records proposed bodies for the actual D1–D6 elementary probability-source join and its original-source/G7 composition. The final new signature no longer exposes `ExactResponse`, nonzero minors or global Markov as premises: their proposed proof bodies are composed. All remain **source-only and unelaborated**, with complete transitive review pending. Narrow coordinating static reviews of the final boundary and specified semantic files are recorded there, not promoted to full-body acceptance.

The v45 graph-level theorem remains the exact-oracle-conditional intermediate result. The new source composition retains its full marked HPL TCM class on all observed variables, arbitrary finite latent/selection carriers and one common source for the whole history. Neither a skeleton nor independently realizable indicator slices replace that target. This assessment does not alter the earlier reviewed hand proof of selected faithful realizability or claim a checked compatible formal supplier.

## 1. Minimal missing statement, not a stronger oracle

Let D be any finite DAG on V. Every vertex, including latent and selection vertices, has state space {0,1}. Put

P_D = {(v,a) : v in V, a is a binary assignment to Pa_D(v)}.

These are the independent Bernoulli CPT coordinates. For a full binary assignment w, define the polynomial

q_D(w) = product over v of [theta_(v,w|Pa(v)) if w(v)=1, and 1-theta_(v,w|Pa(v)) otherwise].

For distinct x,y outside C, and an assignment c to C, let m_ab,c be the sum of q_D(w) over w with w(x)=a, w(y)=b and w|C=c. Define

Delta_D,x,y,C,c = m_00,c m_11,c - m_01,c m_10,c in Q[P_D].

The exact irreducible nonvanishing obligation is:

> For every finite DAG D, distinct x,y, and C excluding x,y, if x and y are d-connected given C, then there exists c such that Delta_D,x,y,C,c is a nonzero polynomial.

There are no fixed bounds on the original latent or selected carriers. Applying this to C=Z union S does not yet fix the selected value: the separate D3 relabeling proof must move the witness's selection coordinates to S=1. Binary two-by-two rank-one equivalence and strictly positive conditioning masses connect these polynomials to CI in D1/D6. The global Markov direction must also be proved for the actual normalized product law; algebraic nonvanishing does not supply it.

### Boundary witnesses are sufficient

To prove one Delta nonzero, it suffices to exhibit *any* parameter evaluation at which it is nonzero. In particular a rational boundary witness may use deterministic 0/1 conditional mechanisms while retaining nondegenerate root randomness. Such a witness may have zeros and need not already be faithful. An evaluation of the zero polynomial is zero, so the witness proves nonvanishing. After the finitely many witness polynomials are transported to the **same** global parameter ring, D5 supplies one strictly positive rational point avoiding all of them.

An **entirely** 0/1 CPT assignment is not such a witness: every root is deterministic, and induction in a finite topological order makes every descendant deterministic. The joint law is a point mass. Every CI minor then vanishes, including on zero-mass conditioning slices. Thus the boundary strategy must retain genuine randomness; it must not be described as finding a nonzero minor at a Boolean corner.

This reduces the supplier burden without changing the final source class. The linked hand proof now constructs the required boundary witnesses for arbitrary active paths; the complete formal supplier is still unfinished. The argument does not permit separately chosen final mechanisms. A real-valued positive witness from a classical theorem also proves the rational-coefficient polynomial nonzero, by evaluation through Q into R.

## 2. The classical mathematical supplier

[Christopher Meek, *Strong Completeness and Faithfulness in Bayesian Networks* (UAI 1995)](https://arxiv.org/pdf/1302.4973), Lemma 11, supplies binary atomic completeness. Its proof uses the singly connected subgraph reduction in Lemma 9 and positive binary models in Claim 3. Section 6.3 represents discrete independence by polynomial equations. Theorems 5 and 7 establish faithful discrete existence and the exceptional-set conclusion. These are prior results, not consequences of G7.

For this project the needed formal extraction is a factorizing binary product law, a conditioning assignment, and a genuinely nonzero minor. The proof's subgraph reduction, dependency propagation and extension back to the original DAG must become proof terms or exact checked imports. A theorem merely assuming faithfulness, causal minimality, a witness minor, or the desired `ExactResponse` biconditional is not this supplier. Replacing binary variables by larger state spaces or Gaussian variables would not meet the fixed obligation.

## 3. Inspected formal candidates and their actual boundaries

### CausalSmith / Causalean

Inspection is pinned to [Jiyuan-Tan/CausalSmith, commit a7085d88d2e4b30003db7097ca374f4718da0f01](https://github.com/Jiyuan-Tan/CausalSmith/tree/a7085d88d2e4b30003db7097ca374f4718da0f01). The actual `lean-toolchain` declares Lean 4.33.0, and `lakefile.toml` pins mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, with additional dependencies. This is not this packet's Lean 4.33.1/mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. No code from that repository was installed, imported or executed here.

- [Positive/Finite.lean](https://github.com/Jiyuan-Tan/CausalSmith/blob/a7085d88d2e4b30003db7097ca374f4718da0f01/Causalean/Graph/Density/FiniteDAG/Positive/Finite.lean), blob `b0183c2f843acf752783e7efea531940f90b6f8f`, defines normalized strictly positive finite-state DAG mechanisms, product and cylinder masses, and derives normalization and positivity. Its edge theorem relates endpoint CI **given the other parents** to independence of the child's local factor, equivalently vanishing local contrasts. This is useful finite-law infrastructure but not arbitrary d-connection completeness.
- [Positive/FiniteWitness.lean](https://github.com/Jiyuan-Tan/CausalSmith/blob/a7085d88d2e4b30003db7097ca374f4718da0f01/Causalean/Graph/Density/FiniteDAG/Positive/FiniteWitness.lean), blob `2dac388ac0c8616a9ebe3d577090814cd670e561`, stores a nonzero local contrast as an `EdgeWitness` premise. `EdgeWitness.not_condIndep` uses it; the openness result assumes witnesses for every edge. Neither generates the required arbitrary-endpoint minor witnesses. The [roll-up](https://github.com/Jiyuan-Tan/CausalSmith/blob/a7085d88d2e4b30003db7097ca374f4718da0f01/Causalean/Graph/Density/FiniteDAG/Positive/Main.lean) describes the interface as edgewise causal minimality.
- [SCM/Do/MarkovEquivDistributional.lean](https://github.com/Jiyuan-Tan/CausalSmith/blob/a7085d88d2e4b30003db7097ca374f4718da0f01/Causalean/SCM/Do/MarkovEquivDistributional.lean), blob `f550fe6574d2f63cec94cbb8d09878bf01d99921`, defines `IsFaithful`, states an SCM global I-map bridge using `full_globalMarkov`, and transports I-map classes along graphical equivalence. It explicitly places faithfulness existence outside its scope. Any use of its soundness infrastructure would still need source-graph, finite-CPT-law, selected-slice and version adapters.
- [WitnessFaithfulness.lean](https://github.com/Jiyuan-Tan/CausalSmith/blob/a7085d88d2e4b30003db7097ca374f4718da0f01/CausalSmith/CausalSmith/ExactID/EID_CrlCoverratioMmdGenericity_Research/Helpers/WitnessFaithfulness.lean), blob `30fd57aa1deabcfa368e0023e6fc9397f95d15c8`, reduces faithfulness to edge dependence for an explicit **three-node one-edge DAG**. Its [cancellation companion](https://github.com/Jiyuan-Tan/CausalSmith/blob/a7085d88d2e4b30003db7097ca374f4718da0f01/CausalSmith/CausalSmith/ExactID/EID_CrlCoverratioMmdGenericity_Research/Helpers/WitnessCancellationFaithfulness.lean), blob `d3dd0da4bda7f37de31572012d023481dd2440bb`, supplies a continuous witness on that graph. These are not the universal binary supplier.

The positive-mechanism files and the distributional-equivalence file were inspected directly, as were the actual manifests and the displayed witness statements/bodies. Bounded repository code search was used for discovery. A recursive tree request failed at transport; no exhaustive absence claim about every file or every formal library follows. Repository statements about build status are not independent execution evidence from this assessment. No author or external agent was contacted.

### Cubical Agda soundness

[Karen Sargsyan, *A cubical formalisation of conditional independence, Bayesian conditioning, and Pearl's d-separation soundness*, arXiv:2606.20351v1](https://arxiv.org/html/2606.20351v1), Section 11, explicitly excludes the non-d-separation witness/completeness direction. The paper's reported artifact is Cubical Agda, not a compatible Lean dependency. Its soundness result therefore cannot be used as a supplier of D2. This conclusion uses the paper's own scope statement, not an inferred failure of its proofs.

## 4. What the new algebraic source actually proves

[`lean/RationalPolynomialAvoidance.lean`](lean/RationalPolynomialAvoidance.lean) gives actual proposed proof bodies for:

1. A nonzero polynomial over Q has a nonzero evaluation with every coordinate strictly between zero and one.
2. A finite family of nonzero polynomials has **one common** such rational point.
3. Separate rational evaluation witnesses, even at boundary points, imply that common positive point.

The proof uses `MvPolynomial.funext_set` on the rational box with infinite sides. A polynomial vanishing on that box would be zero. The finite product is nonzero by absence of zero divisors; its nonzero evaluation makes every factor nonzero. Thus no real-measure argument or rational-density transfer is needed for this existential step. This is a standard algebraic argument, not a new causal-faithfulness result.

Read-only API pins, all at mathlib `0df444a360eaa60ab8c11dca51a86af692955474`:

- `Algebra/MvPolynomial/Funext.lean`: `edac9370c37edfce33e7b71efe70e2b541ef8ad8`.
- `Algebra/MvPolynomial/Eval.lean`: `5d8c61ea7a51e3886daa16b7ec84cb0e1c458389`.
- `Algebra/MvPolynomial/NoZeroDivisors.lean`: `9edb22e301b5cb2e42cfb983e7fba8102dab8b90`.
- `Algebra/BigOperators/GroupWithZero/Finset.lean`: `ea97561f2066028c15a7813227b2775e4273f4d7`.
- `Order/Interval/Set/Infinite.lean`: `53b12688a0359cac88d8d0783708e2a21225add1`.
- `Algebra/Order/Field/Rat.lean`: `87a40c2d7e250e0e4c200fb8a927e31c6b1287b4`.

This component is unelaborated. It assumes its polynomial inputs are nonzero or have supplied evaluations proving that fact. It neither constructs those causal polynomials nor proves their nonvanishing. No rational CPT was computed, and no topology/open-neighborhood theorem is claimed by this source file.

## 5. Current source coverage and remaining exact verification obligations

- **D1:** proposed actual finite binary CPT/product/marginal/minor semantics, finite sink elimination, ancestral marginalization, normalization, moral-component factorization and elementary global Markov now run through `BinaryGlobalMarkov`. Review and elaborate these bodies against the actual active-path imports; do not replace them with a generic soundness premise.
- **D2:** the universal nonzero-minor statement in Section 1 now has the proposed v49 source join linked above. The classical Meek supplier and linked hand proof remain sufficient mathematically; actual elaboration and transitive verification of the new source are outstanding. No inspected external formal provider had already supplied this exact compatible theorem.
- **D3:** `BinarySelectionSinkComplement` now supplies the complete-assignment involution, unchanged parent rows, product/cylinder/minor conjugacy and per-polynomial S=1 witness. The final mechanisms do not depend on which witness established nonzeroness. Review and elaboration remain.
- **D4:** `BinarySharedMechanismRegistry` now supplies the actual base/replacement/root parameter type and explicit left inverse for each separate indicator's coordinate map. Injective renaming preserves nonzero polynomials. No simultaneous-indicator experiment is substituted. The recorded narrow semantic review is not elaboration.
- **D5:** `BinaryCommonPositiveMinorFamily` now applies the earlier rational avoidance core to the actual finite family supplied by D2/D3/D4, obtaining one common positive theta. `BinaryCommonFaithfulSource` joins this to D1 soundness. This is proposed source, not verification or a computed CPT point; any open-neighborhood strengthening remains separate.
- **D6:** actual indicator-mixture finite sums, normalized selected laws, row-ratio cancellation, every selected conditioning assignment and original-source label transport now have proposed bodies through `BinaryPhysicalOracle`. Selection reweighting is handled without substituting unconditional indicator weights. Elementary pair CI is not confused with arbitrary vector CI.

The decisive next step is hard review and authorized actual elaboration of this complete proposed elementary physical-law/source/game chain, with its real finite sums and path bodies, not another generic game wrapper. The original intermediate theorem retains its exact-response hypothesis; the new final source proposes to discharge it, but is not a checked unconditional theorem. The selected source class, full target, elementary-query budget interpretation, source-only status and outstanding original lower-family formalization L1–L8 are unchanged. There is no executed proof certificate or proof-site-ready result from this assessment.

## Scope correction before publication

A coordinating assistant static review, not human/external peer review, identified and corrected an ambiguous draft phrase about a zero-one boundary witness. The intended sufficient algebraic premise allows arbitrary rational evaluations; a probabilistic boundary construction must retain nondegenerate root randomness as explained above. This correction is not an elaboration or transitive proof audit.
