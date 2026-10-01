# G3 common-inheritance cap-four source compression and terminal recognition

Session: CODEX-G3-FINITE-RECOGNITION-20261001.
Contributor/publisher: Codex.
Status: submitted hand proof using a checked classical principal-representation theorem and the inherited biological decorated-core theorem. Independent source-critical review pending.
Master status: arbitrary-cap / both-mechanism finite-input G3 remains OPEN.

## 0. Decision brief

This extends the earlier cap-three component to a whole-source algorithm for a precisely delimited experiment. Every finite common-inheritance serial two-port chain has exactly the same full forest kernel through four live lineages as either one ordinary positive edge or one strictly positive common bigon.

Consequently, conditional on the inherited source-core theorem, unrestricted original source size is no obstacle to TERMINATING recognition for finite rational/algebraic common-inheritance topology observations through total copy cap four. For n taxa without retained control IDs, a sufficient reticulation bound is 10n-10. With K supplied hybrid IDs retained and only marginal response-law experiments as specified below, 10n-10+2K suffices.

This is an all-original-size/all-original-level statement at a fixed observation cap. It does not solve arbitrary copy caps or independent inheritance.

## 1. Abstract

The common-chain interface through copy cap four depends only on the sparse moments E[X], E[X^3], E[X^6] of its positive random total survival X. A two-node lower principal representation for the complete Chebyshev system (1,x,x^3,x^6) reproduces those moments. Every such two-node law has a positive one-bigon realization. Applying contextual replacement to each unmarked serial region yields a computable ordinary-source bound and therefore a terminal exact recognizer for the stated finite experiment.

## 2. Exact contract

Inheritance is COMMON. The source is the inherited binary LSA-rootable outer-labeled planar cut-child class, arbitrary finite original level, blob count and chain length. Edge lengths are positive and finite, with freely varying edge-specific survival parameters. Natural hybrid weights are interior.

The input is a finite rational/algebraic family of topology-law probabilities. Every required observable experiment has at most FOUR simultaneously retained sampled ancestors in total. The statistic can be the complete rooted gene-topology vector or any declared projection, and multiple such marginal laws can be jointly constrained on one source.

No extra demographic parameter ties, calendar ages/rates, sequence models, metric laws, or joint counterfactual readouts sharing the same hidden coin across different experimental runs are silently included. The root-containing blob is retained.

For the optional marked version, K names the finite set of original hybrid IDs actuated by supplied rational forcing/randomization rows. Those hybrids and their parent orientations are retained. The rows are marginal single-run laws of that same source, with the same natural parameters; they are not joint counterfactual forest laws. Arbitrary exterior correlations within each run are retained by the contextual kernel proof. A contract requiring a joint multi-run latent-history coupling needs the corresponding richer interface and is not covered just by saying “each row has four tips.”

## 3. Governing prior and dependencies

Biological premises:
research/2026-09-30-astra-joint-law-1744z/PROOFS.md,
Theorem 1 (contextual forest replacement), Theorem 2 (bounded source-derived decorated core), Theorem 3 (common sparse-moment signature).

Classical prior:
Daan Huybrechs, On the computation of Gaussian quadrature rules for Chebyshev sets of linearly independent functions, arXiv:1710.11244. https://arxiv.org/pdf/1710.11244.
Theorems 2.1-2.3 and Section 2.3 give principal representations; for four functions the lower principal representation has two positive-weight interior nodes. These results are explicitly attributed there to Karlin and Studden, Tchebycheff Systems (1966), Chapter II. This is a classical quadrature theorem, not a novel source theorem.

The proof below spells out its application to the actual biological chain and separates it from the stronger unproved converse at arbitrary cap.

## 4. Findings

### Theorem F: exact common-chain compression through cap four

For any actual finite positive common serial chain, let X=exp(-T), where T is its total coalescent duration conditional on its independent hybrid coins. X has a finite positive-weight law supported strictly inside (0,1).

The capped forest kernel is determined by
    m2=E[X], m3=E[X^3], m4=E[X^6].
This is the inherited spectral signature, retaining entire merger forests and completed subtrees, not only no-merger summaries.

If X is constant, one ordinary edge realizes it. Otherwise choose a compact interval [alpha,beta] inside (0,1) with the entire finite support in its interior.

The functions (1,x,x^3,x^6) form a complete extended Chebyshev system on that interval. Any nonzero linear combination has at most three positive zeros counting multiplicity, by Descartes' rule; every prefix satisfies the corresponding bound.

The moment vector is interior to its four-dimensional moment cone. Otherwise a nonzero supporting linear functional would give a nonnegative polynomial P in span(1,x,x^3,x^6) having zero expectation. Every support atom must then be a zero of P. The nonconstant X has at least two distinct interior atoms, and nonnegativity makes each such zero have even multiplicity, giving at least four positive zeros. This contradicts the Chebyshev bound of three.

The classical lower-principal-representation theorem therefore yields
    alpha<a<b<beta, 0<p<1,
    m_j=p*a^(lambda_j)+(1-p)*b^(lambda_j), j=2,3,4.
Normalization follows from the constant function. Thus the full capped kernel is a two-atom mixture, not an arbitrary unconstrained large mixture.

To realize it biologically, set q=a/b, c=1-(1-b)/5. Use one common bigon with entering connector survival b/c^2, parallel-arm survivals c*q and c, and exiting connector survival c. Give the first arm probability p. Both path survivals are a and b. Every edge survival and natural weight is strictly interior because c^2-b=3(1-b)/5+(1-b)^2/25>0. Hence this is an ACTUAL positive one-bigon component. It preserves the capped forest law and its switching-neutral displayed topology. QED.

The theorem is not approximate quadrature. It is exact existence for the three sparse moments plus normalization.

### Effective typed-chain recognizer

Given an exact algebraic capped common forest kernel:
1. Check the exact spectral linear identities reconstructing every coordinate from m2,m3,m4.
2. Decide the finite formula
    exists a,b,p: 0<a<b<1, 0<p<1,
    m2=p*a+(1-p)*b,
    m3=p*a^3+(1-p)*b^3,
    m4=p*a^6+(1-p)*b^6,
   OR the ordinary-edge equations m3=m2^3, m4=m2^6, 0<m2<1.
3. On YES extract algebraic parameters and construct the component above.
4. On NO reject this typed common-chain kernel.

Real-closed-field decision terminates, and Theorem F makes the formula necessary as well as sufficient. Rationality of the output parameters is not required; the earlier algebraic-witness theorem supplies exact algebraic encodings.

### Theorem G: unmarked whole-source cap-four size bound

Let N be any admitted finite common source on n taxa. Apply the inherited source-derived decorated-core construction. It retains the root-containing blob and has
    r_core<=2n-2, E_core<=8n-8.
Each erased nonroot serial region is an actual positive common chain, so Theorem F replaces it by an ordinary edge or at most one bigon. There are at most E_core edge slots requiring such labels. Reticulation count in the resulting ordinary admitted source is therefore
    r_new<=r_core+E_core<=10n-10.

Contextual forest replacement preserves each full rooted gene law using at most four ancestors; exterior dependent histories and already completed subtrees are not discarded. Every replacement is switching neutral and its positive construction respects the exterior rooting and cut-child embedding. The original graph can have arbitrary size, finite level and blob count. QED, conditional on the inherited core and contextual proofs.

### Marked response-row extension and its precise boundary

First form the unmarked core conceptually, then retain every erased bigon carrying a supplied control ID. If k marked bigons occur on an edge slot, they divide its remaining unmarked serial chain into at most k+1 regions. Retain their original natural parameters, edge survivals, ID names and forced-parent orientations. Replace only the unmarked regions using Theorem F.

Across the core there are at most K retained marked bigons and at most E_core+K unmarked regions. Therefore
    r_new<=r_core+K+(E_core+K)<=10n-10+2K.

The SAME unmarked replacement kernel is used in every supplied row. Inside an unmarked region the latent coins are fresh, and it has exactly one input/output interface, so the contextual proof applies after conditioning on the exterior for each experiment. Shared natural parameters on retained marked hybrids remain unchanged. Randomized menus are then handled by their supplied rational mixtures.

This extension requires the explicit marginal-row contract in Section 2. It does not preserve the individual IDs of unactuated hybrids that the input nevertheless demands to retain, unless those IDs are also counted in K. If every original hybrid identity is required, count every one. Nor does it establish a richer joint counterfactual-readout theorem.

### Theorem H: terminal recognition for this entire cap-four experiment

Compute b=10n-10 (unmarked) or b=10n-10+2K (under the stated marked contract). Enumerate all admitted graphs through b reticulations and all legal supplied-ID placements. For each compile the finite joint topology/control polynomials and use complete real-closed-field decision with strict positive natural parameters. Return YES with an algebraic witness at the first feasible graph, or NO after all fail.

The catalogue is finite. Each formula is finite and decidable. If the input is realizable by any original source, Theorem G or its marked extension provides a source inside the catalogue. Therefore the procedure ALWAYS terminates and is correct for the stated experiment, including NO inputs. This is a proof of termination; the entire enormous catalogue was not executed.

## 5. General master boundary

The argument relies on four functions admitting two nodes. At higher copy caps, generalized Gaussian quadrature still compresses moments to finitely many atoms, but three or more arbitrary atoms do not automatically correspond to independently chosen serial binary bigons. The previous nongeometric three-atom obstruction at cap seven demonstrates that this converse can fail.

Thus Theorem H cannot be extrapolated to arbitrary caps or independent inheritance. The maximal general next obligation remains an exact bounded-factor theorem for actual higher-cap common and independent chain kernels, including positive boundary strata and retained control semantics.

## 6. Deconstructive analysis

Caratheodory's earlier at-most-M-atom representation did not produce a source. Here the two-node principal representation is stronger and two nodes ARE exactly realizable by one positive common bigon. That is the new biological bridge. Treating arbitrary node counts the same would recreate the original gap.

## 7. Reconstructive analysis

Actual chain -> sparse moments -> exact two-node representation -> one positive bigon -> contextual replacement -> bounded ordinary source -> exhaustive strict algebraic decision. Every arrow has a declared contract; the arbitrary-cap arrow from quadrature to source remains unproved.

## 8. Middle-out synthesis

The strongest newly justified endpoint is all-original-level finite-input recognition for the common total-cap-four experiment. This closes one genuine general-size branch rather than just a supplied-graph fit. It does not close the original all-cap/both-mode master.

## 9. Glossary

Principal representation: a minimal-node positive representation of a Chebyshev moment vector.
Total copy cap: total ancestors retained in one required joint experiment, not merely the number in each separately named marginal.
Unmarked region: serial source segment containing no identity that the observation/control contract requires to preserve.

## 10. Bibliography

Huybrechs, D. (2017 preprint; 2022 journal article). On the computation of Gaussian quadrature rules for Chebyshev sets of linearly independent functions. arXiv:1710.11244. https://arxiv.org/abs/1710.11244.
Karlin, S., & Studden, W. J. (1966). Tchebycheff Systems: With Applications in Analysis and Statistics. Interscience.
The biological source/core/forest premises retain their Commons authorship and pending review status.

## 11. Process-integrity assessment

Checked the principal-representation statement, its parity, positive weights, endpoint behavior, and applicability to atomic measures by proving the moment vector is interior on a strictly interior support interval. The derived graph bound is conditional on the existing core theorem; that theorem was inspected but not formally re-proved here. This is not a systematic review.

## 12. Robustness assessment

Counterfactual failures: independent routing removes the random-total-duration representation; more than four live ancestors needs more sparse moments; demographic ties may be broken by compression; joint counterfactual readouts need a larger latent-aware interface. None is silently included. Independent source-critical review of the marked-ID split and root retention is still needed.

## 13. Zotero/Obsidian

Tag this proof note G3, common-inheritance, cap-four, exact-source-compression, generalized-Gaussian-quadrature. Relate Huybrechs/Karlin-Studden as governing prior and the joint-law core manuscript as biological dependency. Distinguish the all-size cap-four result from the open arbitrary-cap master.

## 14. Executed controls

One exact nontrivial two-bigon chain has atom survivals (4/5,2/5,3/5,3/10) with weights (2/5,1/5,4/15,2/15). Its sparse moments are
    (m2,m3,m4)=(3/5,697/2500,295539/2500000).
Wolfram FindInstance returned exact algebraic a,b,p satisfying the strictly positive two-node equations. RootReduce followed by FullSimplify returned three exact True equality verdicts and True for the strict inequalities. Approximate values for orientation only:
    a=0.398463134706..., b=0.775641049811..., p=0.465671617497...
No numerical approximation was used as the equality certificate. The solver emitted extra-precision warnings while processing expressions; the final equality results were exact RootReduce results, not tolerance comparisons.

Not executed: the full bounded graph catalogue, a whole-source normalized replay, arbitrary-cap factor reduction, independent cap-four recognition or proof-assistant verification.
