# Candidate acquisition of the full reachable epoch from partial entry support

Author: dot (OpenAI), 25 October 2026. Written composition candidate for review. The joint escape identity and the adaptation of the earlier positive-entry supplier are exposed separately below. No global unknown-history theorem, historical novelty, finite-data algorithm or formal verification is claimed.

## 1. Model and target

One positive-length constant epoch has finitely many demes D, strictly positive coalescence rates, and finite migration generator Q. Initial locations are independent draws from an unknown probability p with nonempty support S contained in D. States outside S may be reachable by migration. The input is the exact family of all finite-panel unmarked timed-genealogy laws, with any retained labelled main/reporting blocks kept jointly. There is no hidden-state preparation.

The target is the restriction of Q and the coalescence rates to the set reachable from S during this epoch, up to a common permutation, together with coherent initial-location response laws. Demes unreachable during this epoch cannot be identified from these observations and are not called globally irrelevant if a later boundary could activate them.

## 2. Required support-only version of the reviewed local supplier

Claimed adaptation: from product entry supported on S, the earlier star/multistar methods recover |S|, the entry/rate pairs on S, the off-diagonal entries Q_ij for i,j in S, and the full joint response family from every finite tuple of active states. One common residual permutation mixture H of S is retained. It preserves the selected entry/rate marks and the selected within-S off-diagonal migration matrix. It need not yet preserve unknown migration to D minus S, and the diagonals of Q are not yet identified in that frame.

Here are the exact changes requiring review, rather than an invocation of the old full-support statement:

1. The initial star moments contain only S. The b_k formula in ZERO-ENTRY-BOUNDARY-EXTENSION.md counts the multiplicities of positive x_i=p_i lambda_i, hence |S|, without assuming that sum_(i in S)(pQ)_i is zero.
2. In every multistar derivative of total order r, use interpolation sizes k_j>r. No group can end wholly in an initially unoccupied state: that would require at least k_j migrations. Thus the terminal assignment bases remain x_i for i in S only.
3. Initial configurations with a zero-entry lineage have weight zero and are omitted; no division by a zero p_i is performed. Migration paths may pass through outside states, but every such nonzero-migration term still loses at least one degree under the prior count-path bound. Only zero-migration paths yield the top degree 2r. The positive rate-marked partition measure is therefore exactly the active-state one, with the same arbitrary joint future-response factor F.
4. The positive partition preparation covers each member of S, not each member of D. The one-migration directional triad probes between prepared active states identify Q_ij for i,j in S; a route through an outside state takes an extra migration and cannot enter their leading coefficient.
5. For a fixed-calendar future cylinder F, the terminal response can depend on the shrinking first wait t. Its h-th time derivative contributes a generator derivative of order r-h, hence group-size degree at most 2(r-h). For h>0 this is strictly below 2r. Thus the top-degree extraction retains the actual positive response R(0;F), not a signed leading derivative of a future response. Differentiability follows by propagation inside the initial constant epoch to a fixed positive time before the first constraint in F. The same argument applies with finitely many retained reporters.
6. The same finite-orbit mixed-probe selection conditions the active matrix once for all main tuples and F. It leaves one source-faithful H mixture acting on active names while the actual unobserved remainder of the source is retained. No unknown outside generator or tensor factorization is inferred from this step.

The mathematical work inherited here is the explicit legal multistar supplier, not merely a formal matrix inversion. Each listed modification is necessary for the present extension.

## 3. Observable total leakage without identifying every exit coordinate

For an active class i, the joint escape operator E_i of JOINT-ESCAPE-RESPONSE-OPERATOR.md has constant-test value E_i(1). In an individual physical frame this is total departure a_i=sum_(j!=i)q_ij. If H does not preserve a_i, the extracted value is its H average; do not select a favourable alignment separately for each i.

The SUM

    A = sum_(i in S) E_i(1)

is nevertheless exactly sum_(i in S) a_i, because H permutes S. The known within-support off-diagonal matrix supplies

    B = sum_(i,j in S, i!=j) q_ij.

Thus L=A-B is exactly the nonnegative total leakage

    L=sum_(i in S,j outside S)q_ij.

L=0 if and only if every migration edge leaving S has rate zero. This uses positivity, not an assumed rank test. In that case S is closed, the known internal off-diagonal matrix supplies its diagonals by row sums, and it is the full generator relevant to the initial entry.

## 4. Invariant support-expanding product entry

Fix any known kappa>0 in inverse-time units. For each of n designated output lineages, sum over its initial active class i the operation kappa times identity plus the unnormalized escape operator E_i. Keep all other output groups and any main/reporting blocks as joint main coordinates while applying each operation. Normalize the resulting n-lineage response by

    Z^n, where Z=kappa |S|+A>0.

The operator lemma proves pointwise in a physical source frame that the weights are products of the one-coordinate weights. The resulting initial distribution in that physical frame is therefore the product of

    p_new(j) = [kappa 1_(j in S) + sum_(i in S,i!=j)q_ij] / Z.

No unknown location is physically selected. The operation is a finite linear combination of legal derivative/density functionals acquired from the joint response family. Its source representation is positive and normalized.

The formula is INVARIANT under the residual active-name permutation: summing over all i in S removes the frame dependence, and Z is the same in every frame. Hence mixing over H does not introduce correlations into this new entry. The same product p_new tensor ... tensor p_new occurs in every physical frame. This is the step that would fail for arbitrary separately chosen or correlated routing mixtures; it follows here from the proved joint escape identity and the invariant sum.

The new support is exactly

    S_new = S union {j : q_ij>0 for some i in S}.

The kappa term preserves every old active state. If L>0, at least one new state is added. If L=0, no expansion is necessary.

## 5. Conditional finite-source saturation

Apply the support-only supplier of section 2 to this new virtual product-entry family, preserving every requested joint main/reporting test, and repeat sections 3–4. For each finite source, every nonterminal expansion strictly enlarges the physical support. Therefore after at most |Reach(S)|-|S| expansions, the support is closed and equals Reach(S). At the terminal stage the supplier's active matrix is the complete reachable generator, not just a principal off-diagonal submatrix.

This is a finite-source structural termination argument for an observation-supplier composition. It is NOT an arbitrary-input recognition algorithm: computing exact derivatives, inverting finite moment systems, and deciding L=0 from an abstract law representation have not been given a general effective input model. It supplies neither a source-independent finite sample cap nor a finite-data stopping rule. Under an explicitly admitted exact derivative/arithmetic/zero-test oracle, it describes a terminating promised-source procedure; those oracle abilities are not silently granted to DNA data or G3 inputs.

For equivalence arguments, the intended use is to apply the same observable construction to two promised finite sources with equal all-panel laws. They must have the same recovered active counts, invariant leakage values and virtual response laws at every stage. If one reaches L=0, so does the other. This is the proposed route to excluding extra reachable ghost states without an a priori bound on their number. The complete equivalence conclusion remains conditional on review of sections 2 and 4, not an already accepted new theorem.

## 6. Initial entry and retained reporters

The terminal virtual entry is not the original p. Preserve original labelled sample/reporting lineages as main blocks throughout the construction. At the terminal full-support stage, a prepared state i paired with an original-entry reporter has initial coalescence density p_i lambda_i, within the common source frame. Mixed reporter/prepared-block products recover the corresponding finite orbit and retain the same future alignment. This follows the existing typed-reporter boundary method; it must be carried jointly rather than inferring original p from the support-expanding distribution.

For several original taxon classes or a preceding routing matrix, keep the typed reporters and the already stored prefix symmetry. The present packet does not replace that bookkeeping with independent per-class alignments or declare the full multi-epoch induction complete.

## 7. Evidence and next review gate

The escape operator has 39 exact row-generator controls plus three normalization controls. The separate escape-moment extrapolation has 12 controls, including indirect ghost reachability. These do not execute the all-stage saturation algorithm. The support-only multistar adaptation and common-frame composition are written arguments awaiting scoped review.

The next mathematical check is precisely whether section 2's finite exponential-polynomial extraction and section 4's joint nesting retain every claimed positive response family under one source. No additional generic graph reconstruction, abstract realization or tensor theorem is invoked without an observable adapter. Prior no-migration alignment and classical finite positive-moment/orbit methods are reused, not claimed as new general principles.

## 8. Additional bounded execution, 25 October 11:34 UTC

check_support_saturation.py was executed after this candidate was written. With p=(1/2,1/2,0), active rates (2,2), outside rate 7 and nonzero outward/return migration, orders r=1,...,4 give the predicted active-only top coefficients -1,1,-1,1 using samples through 13. This tests the support-only coefficient extension, not the entire multistar extraction.

A separate four-state migration example starts on support {0}. The exact leakage values along support expansion are 2,3,5,0, with supports {0}, {0,1}, {0,1,2}, {0,1,2,3}. At each stage, all permutations of the active labels were enumerated in a two-block joint expansion, and the resulting joint weights equal p_new tensor p_new exactly. This tests invariant averaging and positivity in a finite example; it is not an implementation of observational inversion, a general induction certificate or finite-data evidence. The unedited output is support-saturation-control.json, and the script exited zero.
