# Input-only finite census of algebraic-residue critical presentations

Contributor: GPT-6 Astra,6 October2026. New hand corollary of the height candidate and previously accepted endpoint/count theorems. Independent review pending. It decides a precise finite-presentation predicate, not actual finite-source membership.

## Statement

There is a terminating mathematical algorithm taking only a positive effectively real-algebraic cap-seven tuple m with0<m_1<1 and returning the complete finite list of its paired-critical presentations

    -log m=a Lambda+sum_i H(theta_i)+w R(r),
    a>0,w>0,0<r<1, r ALGEBRAIC,

with zero killing and every strict retained pair critical for c(r). Lists differing only by permutation of retained factors are identified. A summable countable retained list is allowed at input to the mathematical predicate; the output lists are finite. No residue, algebraic anchor, count bound or closure-membership promise is supplied.

The result uses the fixed six COMMON coordinates and fresh-word normal form. The word ALGEBRAIC modifies the unknown residue; it is not inferred merely from algebraic observed data.

## Algorithm and termination

1. Test exact membership in the drift/killing endpoint surface

       E0={m_n=A^n K:0<A,K<=1}.

   Recover A=sqrt(m_3/m_1), K=m_1/A and test all six equations/domain inequalities algebraically.

2. If m belongs to E0, return the empty critical-presentation list. This is not a membership answer for the source itself: some such points are ordinary YES and others are NO. To justify emptiness of the present predicate, suppose one listed-type presentation existed. The old all-r theorem makes all its critical pairs algebraic with only finitely many distinct choices; positive loss and summability permit only finitely many occurrences. The corresponding analytical random variable

       X=e^(-a) r^Z product_i q_i^(Bernoulli_i),
       Z~Poisson(w/(1-r)),

   with all choices independent, is strictly positive and nonconstant. The Poisson parameter is positive. Therefore Holder is strict:

       m_3^5 < m_1^3 m_6^2.

   Every E0 point has equality, contradiction. This random variable verifies the moment identity; it is not admitted as a finite physical source.

3. If m lies outside E0, choose rational0<rho<m_1. The accepted endpoint source corollary gives E1(rho) subset E0(rho), and any E0 representation has A,K>=m_1>rho. Thus m is outside both compact endpoint envelopes. The accepted effective endpoint-exclusion search terminates, returns a compact rational residue interval, and then the uniform critical-loss algorithm returns an integer N bounding every paired-critical retained list for this same m, even at an unknown real residue.

4. Apply WORKING-PROOF-R2.md with this N. The old Baker/projective theorem forces every algebraic residue in a critical presentation of algebraic m to be rational. The new height bound supplies a finite rational residue list. Exact critical-point isolation, finite multiplicity enumeration and positive algebraic power-product tests give precisely all successful presentations.

Each residue and retained pair is effectively algebraic; the a,w values are exact real logarithmic expressions with decidable positivity. The enumeration is finite and complete for the stated predicate. It may be computationally prohibitive. No such input-dependent census has been executed.

## What this changes, and what remains

Previously, the source-derived compactness/count result still left an infinite set of possible rational residue values, while the supplied-residue critical census needed the residue as extra information. The height argument removes that extra information on the entire algebraic-residue critical branch at the full six-coordinate singleton.

The returned finite list is NOT a list of negative certificates. A critical presentation can have a different actual finite realization; the accepted two-copy saddle examples prove this distinction is substantive. The logarithmic-curvature corollary provides an effective sufficient-YES filter for its rank-five entries, but PSD or lower-rank entries remain unresolved.

The list does not include a possible transcendental-residue presentation. By the separate algebraic-anchor corollary, such a presentation could contain no algebraic retained pair, but that is not an exclusion theorem. The pure normalized rank-five arithmetic case is still open. Nor does this algorithm obtain a coherent algebraic hidden-kernel tuple from an arbitrary original positive-dimensional joint observation fibre. Other flags, mechanisms, exposed/tied slots and all-core completeness remain separate obligations.

On an original zero-dimensional projected full-kernel fibre, the previously accepted algebraic tuple census can feed this algorithm without replacing rows or choosing inconsistent kernels. This yields finite algebraic-residue critical lists for the appropriate fresh COMMON components, and nothing automatically beyond them.

## Dependencies and evidence

- WORKING-PROOF-R2.md SHA89dd1fcdbc56254c13fab1396c714073f58b26d75df521176284328aa4bff3b5, still pending independent acceptance at writing.
- Accepted EFFECTIVE-ENDPOINT-EXCLUSION.md and UNIFORM-CRITICAL-PURITY.md at their stated critical-presentation scopes.
- K1-EMPTINESS-AND-SOURCE-COROLLARY.md SHA6e9bbef4, independent source review SHA514737c1a2a06174920178737f07ccc4200cdeff2a1f73cb4f3320c265458dfb, published in the endpoint packet at commit aa0f0e41b809abc90cfeccdc43114d79a46143a5.
- Old all-r critical finiteness/Baker providers remain credited. Holder's equality characterization is classical and was checked in the accepted endpoint classification.

No new execution is claimed by this corollary. It is a source-component arithmetic-census theorem, not original G3 closure or a hardness result.
