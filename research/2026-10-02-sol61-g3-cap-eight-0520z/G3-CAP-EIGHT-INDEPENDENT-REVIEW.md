# Independent review: both-active cap-eight COMMON-chain critical finiteness

Reviewer: dot / continue_lean_proofs_two, 2026-10-02 05:15 UTC.
Decision: ACCEPT the stated, source-specific hand theorem and its exact certificate. No Lean proof of the whole theorem or full-network G3 recognition is claimed.

## Reviewed result and scope

For the genuine COMMON serial Bernoulli factor `1-p+p q^lambda`, with exponents `(1,3,6,10,15,21,28)`, and any nonzero real normal annihilating the six stated mass, drift and paired-residue rows at `0<r<1`, the strict two-parameter critical locus is finite, with at most 4,175 pairs. If r is algebraic the critical pairs are algebraic. Normal scaling is immaterial.

This is a COMMON-chain critical-stratum subproblem. It is not an arbitrary finite-input membership algorithm, an unknown-residue extraction theorem, a general-network complexity bound, or unrestricted G4 stopping. In particular, a lower bound on COMMON-chain factor counts would not automatically be a lower bound on realization size when a larger network class is allowed.

## Source-critical mathematical checks

1. **Normal line and nonzero coordinates.** A dependence among any six selected columns produces a nonzero polynomial with at most six monomials. The mass/drift rows force double root 1, and the four paired-residue rows force double roots r and r squared. These are distinct positive roots. Descartes' bound of at most five positive roots counted with multiplicity contradicts six. Thus every six-column minor is nonzero, the normal line is one-dimensional, and each normal coordinate is nonzero. The exported nonzero B vector satisfies all six polynomial row identities, so it lies on exactly that normal line. No numerical minor test supplies this rank argument.
2. **Actual derivative equations and degree reductions.** The genuine p response has cleared numerator P. The q response has numerator minus p times Q0. Strict positive denominators, p, and 1-p allow replacement by P=Q=0, where Q0=(1-p)Q. Active killing cancels the highest p coefficient of P, and active drift gives Q0(1,q)=0. Both source polynomials therefore have p degree at most five. Fixed-degree (5,5) Sylvester construction remains legitimate if specialization lowers a degree.
3. **Full cubic source identity.** In the constrained rational weight ring, each restricted coordinate is a nonzero linear prime and no two are associates: the two other distinct exponent coordinates outside any selected pair force any putative mass/drift-row relation to vanish. Setting one genuine weight to zero makes its actual linear factor divide P and Q0. It also divides Q in the quotient fraction field because its value at p=1 is nonzero at either q slice. Hence that coordinate divides the source determinant in the polynomial ring. UFD product divisibility and ten linear homogeneous determinant rows give a homogeneous cubic quotient. These are mathematical degree/factor claims, not conclusions extrapolated from determinants at sampled weights.
4. **Unisolvence.** On u4=7, the 35 nodes ui=7(1+ai), with nonnegative multiindices of total degree at most three, are unisolvent. The product binomial Newton basis evaluates triangularly under total-degree order, with diagonal one. Thus the exact 35 source values determine the entire polynomial on that hyperplane. Homogeneity recovers the full five-variable cubic, including u4=0. Additional controls remain samples only.
5. **All-residue exclusion.** The two normal-substituted residuals have degree 231. The explicitly verified Bezout identity modulo 1009, with both leading coefficients nonzero modulo that prime, proves characteristic-zero coprimality by primitive-factor reduction/Gauss. A nonconstant rational common factor would reduce to a nonconstant common factor and contradict the modular identity. Therefore the two actual slice resultants cannot both vanish at any strict r, since no normal coordinate vanishes there. The source resultant in q is consequently a nonzero polynomial for every strict r.
6. **Vertical exclusion.** For each strict q, the losses Di=1-q to exponent i are positive and pairwise distinct. At p=1/Dk, every other P summand contains its zero factor fk, while the remaining term is `Bk Dk product(1-Dj/Dk)`, which is nonzero. This proves P is nonzero as a polynomial in p without the older, now-cancelled leading coefficient. An evaluation outside the allowed p interval is used only for a polynomial identity/nonzeroness test.
7. **Finite count and algebraicity.** The source bounds are q degree at most 84 for P and 83 for Q. Five Sylvester rows of each give degree at most 835. Each strict q root permits at most five p roots of its nonzero P. This gives 4,175 distinct strict critical pairs. For algebraic r, the same argument takes place over the algebraic numbers, establishing algebraicity of q and then p.

## Independent executed evidence

`review_g3_cap_eight.py` reads the saved proposal and constructs source-product coefficients by elementary symmetric subset sums, rather than the proposer's ascending convolution code. It computes the exact coefficient-map determinant with a separate descending-convention check. The replay passes:

- all six normal polynomial identities
- 35 unisolvent source determinants and ten NEW extra controls at q=3
- 35 unisolvent source determinants and ten NEW extra controls at q=5
- all source mass/drift degree reductions at those controls
- both actual normal substitutions, reconstructed with ascending rational coefficient lists
- equality with both exported degree-231 primitive polynomials
- the EXPLICIT mod-1009 Bezout coefficient identity and preservation of both input degrees

Proposal SHA-256: `bdc4b2b07f22324ffef2f248e1fd639bb6d0d8f7ab7606f9c19a29df237e0ae0`.
Independent checker SHA-256: `bc7b088c8d7cf3f10a17743dde88c162b123a6c4be18ce177f383ae853c59ffa`.
Receipt: `g3-cap-eight-independent-replay.json`. Runtime 2.399 seconds.

The determinant controls do not by themselves certify a generic cubic identity. Acceptance uses the separately reviewed factor-divisibility/homogeneity and unisolvence arguments above. Descartes, UFD divisibility, fixed-degree common-factor resultant vanishing, unisolvence, and the modular lift are hand proof bridges here. The replay is exact arithmetic, not a Lean kernel result. Existing cap-seven results and their attribution are unchanged.

## Packaging note

The reviewed universal structural lemma was recovered from `g3-resultant-structure-0451z/WEIGHT-PRODUCT-RESULTANT-LEMMA.md`; publication should include that exact lemma alongside the cap-eight packet or link to its immutable published pin. The two interrupted rational Euclidean-sequence attempts contribute no proof receipt.
