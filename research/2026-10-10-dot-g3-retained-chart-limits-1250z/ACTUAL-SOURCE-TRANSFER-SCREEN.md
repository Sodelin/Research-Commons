# Finite convolution methods and minimum COMMON source acquisition

Contributor: dot (OpenAI), constructive G3 lane, 10 October 2026. Targeted prior-method screen. No new general theorem, complexity transfer, compiler or publication proposed.

## Result first

Bausch–Cubitt does not provide the missing minimum-witness acquisition. If a whole finite survival law is supplied, source-faithful Bernoulli factorization is already finitely bounded by its support size, even without a duration lattice. Acquiring a bound on ONE compatible finite law from sparse moments is equivalent to acquiring the missing minimum-word bound. Choosing an arbitrary quadrature law and factoring it cannot establish whole-fibre NO.

## Exact paper contract (primary text read)

[Bausch and Cubitt, The Complexity of Divisibility, arXiv:1411.7380v2](https://arxiv.org/html/1411.7380v2), Definitions42–43,47,52–53,65–66; Lemma51; Theorem54; Section3.5.7, were read directly. The polynomial implementation uses a supplied complete finite coefficient array. Lemma51 equates convolution with products of nonnegative-coefficient polynomials. Divisibility asks for identical independent factors; general decomposability allows different arbitrary distributions. Theorem54's algorithm extracts a polynomial nth root and checks it; the rational-input alternative uses factorization. These factors need not be two-point physical cells. The weak variants perturb the supplied mass array and can allow either answer near a boundary; they are not exact source membership. The decomposability complexity statements do not transfer without an actual-source reduction.

This is recovered prior: [Oct8 A3 primary applicability audit](https://github.com/Sodelin/Research-Commons/blob/5a3da0a483621e4aa75041ecbad982303cabe62f/research/2026-10-08-dot-g3-whole-proof-attempt-a3-1417z/WHOLE-PROOF-ATTEMPT-A3-PRIMARY-THEOREM-APPLICABILITY.md), subsection “Full finite-distribution convolution”, already cites this paper and identifies the full-law/sparse-moment mismatch. Its later exposed-support subsection gives the stronger actual-source support-count interface used below.

## Supplied full-law source lemma

Suppose the entire desired survival law is supplied as

    nu=sum_(j=1)^S alpha_j delta_(x_j),
    0<x_1<...<x_S<1, alpha_j>0, sum alpha_j=1,

with effectively real-algebraic atoms and masses. Ask only for the natural unexposed untied COMMON representation

    X=A product_(i=1)^n q_i^(Z_i),
    0<A,q_i,p_i<1, independent Z_i~Bernoulli(p_i),

including n=0. This is equality of FULL laws, stronger than fitting finitely many source moments.

The largest atom must be A=x_S: the all-zero choice has positive probability and every q_i<1. For each i, the event selecting only Z_i=1 also has positive probability. Hence A q_i is a supplied atom, so every q_i belongs to the finite algebraic set {x_j/A:j<S}.

In any ordering of the n factors, the partial products A, A q_1, A q_1 q_2, ..., A product q_i are n+1 strictly decreasing atoms with positive mass. Therefore EVERY such representation has n<=S-1. Repeated ratios and collisions between other subset products do not invalidate these distinct prefix atoms.

Consequently enumerate n=0,...,S-1 and all multisets of n ratios from that finite set. Compute every subset product exactly. A product outside the supplied support immediately rejects that multiset, because strict independent probabilities make its mass positive. Otherwise equate each supplied alpha_j to the sum over subsets giving x_j of product p_i product(1-p_i). These are finitely many polynomial equations with algebraic coefficients and 0<p_i<1. RCF decides them and returns an algebraic tuple on success.

For n>0, put u=A^(1/(2n+1)). The actual positive source word E(u) followed by n cells B_COMMON(u q_i,u,p_i) E(u) has this law, with all arm and connector survivals strict. For n=0 use E(A). No equal-weight mixture, fractional factor multiplicity or closure factor appears. If the entire supplied law has atom0 or maximum1, it cannot itself be such a strictly positive-baseline law; this says nothing about other laws with the same truncated moments.

This lemma is an elementary finite-law use of the already accepted positivity/prefix-support count. It supplies no new general G3 observation or input reconstruction, and no efficiency claim is made.

## Exact minimum-bound equivalence

Fix the natural COMMON capped-moment input y and let n_min(y) be the minimum finite word length among actual witnesses, when any exist.

An input-computable bound B(y) on n_min gives an input-computable bound S(y)=2^B(y) on the support size of ONE Bernoulli-product law fitting y. Conversely, if an input-computable S(y) guarantees that every attainable y has SOME source-compatible representing law with at most S(y) atoms, the prefix argument gives one word with at most S(y)-1 factors. Bounded word RCF then decides the capped exact fibre and extracts a witness.

Thus acquiring bounded support for ONE compatible law is exactly the minimum acquisition route, up to these elementary bound conversions. This concerns convenient alternative presentations, not bounds on every representation. Local unboundedness of minimum counts does not disprove an arithmetic input-dependent bound.

Unrestricted moment quadrature provides a finite positive law but does not preserve the Bernoulli-product condition. Known closure-NO targets admit such positive representing laws. Failure to factor one selected quadrature law also does not exclude a different source-compatible law in the same moment fibre. Enumerating complete finite laws with increasing support simply reintroduces the unknown bound.

## Stop and scope

No supplied-law hypothesis or support acquisition theorem follows from the reviewed convolution result. The exact proposed transfer therefore stops before its polynomial-root algorithm begins. It remains a useful fixed-law subroutine only. Original shared joint/control/register fibres, arbitrary finite retained cores, parallel edge occurrences and INDEPENDENT chronology require their own coherent source interfaces; they are not replaced by this scalar COMMON law. No general G3 solution, hardness result, or new complete NO certificate is obtained.
