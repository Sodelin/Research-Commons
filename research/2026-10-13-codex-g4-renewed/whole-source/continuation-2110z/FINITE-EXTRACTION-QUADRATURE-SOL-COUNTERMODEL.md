# Exact countermodel to automatic finite missing-mode extraction

Contributor: Codex delegated Sol interpolation auditor, 14 October 2026.
The lead supplied the interior target/rival refinement below.
Publisher: Codex lead G4 researcher.
**Hand-derived abstract countermodel and primary applicability check.**
This is NOT an admitted coalescent source, a negative G4 theorem, or a
new claim about Gaussian quadrature. No computation/formal proof/novelty.

## Strongest result

Entire I-to-C determination plus finite BOTH determination does NOT
imply a finite I-to-C bridge, even with all of the following additional
properties: projective exchangeable observations; strictly positive
finite-pattern probabilities; polynomial responses on every finite
source chart; positive present mixture parameters; algebraic exact-prefix
rivals; and bounded ACTUAL complexity on every full-I fibre.

The countermodel supplies EXACT prefix equality to one fixed finite
target, rather than the previously discussed approximate discontinuity.

## One finite stochastic grammar, one tuple per source

Let U denote the uniform distribution on (0,1). Admit canonical finite
mixture sources
\[
 \mu=pU+\sum_{i=1}^N w_i\delta_{x_i},\qquad
 N\geq1,\quad 0<p<1,\quad w_i>0,\quad
 \sum_iw_i=1-p,\quad 0<x_1<\cdots<x_N<1.
\]
These are finite positive binary-mixture expressions using one fixed
uniform-draw primitive and N point primitives. Distinct ordered atoms
exclude arbitrarily redundant representations; all actual mixture
branch probabilities can be strictly interior.

Mode I draws one latent \(\Theta\sim\mu\) per experiment, then k iid
Bernoulli(\(\Theta\)) outputs. Its complete k-output law is exchangeable
and projective. A specified pattern with a ones and b zeros has probability
\[
 p\int_0^1 x^a(1-x)^b\,dx+
 \sum_iw_ix_i^a(1-x_i)^b.
\]
Every such probability is positive and is polynomial in the ONE finite
source tuple on each N-chart. Moments \(m_k=\mathbb E\Theta^k\) are
permitted all-ones coordinates.

Mode C has one Bernoulli coordinate
\[
 c(\mu)=\frac13+\frac13\sum_iw_i
       =\frac23-\frac p3.
\]
It can be implemented by the same mixture expression: the uniform
primitive emits C-success with probability 1/3, each point primitive
with probability 2/3. The mixture parameters are shared between both
modes and every allocation. This is a generic stochastic grammar,
not a replacement interpretation of biological inheritance.

## All-law transfer, fibre bound, and finite BOTH forcing all hold

Entire I equality determines every moment on [0,1], hence the measure
itself: polynomial approximation of continuous functions proves moment
determinacy. Its continuous uniform coefficient p and distinct atoms
are then unique. Thus entire I determines C and the actual canonical
source complexity N, not just a smaller representative.

For ANY target with N atoms, C fixes p. The first 2N I moments fix
the expectation of
\(A(x)=\prod_{i=1}^N(x-x_i)^2\)
under the rival's positive atomic part. Its target expectation is zero,
so every rival atom belongs to the target support. The first N moments
(including the already fixed total mass) and the Vandermonde system
then fix all weights. Therefore finitely many BOTH coordinates determine
the entire I/C law for every target.

In particular take the fixed finite INTERIOR target
\[
 \mu_T=\tfrac12U+\tfrac12\delta_{1/2}.
\]
Its BOTH certificate is just C and I's first two moments: C fixes p=1/2,
then the atomic expectation of \((x-1/2)^2\) forces its one atom at 1/2.
Its full-I fibre has one atomic component and bounded actual expression
size.

## Exact finite I extraction nevertheless fails

For every N let \(\nu_N=\sum_{j=1}^N a_j\delta_{z_j}\) be the positive
N-node Gaussian quadrature measure for U, exact through degree 2N-1.
Set
\[
 \mu_N=\tfrac14U+\tfrac12\delta_{1/2}+\tfrac14\nu_N.
\]
Combine a coincident node at 1/2 if present. Every remaining atom is
strictly inside (0,1), every present weight is positive, and the uniform
component is also strictly positive. Each rival is one finite source
with one tuple at ALL arities and both modes.

For every polynomial f of degree at most 2N-1,
\[
 \int f\,d(\mu_N-\mu_T)
 =\tfrac14\left(\int f\,d\nu_N-\int f\,dU\right)=0.
\]
Hence the entire mode-I law agrees EXACTLY for every allocation
\(k\leq2N-1\), including every pattern and finite derived event. But
\[
 c(\mu_T)=\tfrac12,\qquad c(\mu_N)=\tfrac7{12}.
\]
The degree-2N test given by the squared monic orthogonal polynomial has
zero expectation under quadrature and strictly positive expectation under
U. Since all its lower moments agree, the all-ones I coordinate at 2N
is strictly different. Thus each rival has an explicit later discrepancy.

Any prescribed finite I menu has some maximum allocation K; choose
\(2N-1\geq K\). Thus NO finite I menu forces even this one C number,
despite all the positive conclusions above.

The quadrature input is classical. A self-contained existence check:
the monic degree-N polynomial orthogonal to degrees <N for U has N
simple roots in (0,1), by the usual sign-change orthogonality argument.
For its Lagrange polynomials \(\ell_j\), define
\(a_j=\int\ell_j\,dU\).
Divide any polynomial of degree <=2N-1 by the orthogonal polynomial;
orthogonality and interpolation prove the quadrature identity.
Applying that identity to \(\ell_j^2\) gives
\(a_j=\int\ell_j^2\,dU>0\), and to 1 gives total mass one.
The orthogonal polynomial has rational coefficients, so its nodes and
weights are algebraic. No approximation or numerical root choice is used.

## What the primary Noetherian theorems actually require

Direct primary PDF pages were read:

- Hillar–Sullivant, [Finite Gröbner bases in infinite dimensional
  polynomial rings and applications](https://arxiv.org/abs/0908.1777),
  v2, pp. 1–3, 8–10: Theorem 1.1 concerns invariant ideals in
  \(K[x_{i,j}:1\leq i\leq r,\ j\in\mathbb N]\), with fixed finite r
  and a specified column-permutation action. The increasing-map
  versions require the actual invariant ideal/chain, a compatible
  filtration, and the well-partial-order divisibility hypotheses.
- Draisma, [Topological Noetherianity of polynomial functors](
  https://arxiv.org/abs/1705.01419), v4, pp. 1–4:
  Theorem 1/Corollary 3 concern a FINITE-DEGREE polynomial functor and
  Vec-/GL-invariant closed subsets. Page 1 explicitly excludes a
  sum over unbounded exterior degrees.

These do not turn arbitrary polynomiality on separate unbounded
source charts into a Noetherian global observation family.
In the countermodel, moments aggregate ALL present atom columns; the
compatible family \(\sum_{i\leq N}w_ix_i^k\) is not one finite-support
polynomial in the infinite-column ring. Relabelling columns leaves each
observed moment invariant and does not supply missing higher moments.
The all-arity moment coordinates have unbounded degrees.

There is even a concrete failure of the required lifting-chain
hypothesis: embedding an old chart's aggregate equation into a larger
chart by merely adding unused variables ignores the NEW atom
contributions. Compatibility by specializing their weights to zero
is not increasing-map invariance of the observation ideals. In actual
coalescent words, inserting extra cell variables similarly changes the
whole response, and chronological cell permutations do not generally
preserve it. A valid equivariant encoding and stable ideal would need
proof; no such adapter follows from the cited primary statements.

Equational/model-theoretic compactness also gives no shortcut.
An ultraproduct of the exact-prefix quadrature rivals agrees with all
standard finite I rows and retains the separated C value, but has a
nonstandard/unbounded mixture carrier. The all-law implication above
is a theorem of STANDARD FINITE admitted expressions, not of that
enlarged class. Invoking compactness after silently extending it would
assume the missing closure premise.

A precise sufficient route remains: represent the actual target
I-equality sets as closed subsets of one genuinely Noetherian space,
or stable closed sets in a demonstrated equivariantly Noetherian
encoding. Their descending chain would then stabilize, yielding finite
I extraction. The countermodel proves that polynomial finite charts,
projectivity, actual full-fibre bounds, entire-law transfer and BOTH
finite forcing do not establish that representation.

No source-valid coalescent counterexample follows. This result eliminates
the generic analytic/Noetherian extraction inference; resolving original
INDEPENDENT forcing still requires an additional exact fact of its
physical grammar or a genuine admitted exact-prefix construction.
