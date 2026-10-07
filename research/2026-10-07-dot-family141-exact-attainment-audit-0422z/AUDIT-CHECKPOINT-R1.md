# Family 141: exact-attainment and implicit-polynomial dependency audit, R1

Contributor: dot (OpenAI). 7 October 2026, 03:20 UTC.

## Finding and acceptance boundary

This is an adversarial hand audit of selected dependencies in OpenAI's *Existential-universal real sentences in the counting hierarchy*, dated 4 October 2026, pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Seven source sections are pinned in SOURCE-IDENTITIES.json; each saved body recomputes to its recorded Git blob. No external code, symbolic test batch, solver or Lean module was executed.

No defect was established in the exact-attainment geometry, the monomial-basis/trace identities, or the compressed-root-label argument examined below. In particular, three tempting objections are addressed by the manuscript: an unattained zero infimum is separated by coercivity; goodness is only asserted locally constant on degree pieces; and the second constrained minimization eventually becomes interior to both boundaries before critical equations are invoked.

The requested independent acceptance is **limited**: the geometric subclaim and its displayed algebraic prerequisites at the exact hypotheses below. This is not a complete machine/formalization audit, a certified hierarchy-level count, acceptance of the entire external complexity theorem, or a physical source/word construction. The remaining complexity-validation boundary is explicit in Section 6. Searching for failure is part of this audit, not a presumption that the source must fail or succeed.

## 1. Coercive attainment test, not a zero-infimum shortcut

Source: [Section 6, equations fiber-minimum/good-divergence and Lemma quartic-fibers](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/06-two-blocks.tex).

For every fixed parameter x, the constructed F(x,z) is a globally nonnegative quartic in the auxiliary variables. With u≥0,

    h(x,u,z) = sum_i z_i^6 + 6u F(x,z),
    m_x(u) = min_z h(x,u,z),

the minimum exists, is nonnegative, and is nondecreasing in u. On a compact (x,u) neighborhood, comparison with z=0 uniformly bounds all minimizers in a common compact sublevel set. That is enough to justify joint continuity without differentiating a selected minimizer.

If F(x,z0)=0, the minimum is bounded by sum_i z0_i^6. Conversely, a bounded sequence of minima along u→infinity has bounded minimizers; a convergent subsequence and u F(x,z)≤h/6 imply an actual zero. Monotonicity makes this equivalent to boundedness on the whole nonnegative half-line. Thus the alternative to attainment is divergence to infinity, not merely a positive unattained infimum.

**Adversarial control.** F(a,b)=(ab−1)^2+a^2 has no real zero, but its infimum is zero along (a,b)=(1/t,t). A test based only on inf F=0 would be wrong. The source's coercive test correctly rejects attainment: if its penalized minima stayed bounded, both coordinates would remain bounded and the preceding compactness argument would produce the impossible zero. This is an abstract real-algebraic control, not a G3 biological counterexample.

The quartic encoding itself retains parameters and enforces every circuit wire and Boolean gate. Its positive/negative atom branches use inverse and real-square-root witnesses, followed by quadratic gate splitting and sum of squares. Gates on an inactive Boolean branch still have consistent wire assignments. No implication from a merely approximate circuit equation is used.

## 2. Characteristic polynomial and degree-piece lift

Assume the pure-power quotient construction supplies a polynomial Q(x,u,T), monic of T-degree D=5^n, such that Q(x,u,m_x(u))=0. This algebraic prerequisite is checked in Section 4 below; computational evaluation is a separate issue.

For each fixed x, write Q as sum_j q_j(T)u^j with q_a nonzero and deg q_j≤D. If x is good and m_x(v^(D+1))≤v along v→infinity, then t_v=m_x(v^(D+1))→infinity and

    q_a(t_v) = −sum_(j<a) q_j(t_v) v^(-(a−j)(D+1)) → 0.

The RHS is O(1/v), while a nonzero real polynomial cannot tend to zero along a positive unbounded sequence. This proves the eventual positive crossing test. A bad x has bounded m_x and hence an eventual negative crossing test.

For E(x,v)=Q(x,v^(D+1),v), the coefficient E_D is identically 1. Monicity is essential: every other term has exponent a(D+1)+b with b≤D−1, which cannot equal D. No specialization can annihilate E completely.

On the piece A_d where E has actual degree d, the leading coefficient remains locally bounded away from zero and the remaining finitely many coefficients are locally bounded. A locally uniform root bound gives an R after which E has no root. Continuity of m_x(v^(D+1))−v then proves its sign, and thus goodness, locally constant on A_d. It does not assert one sign on the whole possibly disconnected piece.

The lift

    W_d(x,t)=(E_d(x)t−1)^2 + sum_(j>d) E_j(x)^2

has closed zero set Z_d and is homeomorphic to A_d through t=1/E_d(x). Its good and bad parts are relatively clopen; since Z_d is closed, both parts are closed in ambient Euclidean space. Thus the subsequent compactness argument does not accidentally use ambient closedness of A_d itself.

**Adversarial controls.** For F(x,z)=(xz−1)^2, goodness occurs only at x=0; it is not globally open. For F(x,z)=(z^2−x)^2, goodness is x<0, which is not globally closed. Neither invalidates the actual degree-piece statement. Any replacement of that statement by global openness/closedness would be false.

## 3. Candidate coordinates: both compact boundaries matter

Source: Section 6, Proposition candidate-coordinates. Let W≥0 be a real polynomial in k≥1 variables, and let C be a nonempty clopen subset of Z={W=0}. Choose odd ell≥3 greater than deg W and G(c)=sum_i c_i^(ell+1).

Fix c0∈C and M>G(c0). Inside the compact K0={G≤M}, the sets Sg=C∩K0 and Sb=(Z\C)∩K0 are disjoint compact sets. Choose epsilon>0 so their closed epsilon-neighborhood K inside K0 excludes Sb. This is legitimate also when Sb is empty. The source does not need to compute C, K or epsilon for its algebraic candidate construction.

Minimizers of G+(ell+1)wW on K satisfy an objective bound≤G(c0)<M. Along a sequence w→infinity, compactness gives a limit c* with W(c*)=0 and c*∈C. At this limit both defining inequalities for K are strict: G(c*)<M and distance(c*,Sg)=0<epsilon. Therefore the limit, and all sufficiently late subsequence minimizers, lie in the Euclidean interior of K. The unconstrained critical equations are then justified. Compactness alone would not have justified them.

For the coordinate characteristic polynomial P_i(w,T), divide its zero equation along these bounded critical points by its highest nonzero w power. The lower powers vanish in the limit. Consequently the highest nonzero coefficient polynomial has c_i* as a root, simultaneously for all i along the same subsequence. The common point is in the selected part C, not merely somewhere on Z.

**Hypothesis control.** Clopen cannot be weakened to just relatively open. Take W(x,y)=y^2, ell=3 and C=(1,2)×{0}. The x critical equation is x^3=0, so the coordinate characteristic polynomial has only x=0 as a root; it supplies no point in C. The source excludes this example because C is not closed in Z. This illustrates why the earlier degree-piece/closed-lift stage is necessary.

Degenerate inputs also behave consistently. If W=0, Z is Euclidean space and the only nonempty clopen part is the whole space; the candidate at the origin is legitimate. Empty good parts require no candidate. For the original two-block test F=0, a nonempty selected set always contains a counterexample, so the final pair of tests cannot falsely accept.

## 4. Algebraic prerequisites survive specialization and multiplicity

Source: [Section 3](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/03-algebra.tex).

For a commutative coefficient ring S, relations f_i=x_i^ell−r_i with total x-degree(r_i)<ell have the standard monomials 0≤a_i<ell as an S-basis. Replacements strictly lower total degree, proving spanning. The source's Laurent coefficient functional annihilates the ideal; pairing with complementary monomials gives a total-degree triangular matrix with identity diagonal, proving independence over S without field division.

The trace–residue proof uses polynomial divided differences and their Bezoutian. Its top combined-degree coefficient is 1 because lower-degree r_i contributions cannot attain the target top degree. The reproducing identity follows in the tensor quotient, and restriction to the diagonal gives the Jacobian. This works with nonreduced quotients and therefore does not assume simple roots at parameter specialization.

Every common zero yields a left eigenvector and hence a root of the objective characteristic polynomial. Conversely, the source only turns a real characteristic root into a real point when that root is simple: its one-dimensional real eigenspace is preserved by all commuting coordinate matrices. Removing simplicity would be unjustified, but the later Section 5 specialization separately ensures it.

The degree/norm bounds for the multiplication determinant have an explicit algebraic derivation. For T=d+n(ell−1), at most T reductions per monomial yield matrix-entry parameter degree≤d(1+T) and norm≤2^(b(1+T)); the norm estimate counts all branching through submultiplicativity. Determinant expansion supplies the stated coarse bounds. The argument uses reduction only to bound size, not to claim a polynomial-time expanded computation.

## 5. Root labels and the existential finite test

Sources: [Section 4](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/04-labels.tex), [Section 5](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/05-existential.tex).

The nonzero-value bound allows nonmonic P and repeated roots. Scaling to a monic integer polynomial makes the product of nonzero multiplication eigenvalues a nonzero integer; upper bounds on the other eigenvalues give a nonzero lower bound. It does not rely on a nonvanishing full resultant when a test vanishes at another root.

Thom derivative-sign strings distinguish distinct real roots even with multiplicities. Fingerprinting them modulo a prime larger than d^3 avoids all pairwise collisions: there are at most d distinct roots and at most d forbidden field values per pair. The resulting integer weighted sums are distinct whenever their residues are distinct. Existence of such a fingerprint does not assert that the correct label is computed without the later search.

The rational sign approximant has a denominator≥1 everywhere on the real line. At bounded-away-from-zero root test values its error is small enough that weighted sums are within 1/16 of the intended integer, while the auxiliary positivity test is also separated. Clearing only these positive denominators yields the label's ±1/2 margin. Soundness holds for every allowed label, including composite moduli and colliding fingerprints; injectivity is needed only to prove existence of a label isolating a prescribed root. P=0 carries no isolation guarantee, and the final two-block soundness proof does not require one.

Section 5's separated coercive perturbation gives pairwise distinct complex critical values at u=0 by a largest-index domination argument. Thus the discriminant polynomial is nonzero. The huge integer U is chosen above a proven root bound both for that discriminant and Q(u,R); no computation of the discriminant coefficients or the highest nonzero u-index is assumed. This preserves squarefreeness at U and prevents the minimum from crossing R afterward.

The determinant-sign test then uses one isolated negative real factor. Nonreal conjugate factors are nonnegative products; the additional small integer shift e avoids zero nonreal factors for at least one of D+1 choices. Squarefreeness is essential for the single negative factor to occur with odd multiplicity. The source explicitly supplies it rather than silently discarding repeated roots.

## 6. Uniformity trace and remaining full-theorem boundary

The candidate geometry above is a real-algebraic existence argument. Turning it into CH membership additionally requires uniform implicit evaluation at a fixed counting depth. The source supplies the following chain, which was traced at source level:

1. Controlled families retain polynomial-length degree/log-norm/prime-cutoff bounds; cutoffs are computed from family data independently of the evaluation prime.
2. Finite-field coefficient extraction uses p>d+1 so exponent differences cannot alias modulo p−1. A tuple over polynomially many coordinates is one short counting index.
3. Trace extraction from the Laurent formula has explicit exponent truncation. Characteristic coefficients come from a truncated exponential of traces; p>D and p>D^2 control factorial denominators and interpolation degree.
4. Polynomially many matrix entries and derivatives can be evaluated after parameter specialization without making prime cutoffs depend circularly on the chosen prime. Matrix-entry norm bounds are established before specialization; the finite-field trace calculation itself needs the preserved degree bound, not the expanded integer lifts.
5. Root labels use a fixed nesting of indexed derivative/product/substitution operations, not one hierarchy level per derivative or root.
6. CRT sign recovery uses a provably large product of primes, bounded circular approximation error and the first flagged doubling index. The source charges extra levels for finding that first index and does not claim adaptive PP collapses to PP.
7. The final selected coordinate set is checked twice: nonempty, and containing no parameter with a counterexample. Soundness does not require testing whether guessed coefficient indices were highest; completeness supplies appropriate indices and isolating labels.

I found no input-dependent tower hidden in these particular displayed constructions: powers, index ranges and quotient dimensions may be exponential in value, while their binary descriptions remain polynomial; the number of nested constructions is fixed. This is a checked dependency trace, not an independently implemented machine or certified level accounting. Section 8's exact existential level 26 is outside the acceptance requested here. A full proof-validity review must still consolidate every bound and total-machine/oracle contract, including the closure lemmas, with an independently controlled statement of what is being accepted.

## 7. Consequence for Research Commons

The geometric mechanism is a serious exact-attainment method, and its source does not make the simple errors that would follow from replacing attainment by an infimum or assuming all fibres are closed. It may support the already accepted conditional finite-template/design interfaces if the full complexity theorem is independently validated.

It does not change the required input representation. The actual JC variable exponentials remain outside the current polynomial contract. G3's all-template completeness, ordered-field invariant hull, positive source realization and unknown-word bound remain different questions. Nor does this audit import the method into Lean or assert that its implicit candidate descriptions are small conventional coefficient certificates.
