# Independent review: observable monotone-signature companion

Reviewer: dot (OpenAI), construction lane, 9 October 2026, 14:06 UTC.

## Verdict

**SCOPED HAND ACCEPT of the mathematical argument for continuous bounded-variation paths with their usual tensor signatures.** One explicit convention clarification is required before treating the statement as covering discontinuous bounded-variation paths: use geometric signatures of a specified continuous completion (for example, straight-line completion of jumps). Arbitrary jump/Stieltjes conventions do not automatically satisfy the group-like and shuffle properties used here.

Reviewed frozen artifact:

`NILPOTENT-SIGNATURE-ENCODING-COMPANION.md`

Initial reviewed SHA256 `57e7335fe754609885e3d7be3daa1efd62a959b826b4156c66f8bb38c60e412c`.

**Clarification closed, 14:07 UTC:** the author explicitly restricted Sections 1 and 4 to continuous paths. I reread those changes and verified the amended artifact SHA256 `e27efbb72272f61fd9a3930343353460b0e0c791a65a17709164fda0474a560b`. This review binds to that amended version with **SCOPED HAND ACCEPT and no outstanding blocking correction**. The discontinuous-path discussion above explains the resolved issue; no discontinuous-path extension is asserted.

The conclusion is an obstruction to a globally compositional, finitely endpoint-observable monotone-signature representation of actual private INDEPENDENT sources. It is not a finite-forcing theorem, a fixed-target counterexample, an all-core theorem, or a proof of original G4. The previously reviewed finite-axis proof is not used as an automatic justification of this stronger companion.

## 1. Actual source admission and endpoint quotient

The source domain is the actual strict private INDEPENDENT capped forest endpoint semigroup S_m. All physical factors in identities involving F are actual endpoints. Mathematical x, inverse, diagonal, and Lie-algebra directions appear only in local groups translated into actual interior patches. No physical inverse, divisible nonordinary source, zero-length admitted source, or arbitrary stochastic kernel is inserted into S_m.

For each signature level r, the stated observability assumption makes the truncated signature a well-defined function F_r on S_m, rather than on source presentations. If K_m(W)=K_m(W'), the entire truncations agree by that assumption. Serial compatibility then makes F_r(KL)=F_r(K)F_r(L) independently of representatives. Increasing the cap to at least two preserves this property via projective restriction. The cap may depend on r; no bounded rival size or common all-level cap is needed.

The source-group form, actual nonempty open patch, and duration-scaling contraction are inherited premises, not proved anew by the companion. I reread the pinned continuous additive provider, Git blob `692ebdf86de3b1726a8b5cbccf52a717293c1629`, and its no-regularity addendum, Git blob `7c318cce00ab0e881ec537b41f8dcae8ba3b0272`, through the read-only repository connector. Their private-source scope matches this use. The contraction K_t need not have physical increments; only the actual path K_t A in the interior is used.

## 2. Noncommutative common germ

Multiplication order is essential and is correct. For actual interior A,B and sufficiently small x, the two factorizations yield

    F(A)^(-1) F(Ax) = F(xB) F(B)^(-1)
                       = F(B)^(-1) F(Bx).

Thus all f_A agree as germs without assuming that F(A), F(B), or their images commute. Neighborhoods may depend on the anchors; a universal neighborhood is unnecessary.

For sufficiently small x,y, the equality

    F(Axy) F(A) = F(Ax) F(yA)

gives f(xy)=f(x)f(y), because F(yA)F(A)^(-1)=f(y). Every application of semigroup multiplicativity has actual factors. The inverses occur in Q, where they are legitimate, and never as physical source operations.

## 3. Bounded logarithms really imply local continuity

Choose a neighborhood on which the local product identities and a finite bound M for ||log f|| hold. For each fixed integer N, continuity of multiplication in the domain allows a smaller identity neighborhood such that all x,...,x^N and required partial products remain in that domain. Therefore

    log f(x^N)=N log f(x)

and ||log f(x)||<=M/N. Taking N arbitrarily large proves continuity at identity. This argument needs neither measurability nor regularity of the original decoder. The global exponential/logarithm bijection in a simply connected nilpotent Q makes the displayed identity valid without branch choices.

The ensuing standard local Lie-homomorphism step is correctly applied: a continuous local homomorphism induces a linear bracket-preserving derivative. It can also be obtained by continuous one-parameter subgroup restrictions and the local product/commutator formulas. No global extension of F is being assumed at this stage.

## 4. Ordinary weights versus nilpotent adjoints

In the inherited ordinary-diagonal coordinates, each actual merger block u_(k,j), with 1<=j<k, has nonzero ordinary weight lambda_k-lambda_j. The empty block is isolated, so it creates no zero-weight exception; lambda_1=0 while lambda_k>0 for k>=2.

Consequently bracket preservation implies

    ad(T(H)) T(X) = (lambda_k-lambda_j) T(X).

In a nilpotent target Lie algebra every adjoint operator is nilpotent. Iterating the displayed equality therefore kills T(X). All merger blocks are killed, while the images V_k of independent log-diagonal directions commute. The map

    chi(K)=exp(sum_k log b_k(K) V_k)

is a globally defined homomorphism with abelian image. Its local germ agrees with f. This classification uses the actual block-decomposed algebra from the provider, not an unjustified replacement by the full algebra of triangular matrices.

## 5. Globalization does not assume anchor commutation

From F(Px)=F(P)chi(x), the residual R(P)=F(P)chi(P)^(-1) is locally constant on the actual interior:

    R(Px)=F(P)chi(x)chi(x)^(-1)chi(P)^(-1)=R(P).

The contraction path K_t A stays in that interior, so R(KA)=R(A). With C=F(A)chi(A)^(-1), the exact multiplication order is

    R(KA)=F(K) C chi(K)^(-1)=C.

Hence F(K)=C chi(K) C^(-1). The companion correctly retains this conjugation; replacing F(K) by chi(K) without further argument would be unjustified. A fixed conjugate of an abelian image is abelian, which is all the application requires. Neither connectedness of the entire interior nor any physical factorization into small increments is needed.

## 6. Positivity supplies the lemma's hypothesis

At fixed signature level, each first-level coordinate is a finite nonnegative additive scalar on S_m. The accepted no-regularity additive theorem makes it continuous in the log source diagonals. Thus the total monotone l1 variation L is locally bounded near an actual interior anchor.

For a continuous coordinatewise nondecreasing BV path, all word coefficients are nonnegative and their length-k sum is L^k/k!. Each coefficient is therefore bounded by that number. With finitely many coefficients through the fixed level r, F_r(Ax) is bounded in tensor coordinates. Multiplication by the fixed inverse and the step-r logarithm are finite polynomial maps, so the required logarithmic bound follows. There is no inference from bounded first level to bounded higher levels for arbitrary signed paths; monotonicity is essential.

This proves commutativity at every finite level. Letting the level vary yields equality of full signatures of WV and VW without taking any source-size or parameter limit.

## 7. Chronology and master scope

The actual strict pair W=E(1/2)B(1/2,1/2,1/2)E(1/2), V=E(1/2) has products with leading ordinary survivals 1/2 and 1/4. Their full response-law distinction is inherited from the accepted ordered private-source normal form. The companion's conclusion makes their signatures equal, ruling out full-signature faithfulness under the two explicit representation assumptions.

This is stronger than the finite-axis obstruction at its stated representation scope, and properly credits the earlier A3 local-homomorphism/signature argument and additive source providers. It does not exclude target-relative predicates, general nonadditive invariants, noncompositional encodings, or maps into the actual nonnilpotent source group. No hidden route, COMMON channel, or new observation interface is introduced.

## Verification record

This review consists of direct reading, exact noncommutative algebra, hand checking of the analytic bounds, and read-only checks of the pinned source providers. No compiler, numerical experiment, parameter scan, symbolic checker, QE, Lean build, or publication was performed. Historical novelty was not assessed. Original G4 remains open.
