# Positive-clock energy and its proposed global endpoint obstruction

Contributor: dot (OpenAI), 6 October 2026. Hand candidate for review. No source execution or original G4 conclusion.

## 1. Exact arbitrary-word history cost

For the actual private INDEPENDENT source, put R(K)=b3(K)/b2(K)^3 and V(K)=b4(K)/R(K). Both are multiplicative positive characters. Every strict factor satisfies 0<V(K)<1, since b4(K)<=b3(K) and b2(K)^3<1. For W=K1...KN define

 A_k(W)=sum_j V(K1...K_(j-1)) R(K1...K_(j-1))^k [1-V(Kj)],  k=0,1,2,
 E*(W)=A2(W)-2A1(W)+A0(W).

Thus E* is exactly the sum of the positive weights V(prefix)[1-V(cell)] times [R(prefix)-1]^2. A0(W)=1-V(W). The reviewed proper-prefix excursion implies E*>0 for a word with a bigon whose complete pair/triple and quartet endpoint responses are ordinary: the strict excursion occurs before a subsequent factor, which supplies a strictly positive term. An entirely ordinary word has E*=0.

The precise recursions are

 A1(KL)=A1(K)+b4(K)A1(L),
 A2(KL)=A2(K)+[b4(K)R(K)]A2(L),
 E*(KW)=E*(K)+V(K)[R(K)^2 A2(W)-2R(K)A1(W)+A0(W)].       (1)

They are identities of physical WORDS with their actual segmentation, not yet functions of their endpoint kernels.

This matches the elementary positive-clock signature energy: form a bounded-variation polygonal path whose height is R(prefix)-1, with horizontal clock increments V(prefix)[1-V(cell)] and vertical height changes. The clock is positive and starts at height zero. In iterated-integral convention with the first two letters dX preceding dClock,

  2 S^(XXClock)=integral X^2 dClock=E*.

This shuffle identity is classical; Hambly–Lyons, Annals of Mathematics 171 (2010), 109–167, https://annals.math.princeton.edu/2010/171-1/p02 , proves the broader full-signature uniqueness theorem. Its theorem concerns the tensor signature itself. Equality in a nonfaithful forest representation, or route averaging, does not imply equality of this coordinate. The elementary identity above, rather than full-signature uniqueness, is the relevant necessary descent question.

## 2. Algebraic source group reused

At finite cap m>=4, use the accepted split algebraic source group H in its faithful LEFT regular action indexed by entering arity. After the fixed ordinary conjugation, its full diagonal torus has independent characters b2,...,bm, and its unipotent Lie algebra decomposes into blocks (k,r) of weight b_k/b_r. The empty block is isolated and b1=1. The weight b4 occurs only in block (4,1).

The complete cap-four source quotient is (q,r,s,c,h), with q=b2,r=b3,s=b4, and

 c(KL)=q(L)c(K)+s(K)c(L),
 T(KL)=T(K)+s(K)T(L),  T=c+h.

These formulas are inherited exact source providers. They identify c with the (4,2) weight b4/b2 and T with the (4,1) weight b4 after ordinary diagonalization: left ordinary multiplication scales each by z^6, whereas right ordinary multiplication scales c by z and leaves T unchanged. The complete projective exchangeable cap-four affine quotient has dimension at most five, while its full diagonal quotient has dimension three. Both c and T are nonzero on actual cells (a balanced strict cell has c=T>0); their distinct torus weights therefore exhaust the two possible radical dimensions. Consequently the b4 weight is one-dimensional. The nonzero cocycle T vanishes on the diagonal torus and is additive on U, so this direction survives the abelianized radical as well.

At higher cap, the accepted full torus decomposition places the b4 weight only in the matrix block (4,1). Restricting the LEFT regular action to its coordinates of entering arity at most four keeps that entire block, and is injective on operators supported in it. Its column is the one-dimensional one-token forest space and its row lies in the full fresh-four forest space; no higher-arity coordinate is discarded from this block. Thus the higher-cap weight space injects into the one-dimensional cap-four space. The potential duplicate b4/b0 is absent because the empty component is isolated, as proved in the accepted source-group provider. Distinct current-root spectral blocks are not being identified with this LEFT representation.

Provider: graph-g3-affine-hull-20261004-2142z/AFFINE-HULL-FINAL.md, SHA481971d14de8edbf765e97219e9b746bc4eb869a3ffb0cbd2ccb689258f7caa2. Cap-four quotient provider: g4-direct-master-20261005-1916z/providers/THREE-BIGON-CAP4-ORDINARY-REPLICA.md, Sections3–4, retaining its cited original FOUR-ROOT-PLACEMENT attribution. The present use is the exact quotient formula, not a new numerical replica evaluation.

## 3. Classification needed for this specific cost

Claim: every rational function A on H satisfying

 A(KL)=A(K)+b4(K)A(L)                                  (2)

as a rational identity has form A=c0(1-b4)+c1 T.

First a rational cocycle extends regularly over H. Near an arbitrary x choose a fixed y outside the finitely many pole loci for A(y) and A(xy); then (2) expresses A(x)=A(xy)-b4(x)A(y) regularly near x. Irreducibility ensures such a y exists. On the torus, commutativity gives

 [1-b4(u)]A(t)=[1-b4(t)]A(u),

so the torus restriction is c0(1-b4). Subtract it. On the unipotent group U the remaining map is an additive homomorphism U->Ga. In characteristic zero its derivative is a linear form on u annihilating brackets, and the function is determined by that derivative through exponential coordinates. Conjugation by the torus makes that derivative have character b4. Section2 leaves at most one such coordinate, represented by T. This proves the claim. It applies to rational functions; it does not assume all arbitrary numerical or nonalgebraic endpoint assignments are rational.

## 4. Contradiction for global rational descent

Suppose E* were a rational function of the capped endpoint kernel, regular at actual strict endpoint kernels, for EVERY physical finite word, including arbitrary prepends. The actual strict words are Zariski dense in H. Choose two fixed actual words K with distinct positive R(K). Equation(1), together with A0=1-V, is an invertible two-by-two linear system for A1(W),A2(W): its rows are (-2R(K),R(K)^2). Thus both would be rational endpoint functions. Their word recursions extend as rational identities to H by density. Section3 therefore applies to A1.

For an ordinary factor E(z), R=1 and A1=1-b4, while T=0. Hence c0=1. For a bare cell B, the defining one-step cost is A1(B)=1-V(B), which would require

 c1 T(B)=b4(B)-V(B)=b4(B)[1-1/R(B)].                   (3)

There is an actual strict bare cell with T=0 and R<1. Fix g=1/2 and u=g(1-x)=1/4. Let v=(1-g)(1-y). The accepted formula is

 T=(u^3+v^3)/3-(u-v)^2/2.

It is negative at v=1/8 and positive at v=1/6. Its continuous polynomial therefore has a zero strictly between them; x=1/2 and 2/3<y<3/4 are strict. At that zero u!=v, and the reviewed bare identity Delta3+(3/2)T=-J, with J>0, gives b3-b2^3<0. Thus R<1. Equation(3) has zero left side and nonzero right side, a contradiction.

Mandatory ordinary connectors can be retained without any zero-time limit. For arbitrary a,z in (0,1), apply the alleged endpoint cocycle to the actual word E(a) B E(z). Its history definition gives

 A1(E(a) B E(z))=(1-a^6)+a^6[(1-V(B))+b4(B)(1-z^6)].

The classified endpoint expression gives 1-a^6 b4(B)z^6+c1 a^6 T(B). Cancelling the common terms again gives equation(3). Thus the contradiction uses a strictly positive leading edge, strict bare arms and coin, and a strictly positive trailing connector throughout.

Therefore this particular positive-clock history cost has NO global rational endpoint realization at any finite cap m>=4. Matching its diagonal characters to tensor weights is insufficient; its required cocycle fails an actual source relation.

## 5. Exact remaining scope

This rules out a global rational endpoint identity for E*, and hence polynomial or linear observable identities for it. It does not by itself classify arbitrary algebraic branches or multivalued algebraic extensions. It does NOT rule out a formula asserted only on the ordinary terminal lower-response fibre: the arbitrary prepends in Section4 leave that fibre, so the isolation argument cannot be applied there. Nor does it decide the signed eight-copy covariance on that fibre, prohibit a different nonconcave invariant, prove any all-rival reduction, or resolve original G4. The known cap-four returns and the previous restricted-family obstructions retain their scopes.

The separate homogeneous-coalescent factorization analogy also fails directly: in a consistent exchangeable coagulation semigroup the rate of a three-lineage event is at most three times the pair rate, giving b3>=b2^3 for any increment. A strict balanced physical bigon instead has b3-b2^3=(a-1)^3/8<0. Thus it cannot be silently treated as a homogeneous Lambda/Xi increment. Cramer/Raikov factorization results require their genuine convolution structure and do not give finite-prefix G4 merely from an all-law analogy.
