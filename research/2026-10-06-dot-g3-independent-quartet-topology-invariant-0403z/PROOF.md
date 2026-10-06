# A nonlinear INDEPENDENT whole-word invariant using completed quartet shape

Contributor: dot / original G3 lane, 6 October 2026, 03:57 UTC.
Status: complete hand-proof candidate for independent review. No new numerical, symbolic, QE or Lean execution.

## 1. Source and actual topology functional

Fix the original natural INDEPENDENT private bridge-word source at a finite cap m>=4. The same physical parameters act at every arity. Cells route each CURRENT ancestral root independently; previously formed subtrees are opaque current roots and are never rerouted by their original tip counts. All arm and ordinary survivals are in (0,1), and all routing probabilities are interior. Keep the full labelled unranked forest graft kernel.

Write a(K)=b_2(K), c(K)=b_4(K), and define

    T(K)=Pr(the completed rooted four-tip tree is balanced | K)-1/3.

Here completion means the original unrestricted ordinary ancestral-root completion applied after the private forest. A balanced tree has two cherries at the root. T is an affine functional on stochastic kernels, or equivalently the linear row functional obtained by subtracting one third of the row total. It is not a hidden routing flag or a new independent repetition of the source. In a larger retained core it is used as an internal kernel functional unless the actual legal response compiler identifies it.

The theorem is the polynomial inequality

    T(K)<144(1-a(K))^3                                  (1)

for every strict finite INDEPENDENT word, together with c(K)<=a(K)^3. More precisely the stochastic graft-kernel region given by these inequalities is preserved by every actual chronological source append. The coefficient 144 is a convenient uniform hand bound; no optimality is claimed.

An explicit coherent full-kernel family below satisfies all affine source guards, the previously accepted pair/triple nonlinear test, and c<=a^3, but violates (1). This is a full-topology certificate beyond those relaxations. It is not complete recognition of arbitrary original fibres.

## 2. Classical prior used for no-merger log-concavity

David W. Walkup, Pólya sequences, binomial convolution and the union of random sets, Journal of Applied Probability 13(1), 76–85 (1976), DOI 10.2307/3212667, is the direct binomial-convolution predecessor:
https://www.cambridge.org/core/journals/journal-of-applied-probability/article/abs/polya-sequences-binomial-convolution-and-the-union-of-random-sets/16A9813D68099FA8FE20EF67634D012A .
The publisher's 2016 online date is not its original publication year.

For a precise checked theorem, use Liggett's convolution theorem for ultra-log-concave sequences, as stated and proved anew in Leonid Gurvits, A short, based on the mixed volume, proof of Liggett's theorem on the convolution of ultra-logconcave sequences, arXiv:0804.1181, Theorem 1.1:
https://arxiv.org/pdf/0804.1181 .
It says convolution takes ULC(l) and ULC(d) to ULC(l+d), with ULC(d) defined by log-concavity after division by the binomial coefficients of order d. This established method is credited, not claimed as a new theorem. The original Liggett paper is JCTA 79 (1997), 315–325, DOI 10.1006/jcta.1997.2790.

For a bare physical cell with arm survivals x,y and routing probabilities p,q=1-p, its no-merger coordinate is exactly

    b_k=sum_(j=0)^k binom(k,j) p^j q^(k-j)
          x^(j(j-1)/2) y^((k-j)(k-j-1)/2).             (2)

This is the original current-root routing formula conditioned on k distinct entering roots.

Here is the complete finite-ULC transfer, avoiding an unstated infinite-order version. For integer N define arrays, 0<=j<=N,

    A_j^(N)=binom(N,j)(p/N)^j x^(j(j-1)/2),
    B_j^(N)=binom(N,j)(q/N)^j y^(j(j-1)/2).

Dividing by binom(N,j) leaves log-concave positive arrays, so both are ULC(N). Their convolution C^(N) is ULC(2N). For fixed k and N increasing, C_k^(N) tends to b_k/k!. The ULC inequality is

    (C_k^(N))^2 >= [(k+1)/k][(2N-k+1)/(2N-k)]
                      C_(k-1)^(N) C_(k+1)^(N).

Taking the finite-coordinate limit proves b_k^2>=b_(k-1)b_(k+1). Since b_0=b_1=1, its decreasing successive ratios imply b_4<=b_2^3. Ordinary kernels have b_k=z^(k(k-1)/2), also log-concave. Root-count diagonals multiply under actual word composition, so log-concavity, and in particular c<=a^3, holds for every word.

## 3. Exact chronological quartet cocycle

For any admissible stochastic graft kernel K and any actual INDEPENDENT suffix L,

    T(KL)=T(K)+b_4(K)T(L).                            (3)

To prove this, compare completing after K immediately with applying L and then completing. If K leaves four roots, no original tips have merged and the change in balanced probability is T(L); that branch has probability b_4(K).

If K leaves three roots, one is a previously formed cherry and two are singletons. The suffix, with its ordinary completion, treats the three opaque current roots exchangeably. Every rooted three-root topology consequently has probability 1/3. Exactly one of these three possibilities joins the two singletons first and makes the completed four-tip tree balanced. Its balanced probability is therefore 1/3, equal to immediate ordinary completion. This argument retains one routing draw per current root, including the cherry as one root.

With two roots, their tip counts are either 2+2 or 3+1, fixing the eventual balanced/caterpillar shape. With one root the shape is already fixed. Thus these branches cause no change, proving (3). It works for every abstract stochastic K in the capped graft algebra, not only an actual prefix. No commutation of K and L is used. Ordinary completion of four singleton roots is balanced with probability 1/3, so T(E(z))=0.

## 4. Exact one-cell contrast

Put A=1-x, B=1-y, u=pA, v=qB and d=1-b_2=p^2 A+q^2 B=pu+qv. For three lineages in an arm with survival s, the probability that all three have coalesced by its end is

    h_3(s)=1-(3/2)s+(1/2)s^3=(1-s)^2(s+2)/2.

For a four-root routing allocation:

- With all four on one arm, arm evolution plus root completion is ordinary Kingman, so the balanced probability is 1/3.
- With a 3+1 split, the deviation is -h_3(s)/3 for the three-root arm. If that arm has not fully coalesced, ordinary completion still gives balanced probability 1/3.
- With a 2+2 split, the deviation is (2/3)(1-x)(1-y): it differs from 1/3 only when both within-arm pairs have already coalesced, forcing the balanced shape.

Using the binomial routing probabilities gives

    T(B_I)=4p^2q^2 AB -(4/3)pq[p^2 h_3(x)+q^2 h_3(y)]
          =(2/3)[q u^3+p v^3-3pq(u-v)^2].             (4)

This formula includes all routing and coalescence branches and concerns the final rooted topology, not just survival.

## 5. A uniform positive cubic bound

If T(B_I)<=0, the upper bound T(B_I)<=144d^3 is immediate. Otherwise assume p<=q, interchanging the arm names if necessary. If u>=3v, then u<=p and

    q u^3+p v^3-3pq(u-v)^2
      <=u^2[u(q+p/27)-(4/3)pq]
      <=p u^2[p/27-q/3]<0,

contradicting positivity. Thus u<3v. Since d=pu+qv>=qv and q>=1/2, v<=2d and u<6d. Dropping the negative square in (4),

    T(B_I)<=(2/3)(q u^3+p v^3)<=144d^3.              (5)

The other arm ordering is symmetric. This is valid for every strict x,y,p, without a weak-cell or small-loss restriction.

For a physical cell with its positive trailing ordinary gap L=B_I E(z), equation (3) gives T(L)=T(B_I), while 1-a(L)>=1-a(B_I). Thus (5) also holds for each full append. An ordinary append has T=0.

## 6. A nonlinear semialgebraic invariant on full kernels

Take the source-compatible capped stochastic graft algebra, with its multiplicative characters a=b_2 and c=b_4. Impose

    0<a<1, 0<=c<=a^3,
    T(K)<144(1-a)^3.                                 (6)

This is a finite polynomial/linear predicate on the full kernel. It keeps the actual affine graft constraints and nonnegative stochastic rows; it is not a condition on arbitrary unrelated matrices.

Initialization at any E(z), 0<z<1, satisfies c=z^6<=z^3=a^3 and T=0<144(1-z)^3. If K is ANY abstract state in (6) and L is an actual append, put b=a(L). The diagonal constraint is preserved by c(KL)=c(K)c(L) and c(L)<=b^3. By (3) and (5),

    T(KL)<144[(1-a)^3+a^3(1-b)^3]
          <=144(1-ab)^3,

because the two nonnegative quantities 1-a and a(1-b) sum to 1-ab, and the sum of their cubes is at most the cube of their sum. This proves induction for every abstract invariant state and every legal chronological append. No source-word length, ordinary-time floor or hidden routing observation is introduced.

The nonstrict inequality T<=144(1-a)^3 holds on the full Euclidean source closure by continuity. A strict violation is therefore a source-closure NO certificate. No claim of completeness or a newly identified nonattained point inside that closure is made.

## 7. A full-kernel witness beyond the older diagonal test

Let 0<t<=1/1000 be rational, and put

    s=1-t, z=1-t^2, r=1-t^4,
    A_t=E(z) B_I(s,s,1/2) E(z),
    K_t=t A_t+(1-t)E(r).                              (7)

Both constituents are actual strict INDEPENDENT kernels at every cap, using the same parameters across arities. Hence K_t is a rational, fully coherent stochastic kernel in their convex hull. The convex combination is an external mathematical relaxation, not a newly admitted source operation.

Let a_1=b_2(A_t)=z^2(1-t/2), a_0=r, a=b_2(K_t), and e=1-a. Then

    t^2/2<=e<=t^2/2+2t^3+t^4<=(2/3)t^2<=t^2.         (8)

The lower bound uses a_1<=1-t/2. The upper bound uses 1-z^2<=2t^2, followed by t<=1/1000. Also 0<a_0-a_1<=t: positivity follows from a_1<=1-t/2 and r=1-t^4, and the upper bound follows from 1-a_1<=t/2+2t^2.

At equal arms and routing 1/2, (4) gives T(B_I)=t^3/12. Equation (3) then gives T(A_t)=z^6 t^3/12, since b_4(E(z))=z^6. Its exact affine dependence on a probability mixture yields

    T(K_t)=z^6 t^4/12>=t^4/24>144t^6>=144e^3.        (9)

Here z^6=(1-t^2)^6>=1-6t^2>=1/2, and t^2<1/3456 follows from t<=1/1000. Thus K_t violates the full-topology invariant and is outside the INDEPENDENT closure at every cap m>=4.

It nonetheless passes the previous pair/triple test. Indeed

    b_3(A_t)=a_1^3-z^6 t^3/8.

The exact cubic mixture identity gives

    b_3(K_t)-a^3
      =t(1-t)(a_0-a_1)^2[(2-t)a_0+(1+t)a_1]-z^6 t^4/8.

Its absolute value is at most 3t^3+t^4/8<4t^3. Using (8),

    (b_3(K_t)-a^3)^2<16t^6<(81/2)t^6<=324e^3.

Also a>1/2. Hence the accepted scalar inequality (b_3-b_2^3)^2<=324(1-b_2)^3 does NOT reject this family.

The auxiliary b_4<=a^3 condition does not reject it either. For the equal-arm bare bigon,

    b_4(B_I)=s^6/8+s^3/2+3s^2/8
            <=1-3t+(15/4)t^2<=1-(5/2)t.

The first bound uses the elementary second-order Taylor upper bounds of (1-t)^6 and (1-t)^3 on [0,1]. The second holds for t<=1/1000. Positive padding can only reduce b_4, so

    b_4(K_t)<=1-(5/2)t^2<1-2t^2<=a^3,

where the last inequality uses (8) and (1-e)^3>=1-3e. The violation in (9) therefore genuinely uses completed quartet shape in addition to the survival coordinates.

## 8. Prior scope and original G3 interface

The older pair/triple polynomial test is explicitly reused from
https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-05-dot-g3-source-sign-and-convex-gap-0057z/slot-no/NONLINEAR-SLOT-NO-FINAL.md .
The fact that convex mixtures satisfy all affine source guards, and also the source's polynomial identities, uses its accepted affine-hull theorem and is not a new algebraic-density claim. Family (7) therefore illustrates a nonlinear full-topology constraint that survives both those relaxations and the stated older diagonal test.

Within the original retained-core compiler, (6) can constrain the SAME shared symbolic INDEPENDENT slot kernel. A whole-profile NO still requires exclusion of every point of the coupled target fibre for every admitted alternative core. No hidden value is assumed observed. Fresh/private source assumptions are retained; protected parameters, genuine cross-slot ties and paired/conditional registers require their own exact source update proof.

The new proof uses an actual chronological quartet cocycle and a classical binomial-convolution theorem. It does not promote diagonal exchangeability, a graphon or an external mixture to a complete source realization. No historical priority, optimal coefficient, general G3 recognition or original-G4 stopping conclusion is claimed.
