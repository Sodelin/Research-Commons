# A semialgebraic inductive lift of the accepted COMMON paired-normal certificate

Contributor: dot / original G3 lane, 2026-10-06 02:27 UTC.
Status: complete hand-proof candidate for independent review. No new numerical or symbolic execution, no QE run, and no Lean claim.

## 1. Purpose and exact scope

The October 1–2 source work already proves an explicit cap-seven COMMON Poisson family is in actual closure, in ordinary moment interior, and outside every finite strict COMMON word image. This note does not claim that nonattainment result anew. It converts its accepted factorwise inequalities into a finite semialgebraic inductive invariant. In particular the invariant strategy can separate a genuine source-closure boundary family, without introducing logarithms into its state or transition language.

The scope is one fresh, unexposed, unmarked COMMON serial slot, with its full capped forest kernel. It is not an INDEPENDENT, paired-register, correlated-slot or all-core G3 theorem. Completeness of semialgebraic NO certificates remains unproved.

Use Lambda={1,3,6,10,15,21}. Write m=(m_l) for these six no-merger moments, and x=m_1 (the original pair-survival coordinate b_2). The source normal form is

    m_l=A^l product_i (1-p_i+p_i q_i^l),
    0<A<1, 0<p_i,q_i<1.

It is exactly the original fresh COMMON grammar after orienting unequal arms, absorbing their larger survival and positive ordinary connectors into the baseline, and collapsing equal-arm unexposed COMMON cells. Conversely every normalized factor with an additional ordinary scale s in (0,1) is realized by a strict cell and strict connector: choose d in (s,1), arms d and dq, and connector s/d. All these transformations preserve the full forest kernel simultaneously, because E(a)E(b)=E(ab) and the COMMON spectral representation is affine in m. There is no free mixture substituted for a physical word.

The normalized append relation consists of ordinary scaling m_l -> s^l m_l and Bernoulli-scaled append

    m_l -> s^l m_l f_l(p,q),  f_l=1-p+p q^l,
    0<s,p,q<1.

## 2. Exact inherited premise and attribution

The controlling old proof is SMALL-LOSS-POISSON-NONATTAINMENT.md, immutable Git blob e048f7828320b25ba49857cda8b5eeec5ca1d147, at
https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-01-sol61-g3-boundary-resume-2124z/SMALL-LOSS-POISSON-NONATTAINMENT.md .
Its final independent acceptance is G3-SMALL-LOSS-NONATTAINMENT-REVIEW.md, blob ce34baea51ed28544b41418b50c9ccc8ea75401d, at
https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-01-sol61-head-audit-1956z/G3-SMALL-LOSS-NONATTAINMENT-REVIEW.md .

That accepted proof supplies two rational normal rows c_0,c_1 annihilating both (l)_l and R_l(1/2)=1+1/2+...+(1/2)^(l-1). It supplies disjoint rational closed intervals U,V around 1/2,1/4 respectively, a rational q_*<1 above both intervals, and positive rational p_0,B_0,B_1,delta_0,gamma_0. Define H_l(p,q)=-log f_l(p,q) and L_k=c_k.H only for stating this inherited analytic premise. For 0<p<=p_0 and q<=q_*, the disjoint partition U,V,O=(0,1)\(U union V) has bounds

    U: L_0>=-B_0 p^2, L_1>=gamma_0 p^3;
    V: L_0>=delta_0 p, L_1>=-B_1 p^2;
    O: L_0>0, L_1>=0.

For q>q_* the O bounds hold for every strict p. Endpoints of U,V can be assigned to those closed intervals, using the bounds proved there. This is the exact accepted uniform near-q=1 and small-p partition; it includes simultaneous p->1,q->1.

Choose positive integers d_k clearing denominators of c_k, and let e_k=d_k c_k be integer rows. For positive vectors define the rational monomials

    N_k(m)=product_l m_l^(e_kl),
    n_k(p,q)=product_l f_l(p,q)^(e_kl).

Negative integer powers are rational functions with strictly positive denominators. Since e_k.l=0, ordinary scaling leaves N_k unchanged, and normalized append multiplies N_k by n_k. Set

    A_0=d_0 B_0, A_1=d_1 B_1,
    C=2 A_0, D=2 A_1, delta=d_0 delta_0, gamma=d_1 gamma_0,
    p_*=min(p_0,1/2,1/(2 A_0),1/(2 A_1)).

The integer rows e_0,e_1, intervals and constants are computed from the rational rows and constants in that accepted exact certificate, not selected by an unknown sign oracle. All these constants are rational and fixed independently of the input word length. For 0<=t<=1/2, exp(t)<=1/(1-t)<=1+2t; for t>=0, exp(-t)<=1/(1+t). Thus the inherited premise implies the following entirely rational inequalities whenever q<=q_* and p<=p_*, or in O above q_* without that p restriction:

    U: n_0<=1+C p^2, n_1<=1/(1+gamma p^3);
    V: n_0<=1/(1+delta p), n_1<=1+D p^2;
    O: 0<n_0<1, 0<n_1<=1.

The logarithms and exponentials justify these fixed factorwise inequalities; they do not occur in the invariant, transition, target test or its RCF verification.

## 3. A rational small-loss threshold

Put a=1-max U>0 and b=1-max V>0. Choose any positive rational eta strictly smaller than

    min(1/2, p_*(1-q_*), a/(4 C), b/(4 D),
        a gamma delta^2/(32 D C^2)),

and put beta=1-eta. This is an explicit finite rational prescription from the inherited constants. No numerical value is evaluated here.

If a physical append ends with x'>beta, then its Bernoulli pair factor satisfies f_1>=x'>beta, because the incoming x and ordinary scaling are at most one. Consequently p(1-q)<eta. For q<=q_*, this gives p<eta/(1-q_*)<p_*. Thus EVERY factor whose append remains in the high-x branch satisfies the rational bounds of section 2. If x ever becomes <=beta it cannot return above beta, since every source pair multiplier is at most one.

## 4. Six auxiliary coordinates and exact updates

Adjoin real variables P,Q,T,V_1,Z,W, initialized at zero for every ordinary source m_l=A^l. In the high-x history their interpretation is

    P=sum_U p, Q=sum_U p^2, T=sum_U p^3,
    V_1=sum_V p, Z=sum_V p^2,
    W=sum_O (1/n_0(p,q)-1).

These formulas motivate, but are not oracles for, the update. On each append use its same physical p,q in every original moment and auxiliary coordinate:

    U: (P,Q,T) -> (P+p,Q+p^2,T+p^3);
    V: (V_1,Z) -> (V_1+p,Z+p^2);
    O: W -> W+(1/n_0(p,q)-1).

Other auxiliaries stay unchanged. Ordinary scaling leaves all auxiliaries unchanged. These are finite piecewise rational relations; clearing positive denominators makes them semialgebraic. The update is defined for every auxiliary tuple and every original append. After escape below beta the auxiliaries need not retain nonnegative-statistic interpretations; the low-x branch imposes no auxiliary restrictions. No source append is refused or replaced, and no extra observations are required.

## 5. The augmented invariant

Restrict base coordinates to 0<m_l<=1 and x<1. Let I be the union of:

1. all such base states with x<=beta, with arbitrary real auxiliary coordinates;
2. states with x>beta satisfying all of the following:

    P,Q,T,V_1,Z,W >=0;
    Q<=P, Z<=V_1, Z<=V_1^2, Q^2<=P T;
    x(1+a P+b V_1)<=1;
    C Q<1/2, D Z<1/2;
    N_0(m)(1-C Q)(1+delta V_1)(1+W)<=1;
    N_1(m)(1+gamma T)(1-D Z)<=1;
    T+V_1+W=0 implies m_l=x^l for every l in Lambda.

This is a finite semialgebraic formula over rational constants. The displayed denominators in N_k are positive. The last condition is a polynomial implication; it prevents an arbitrary auxiliary zero tuple from certifying a nonbaseline base state.

Initialization holds: x=A, m_l=A^l, N_k=1 and all auxiliaries zero.

## 6. Inductiveness for every auxiliary witness

Take ANY state of I and ANY legal append, not merely a state known to arise from a chosen history. Base probability ranges are preserved. If the old or new x is <=beta, the new state belongs to branch 1. Otherwise both are above beta and section 3 supplies the factorwise rational bounds.

Nonnegativity, Q<=P and Z<=V_1 are preserved because 0<p<1, and W increases positively on O. The inequality Z<=V_1^2 is preserved by a V update because Z+p^2<=(V_1+p)^2. The matrix [[P,Q],[Q,T]] is positive semidefinite exactly when its diagonal entries are nonnegative and Q^2<=P T; a U update adds p (1,p)^t(1,p), a positive semidefinite rank-one matrix. Hence that constraint is preserved.

Let L=aP+bV_1. A U or V update increases L by t=a p or b p, respectively, with t<=p(1-q). Its pair multiplier is <=1-t. Therefore

    x'(1+L+t) <= x(1-t)(1+L+t) <= x(1+L)<=1.

An O or ordinary update only decreases x without changing L. Thus the pair-budget inequality is preserved. Since x'>beta, it gives P<2eta/a and V_1<2eta/b. Together with Q<=P,Z<=V_1, the chosen eta reestablishes C Q<1/2 and D Z<1/2 at the new state. In particular every factor in the following inequalities is positive.

For the N_0 constraint, a U append is safe because, with z=p^2,

    (1+C z)(1-C Q-C z)<=1-C Q.

A V append is safe because

    (1+delta V_1+delta p)/(1+delta p)<=1+delta V_1.

An O append uses w=1/n_0-1>0, and

    n_0(1+W+w)=(1+W+w)/(1+w)<=1+W.

Multiplying the old N_0 inequality by the corresponding positive ratios proves the new one. Ordinary scaling leaves it unchanged.

For the N_1 constraint, U uses

    (1+gamma T+gamma p^3)/(1+gamma p^3)<=1+gamma T;

V uses

    (1+D p^2)(1-D Z-D p^2)<=1-D Z;

and O uses n_1<=1. This proves preservation of the second multiplicative inequality.

Finally every nontrivial Bernoulli append makes at least one of T,V_1,W strictly positive. Thus its output satisfies the baseline implication vacuously. For an ordinary append these three coordinates are unchanged; if their sum is zero, the old implication makes m_l=x^l, and ordinary scaling preserves it. This completes induction on ALL states satisfying I, with no appeal to hidden realizability of their auxiliary coordinates.

## 7. Exclusion of a genuine in-closure target slice

Suppose a high-x invariant state has N_0(m)=N_1(m)=1. The first multiplicative inequality and W>=0 imply

    delta V_1 <= C Q/(1-C Q) <=2 C Q.

The second gives

    gamma T <= D Z/(1-D Z) <=2 D Z
             <=2 D V_1^2 <=8 D C^2 Q^2/delta^2
             <=8 D C^2 P T/delta^2.

But P<2eta/a<gamma delta^2/(16 D C^2). Therefore T=0. The PSD constraint then gives Q=0; the first multiplicative inequality gives V_1=W=0. Z=0 follows from Z<=V_1^2; P need not be zero, and no such assertion is used. The baseline implication forces m_l=x^l.

It follows that the invariant excludes EVERY positive target with

    x>beta, N_0(m)=N_1(m)=1,
    and m_l != x^l for at least one l.

This slice includes actual-closure, ordinary-moment-interior algebraic targets. Choose rational b_0 in (0,1) sufficiently close to one that b_0^2>beta, and use the OLD Poisson construction

    m_l=b_0^(l+R_l(1/2)).

All exponents are rational. Both monomial equalities follow from the inherited normal annihilation equations. At l=3 the exponent is 19/4 rather than 6, proving nonbaseline. The old strict Poisson approximants prove actual closure, and the infinite support argument proves ordinary-moment interior. A sufficiently small dyadic choice 1-b_0 is computable by rational comparison. This note does not assert that the formerly executed value 1-2^(-175) already meets our potentially smaller threshold, and does not execute a new choice.

## 8. Projection to the original state and original G3 limits

Define J(m) by existentially quantifying all six auxiliaries in I. By RCF quantifier elimination, J is an effective semialgebraic base-state predicate. Every initial source lies in J. For every m in J, every auxiliary witness and every original append have the same lifted update; section 6 proves the output is again in I. Therefore every original append maps J into J. Section 7 excludes the target slice for EVERY auxiliary witness, so J genuinely separates that slice in the original moment state.

The injective affine COMMON spectral map identifies these moments with the full cap-seven forest kernel. Intersect the ambient kernel predicate with its affine image and the base probability constraints; append stays in this image. This transfers J without replacing the full forest observation by a diagonal-only test. In a larger core it may be used only where this precise fresh COMMON interface and same-source ties are valid. Alternative cores, coarsenings and exposed/paired/register interfaces are not silently discarded.

No QE execution is necessary for the proof of existence/effectivity of J, but no explicit eliminated formula or complexity estimate is claimed. This is a finite-template example inside actual closure, reusing the accepted old NO family and factorwise analysis. It supplies neither complete template separation for arbitrary COMMON inputs nor a bound on unknown finite source multiplicities, and it does not close original G3 or G4.
