# Global weak-word loss constraints on the exact ordinary fibre

Codex G6, 8 October 2026. NEW HAND ARGUMENT pending independent review. This is a source-specific constraint used in the second COMPLETE G4 attempt, not a finite-forcing theorem. Natural INDEPENDENT private words only; original graph/ties/multiport transfer remains open. All lengths are finite, all natural coins interior, and one actual tuple supplies all arities.

## Exact source variables

Split every word factor into one bare strict bigon or one positive ordinary population; keep all physical gaps. For a bare cell with survivals x,y and coin g put q=1-g and

    u=g(1-x), v=q(1-y), d=gu+qv=1-b2,
    S=gq(u-v)^2,
    Delta=b3-b2^3=3S-u^3-v^3+d^3,
    R=b3/b2^3.

Thus 0<u<g, 0<v<q, 0<d<1. The exact source formulas and Jensen/quartet identity are inherited from Dot's accepted EXACT-JENSEN-ENERGY-WORKING.md and its actual quartet provider. Define d=S=0, R=1 for the separate ordinary factors when summing the bare-cell losses below. Their positive durations still contribute to the target pair time.

## Universal cubic estimate, without a chart or coin floor

For EVERY strict bare triple,

    u^3+v^3 <= 2S+432d^3,
    Delta >= S-431d^3.                                  (1)

If u,v<=6d, their cube sum is at most 432d^3. If u>6d, d>=gu implies g<1/6 and q>5/6. Also v<=d/q<(6/5)d<u/5, hence u-v>(4/5)u. Using u<=g gives

    u^3 <= g u^2 < (25/(16q))S < (15/8)S,
    v^3 < (216/125)d^3 < 2d^3.

This proves (1) in this case too. The v>6d case is the same calculation with the two physical arms exchanged. No zero/infinite arm or endpoint coin is admitted. The boundary inequalities used above are upper bounds for actual strict tuples.

## Exact ordinary pair/triple endpoint

Assume d_i<=1/6 for every bare cell, and the whole physical word has exact ordinary pair/triple diagonals. Equivalently sum_i log R_i=0 because separate ordinary factors have R=1. Let

    Z=sum_i d_i^3,
    P=sum_(log R_i<0) |log R_i|
      =sum_(log R_i>0) log R_i.

Then

    P <= 862 Z,
    sum_i S_i <= 1293 Z.                                (2)

For the log bound, sampling consistency and the selected-pair union bound give b3>=1-3d>=1/2, while b2^3>1/2. Also b3,b2^3<=1. By the mean value theorem log R=Delta/xi for xi between b3 and b2^3. If Delta<0, (1) implies Delta>=-431d^3 and therefore log R>=2Delta>=-862d^3. If Delta>0, log R>=Delta. Consequently S<=log R+431d^3 in the positive case and S<=431d^3 in the negative case. Summing and using exact sum log R=0 proves (2).

For EVERY actual proper prefix W_j,

    |log R(W_j)| <= P <= 862 Z.                          (3)

Indeed a partial sum of real increments with total zero lies between minus the total negative part and the total positive part. This is latent prefix control derived from endpoint equations; no internal prefix is granted as an observation.

If the physical pair target time is tau<=1/6, multiplicativity gives sum bare c_i+sum ordinary t_j=tau, with c_i=-log(1-d_i)>=d_i. Thus the cell-size premise follows automatically and

    Z <= (max_i d_i)^2 sum_i d_i <= B^3 <= tau^3,
    B=sum_i c_i.

This is uniform over finite word count and every biased/rare/noncompact/multiscale tuple. It is a rough quantitative constraint, not a claim that all weak cells lie in the compact parabolic chart.

## Adding the exact completed quartet equation

Suppose additionally the completed quartet statistic T(W)=Pr(balanced)-1/3 equals its ordinary value zero and b4(W)=exp(-6tau). The source Jensen defect has the exact factorization

    J=gu^3+qv^3-d^3
      =S[(1+g)u+(1+q)v]
      >= max(u,v) S >=0.                                (4)

This is the cubic identity for a two-point loss distribution, NOT an ordinary-mixture representation of an INDEPENDENT word.

Use the accepted exact whole-word formula, with a_j=b2(K_j)^3, b_j=b3(K_j), c_j=b4(K_j), C_j=product_(l<=j)c_l and R_j=R(K_1...K_j):

    sum_j C_(j-1) J_j
      =sum_(j<N)(w_j-w_(j+1))(1-R_j),
    w_j=C_(j-1)a_j/R_(j-1),
    w_(j+1)/w_j=c_j a_(j+1)/b_j<1.

All actual ordinary factors remain in these weights. Endpoint R_N=1 implies

    w_N=C_(N-1)b_N >= C_N=exp(-6tau),
    w_1=a_1<=1,
    C_(j-1)>=C_N.

By (3), 1-R_j<=1-exp(-P). The right side is at most [w_1-w_N][1-exp(-P)]. Therefore

    sum_j J_j <= (exp(6tau)-1)[1-exp(-P)]
               <= 862(exp(6tau)-1) Z,                   (5)
    sum_j max(u_j,v_j) S_j <= 862(exp(6tau)-1) Z.

For tau<=1/6, exp(6tau)-1<=12tau, so the last bound is <=10344 tau Z. Equations (2)-(5) couple exact ordinary endpoint equalities to loss anisotropy and latent-prefix excursions at EVERY finite word length. They do not use a fair coin, common scale, compact shape, or source-dependent negative ordinary population.

## Why this is not yet the target-fibre guard

The zero-diagonal equations permit arbitrarily many small cells. Bounds (2)-(5) do not force Z=0 and do not recover the hidden prefixes. Balanced u=v cells have S=J=0 but Delta=-d^3, so other cells must compensate their triple defect; the amount and chronology remain source-coupled. Endpoint-approaching coins can have u=v of pair-loss order while one physical arm remains finite. That regime obeys these bounds and is outside the compact-interior parabolic jet proof.

A complete guard must combine D4 and further complete forest equations with the exact chronological square and its two intrinsic source defects. Dropping those defects or bounding them by exact X is invalid by Dot's accepted exact-X-zero cell. This packet supplies uniform conditional controls to use in that next calculation; it does not establish its missing sign, actual all-cap return, all-core transfer, or effective original G4 stopping.

Attribution: exact pair/triple routing, J and its whole-word transport are the accepted Dot Jensen provider; selected-pair projectivity/union bound is the original source property used in the earlier reviewed pair-weak full-forest proof. The elementary physical loss split, uniform log/variance bounds and their quartet-coupled consequences are the present hand derivation. Historical novelty is unassessed. No source program, numerical scan or compiler was executed to establish these inequalities.
