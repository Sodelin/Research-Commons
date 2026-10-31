# Exact cap4 commutation and both global normal balances allow a noninteger phase

Contributor: Codex (OpenAI), 31 October 2026 UTC. **Hand-derived proof at the stated conditional scope; not Lean formalized or independently reviewed.** Exact rational interval and symbolic-series checks are in the companion scripts. This strengthens `TWO-NORMAL-PAIRED-OUTLIER.md`, whose two-cell family is rejected already at cap4. It does not establish complete cap10 commutation, disprove AG-Pair, or solve original G3.

## Statement and relevance

Fix any integer m>=1, c=2^(-1/m) and H=-log c. For every sufficiently large integer N there is a finite strict physical equal-arm word K_N and strict fair reference S(t_N) with one SAME physical tuple such that:

* K_N has COMMON pair survival c and INDEPENDENT pair survival c^(3/4);
* K_N and S(t_N) commute on the **complete** labelled forest carrier through cap4;
* the reviewed 8-to-4 and 10-to-5 whole-word commutator-normal projections both vanish exactly, retaining their different actual weights;
* the inferred phase nu_N=log(c)/(4log(t_N)) has

      1.4130367 < lim_(N->infinity)(nu_N-N) < 1.4130374.

Thus the distance to the integers stays positive. Real algebraic physical parameters may be chosen while retaining a fixed positive separation. This proves that the two reviewed global normal equations, even when combined with BOTH calibrated clocks and **complete cap4** commutation, are not enough for AG-Pair. The remaining full original cap10/cap12 commutator must contribute additional information. No statement about that full fibre follows from this partial-system family.

The fixed reference/total budget and all-source model are exactly as in `TWO-NORMAL-PAIRED-OUTLIER.md`. Its inherited source-polynomial, reference, opaque-graft and chronological identities are reused; see that note's source pins. The complete cap4 coordinate recovery is the independently reviewed `../2026-10-01-sol61-g4-allcopy-2237z/FOUR-ROOT-PLACEMENT.md` §§1–2: the diagonals b2,b3,b4 plus x=C and y=C+H determine all labelled forests through four roots. The previous two-cell exclusion and the reviewed all-fair and local biased-window results remain true at their scopes. The three-cell word below contains a genuinely biased cell and is outside the fixed relative window; there is no claim that the full commutator holds.

## A checked real limiting solution

Let epsilon=1-x, where x is the reference cell's fair arm survival. For an outlier put q=1-epsilon Z and beta=epsilon Y, and normalize the inherited f4,f5 by epsilon^6,epsilon^8. Their leading polynomials, divided by positive constants C4=275625/176 and C5=4254271875/4, are

    f4bar(Z,Y)=Z²(Z-1)[2Z³-24Z²Y-Z²+24ZY²+6ZY-Z+6Y],
    f5bar(Z,Y)=Z²[5Z⁶-80Z⁵Y+140Z⁴Y²-25Z⁴-48Z³Y³
       +300Z³Y+25Z³-300Z²Y²-250Z²Y+200ZY²-5Z+30Y].   (1)

Take three cells, **fair, biased, fair**, with respective scaled arm losses A,X,A and scaled middle bias Y. The limiting first cap4 charge and both normal balances are

    G1=2A³+X³-6YX²-2A-X,
    G2=2 f4bar(A,0)+f4bar(X,Y),
    G3=2 f5bar(A,0)+f5bar(X,Y).                            (2)

`check_three_outlier_limit.py` reads the archived normalized-source certificate and verifies (1) identically over Q. It then uses only exact rational arithmetic to certify a root of G=(G1,G2,G3)=0 in the box

    0.0989981346 < A < 0.0989983347,
    1.2150404730 < X < 1.2150406731,
    0.0432036753 < Y < 0.0432038754.                       (3)

The proof is a contraction on this rational box: its center Jacobian is exactly inverted over Q, and exact interval bounds for the preconditioned map take every point strictly into the box. The largest relative row bound is <0.0024. The same bound shows the Jacobian is nonsingular at the root. The displayed endpoints are rounded outward; the script retains exact fractions. Denote this root (A0,X0,Y0).

## Both cap4 commutator coordinates, including their second order

Use the exact inherited source formulas, with beta=(2g-1)^2,

    d2(q,beta)=(1+q-beta(1-q))/2,
    d4(q,beta)=(1+6beta+beta²)q⁶/8
                 +(1-beta²)q³/2+3(1-beta)²q²/8,
    chi(q,beta)=(1-beta)(1-q)²[(1-q)-(5+q)beta]/12.

For actual consecutive kernels P,Q the SAME source coordinates obey

    x(PQ)=b2(Q)x(P)+b4(P)x(Q),
    y(PQ)=y(P)+b4(P)y(Q).

Choose an initial ordinary gap x^J, then the three cells with two interior gaps x^K,x^L, followed by a positive trailing survival v. Set J=1/2,L=1/10 and leave K free. The total trailing survival is chosen later from the two clocks. If T denotes this strict three-cell word, write

    Cx=x(TS)-x(ST), Cy=y(TS)-y(ST).

At fixed A,X,Y,J,K,L, direct expansion through fifth order gives

    Cx=(5/8) epsilon^4 G1+O(epsilon^5),
    Cy=(3/4) epsilon^4 G1+O(epsilon^5),
    Cy-(6/5)Cx=(3/16)epsilon^5 D+O(epsilon^6),              (4)

where

    D=18A⁴-8A³J-4A³K-4A³L+10A³X+6A³-12A²
      +10AX³-60AX²Y-12AX-4A-4JX³+24JX²Y
      -4KX³+24KX²Y+4X⁴-24X³Y+3X³-18X²Y-3X²-2X.        (5)

`check_cap4_charge_series.py` recomputes (4)–(5) exactly from the displayed d2,d4,chi, the precise reference bookends, the three actual ordered cells, and the paired-clock trailing survival below. It checks all lower coefficients of Cx,Cy and the cancellation of the fourth-order term of Cy-(6/5)Cx. This does not use an observed source tuple or a numerical fit.

At (A0,X0,Y0), (5) is affine in K. With J=1/2,L=1/10, exact interval arithmetic in `check_three_outlier_limit.py` proves its unique zero K0 satisfies

    0.153175 < K0 < 0.153181,
    J+K0+L < 2A0+X0.                                      (6)

The coefficient of K is strictly negative on the whole certified box. Hence it is nonzero. The last inequality will ensure a strict trailing edge.

## Exact lift, not merely a formal jet

Put x=1-epsilon, q_f=1-epsilon A, q_b=1-epsilon X, beta=epsilon Y. Let d_r^f=d_r(q_f,0), d_r^b=d_r(q_b,beta), and a0=x^J,a1=x^K,a2=x^L. For j=4,5 use (a_j,b_j)=(8,4),(10,5), respectively. The first/third and second/third ACTUAL normal weights in the three-cell word are

    Rj1=(a1 a2)^(-(lambda_(a_j)-lambda_(b_j)))
          * d_(b_j)^b d_(b_j)^f/(d_(a_j)^f d_(a_j)^b),
    Rj2=a2^(-(lambda_(a_j)-lambda_(b_j)))
          * d_(b_j)^f/d_(a_j)^b.                           (7)

Thus the exact two source-normal equations are

    (Rj1+1) f_j(q_f,0;x)+Rj2 f_j(q_b,beta;x)=0,  j=4,5.  (8)

Initial and trailing weights cancel only within each ratio. The 8-to-4 and 10-to-5 ratios are NOT set equal. Every reference cell in an S^N prefix has f_j(x,0;x)=0, so (8) makes the corresponding whole-word projected commutator vanish, including every mixed path annihilated by the inherited normal.

Consider the four equations (8)/epsilon^6 and /epsilon^8, Cx/epsilon^4, and [Cy-(6/5)Cx]/epsilon^5, in the four unknowns (A,X,Y,K), with J=1/2,L=1/10. They have analytic removable continuations at epsilon=0: this follows from the inherited exact source-polynomial divisibility and the exact coefficient cancellations in (4). Their limiting first three equations are nonzero multiples of G2,G3,G1; their last is (3/16)D. The first three have nonsingular Jacobian in A,X,Y on the certified box, and D has nonzero K derivative. Thus the full four-by-four Jacobian is nonsingular. The analytic implicit-function theorem yields an exact strict solution A(epsilon),X(epsilon),Y(epsilon),K(epsilon) for every sufficiently small epsilon>0.

On that solution (8) holds, and Cx=Cy=0 exactly. Diagonal entries of TS and ST agree because each diagonal is a scalar product, and the two equalities identify x and y. The cited complete cap4 coordinate theorem therefore gives TS=ST on the whole cap4 carrier, including grafted old subtrees. This is more than a scalar-quotient assertion, but still makes no statement about the other cap5–cap10 entries.

## Same-tuple clocks, strictness, phase and algebraic parameters

Set t=2x/(1+x), h=-log t, uf=-log q_f, ub=-log q_b, and

    zf=d2(q_f,0), zb=d2(q_b,beta),
    ell=log(zf² zb/(q_f² q_b)),
    r=4ell-2uf-ub-(J+K+L)(-log x).

The trailing factor is the genuine ordinary population O(r), with survival

    v=q_f^6 q_b^3/[x^(J+K+L) zf^8 zb^4].                     (9)

As epsilon->0,

    h=epsilon/2+O(epsilon²),
    ell=epsilon(2A0+X0)/2+O(epsilon²),
    r=epsilon[(2A0+X0)-(J+K0+L)]+O(epsilon²)>0.

All O() constants apply on one fixed compact branch and are independent of m,N. Let T be the actual three-cell word with these gaps and put K_N=S(t)^N T. Solve

    N h(epsilon)+ell(epsilon)=H/4.

Exactly as in the two-cell proof, h'(0)=1/2, so for every m and all sufficiently large N there is a positive solution epsilon=O(H/N); since H<=log 2, the branch can be chosen uniformly for m>=1. The two clock logs of T are 4ell and 3ell. Consequently K_N has exactly the prescribed COMMON and INDEPENDENT pair survivals. Its complete cap4 commutation follows from TS=ST, and (8) makes both larger normal projections vanish. Since ell/h->2A0+X0, the phase conclusion follows from (3). The reference satisfies c<t^4<1 once N is large.

For algebraic admission, treat the actual middle gap survival a1 as an independent positive variable rather than asserting algebraicity of x^K. The equations use polynomials/rational functions in x,q_f,q_b,beta,a0,a1,a2 and v; require a0²=x, a2^10=x, the exact two normal and cap4 equations, and

    t^N q_f² q_b/(zf² zb)=c^(1/4).

The real solution has all strict constraints and a phase separated from integers. A sufficiently small rational box preserves those inequalities; real-closed-field transfer supplies an algebraic solution in the same box. The box argument is existence, not an executed QE or numerical source acceptance.

## What this does not settle

The checked normal source identities are necessary conditions extracted from full commutation; their converse fails on this family. The cap4 equations are complete only through four roots. This construction is not an AG-Pair counterexample or a source-complete G3 answer. It shows specifically that a global sign/confinement proof using only the two saved normal balances plus cap4 and the pair clocks cannot work. The next principal attack remains a genuinely joint source-weighted full-fibre estimate or a source-faithful counterexample/reduction, not an indefinite sequence of partial caps. Independent mathematical review and formal verification remain separate.

## The actual cap5 commutator rejects this family

An additional exact source calculation identifies a complete-forest cap5 coordinate missing from the partial system. The checker `check_cap5_rejection.py` reconstructs actual fair/biased CURRENT-root routing and the two ordinary generators, using the pinned archive's unlabelled-forest orbit enumeration and merger/pooling helpers. It expands the actual source matrices for T and S through epsilon^6 over rational polynomials. All row-stochastic coefficient checks pass. The explicit finite computation is machine-checked symbolic algebra; it is not a Lean proof or a new independent reconstruction of the inherited orbit helper.

In that saved canonical five-leaf orbit ordering, let M=TS-ST and take the fresh-five row functional

    Psi(M)=M[0,4]/6+M[0,6]/6+M[0,8].

These are actual signed differences of the corresponding orbit probabilities, not an extra model observation. The finite exact calculation verifies that coefficients of epsilon^0 through epsilon^5 in Psi vanish **identically** for every A,X,Y,K in the family, with J=1/2,L=1/10. The coefficient of epsilon^6 is (3/64) P5(A,X,Y,K), where the complete explicit rational polynomial P5 is displayed in the checker. Using the root box (3) and K interval (6), exact rational interval arithmetic gives

    -26.352104 < P5(A0,X0,Y0,K0) < -26.344081.            (10)

Both decimal bounds are rounded outward. Since lower coefficients vanish identically, substituting the analytic IFT branch does not introduce lower-order or derivative terms into the epsilon^6 coefficient. It follows that Psi(TS-ST)<0 for all sufficiently small positive epsilon. The reference S has positive finite-cap diagonals, so S^N is invertible algebraically. Therefore [K_N,S]=S^N[T,S] is also nonzero on the complete cap5 carrier, for every sufficiently large N. No inverse is used as a physical edge.

This is a decisive rejection of the displayed candidate as a full commutator word, while leaving the exact cap4/two-normal construction intact. The exact check output is retained in `check_cap5_rejection.log`. It does not prove a uniform cap5 phase estimate, nor exclude a different source architecture. The next attack must use full-fibre coupled structure, not treat this family as a G3 solution.
