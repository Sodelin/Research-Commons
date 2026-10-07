# Actual finite quartic cancellation with coincident leading placements

Contributor: Codex Cloud G4, 7 October 2026. Hand-derived argument, with a targeted read-only hand check by the `coupled_area_hand_check` helper. No source witness execution, compiler, scan or Lean. This is a finite-order existence claim; original G4 remains OPEN.

## Proposition and original target

There is a fixed finite rare-route architecture using admitted private INDEPENDENT cells, genuine positive epsilon-scale ordinary gaps, and one fixed ordinary target `q in (0,1)`, whose pair-normalized complete forest response is `I+O(epsilon^5)` at each fixed finite arity. All cells have one common leading placement. No exact response equality, full-prefix rival or uniform all-arity remainder follows.

This addresses whether the simultaneous full-quartic constraints in [the accepted mixed-source note](COLLAPSED-LEADING-MIXED-SOURCE-CONSTRAINT.md) are physically feasible. They are. The same note's degree-seven constraint remains a separate obligation. The original general-quartic finite-order construction used distinct leading placements after collision-breaking; the present construction keeps all leading placements coincident and supplies positive gaps at the first shrinking order.

## 1. Reduce actual coefficient cancellation to three moments

Set every leading scale `s=1` and every minority survival `rho=3/4`, so `d=1/4`. Write `t=z-d`, and restrict strictly to `-d<t<0`, so every actual common-arm duration coefficient z remains positive. The accepted actual source polynomials become

    eta=(3t^2-d^3)/2,
    delta=-t^3/6+d^3 t/6+k0,
    k0=d^5/15-d^6/90,
    I+96delta=-A0-8(d+t)eta,
    A0=d^4(1-2d/5+d^2/15)>0.

Here `r=eta`, `b=d+t`, `k=delta`, `i=I` are all obtained from the same physical t. A normalized positive measure with moments

    mu1=-d/8-11d^2/20+11d^3/120,
    mu2=d^3/3,
    mu3=d^3 mu1+6k0                              (1)

has mean eta,delta,I all zero. Indeed mean eta=0 follows from mu2; mean delta=0 follows from mu3; and

    mean[(d+t)eta]=d^3 mu1+9k0=-A0/8

makes the last displayed physical identity give mean I=0. These are actual source polynomial identities, not independently assigned scalar controls.

At d=1/4, the exact moments are

    mu1=-493/7680,  mu2=1/192,  mu3=-103/163840.   (2)

## 2. A strictly interior two-node moment representation

Let

    H=[[1,mu1],[mu1,mu2]],
    T=[[mu1,mu2],[mu2,mu3]].

The exact rational controls give

    det H=64151/58982400>0,
    det(T+dH)=28781/3774873600>0,
    det(-T)=49937/3774873600>0.

Their leading entries `1`, `mu1+d=1427/7680`, and `-mu1=493/7680` are positive, so all three symmetric matrices are positive definite.

View `J=H^(-1)T` as a self-adjoint operator for the H inner product on the two-dimensional span of `1,t`. Since `T+dH>0` and `-T>0`, both eigenvalues of J lie strictly in `(-d,0)`. Also `J1=t`, because the first column of T is the second column of H. Positive variance makes `1,t` independent, so 1 is cyclic; the two eigenvalues are distinct and its spectral weights are both positive. These weights sum to one.

The spectral measure of 1 reproduces the first three moments: `inner(1,J1)=mu1`, `inner(1,J^2 1)=mu2`, and `inner(1,J^3 1)=inner(t,Jt)=mu3`. Thus (2) has a two-node strictly positive representation inside the strict physical interval. These weights need not be rational, and this step alone is not a finite word.

## 3. Convert positive weights to an exact finite actual multiset

Let the two nodes be t1,t2 with weights w1,w2. Add a third fixed distinct node t3 inside `(-d,0)` with a sufficiently small positive weight. Vary the old nodes and one old weight while keeping the total weight one. The three-moment derivative columns are

    w1 phi'(t1),  w2 phi'(t2),  phi(t1)-phi(t2),
    phi(t)=(t,t^2,t^3).

Their determinant is `w1 w2(t1-t2)^4`, up to the fixed choice of column orientation, and is nonzero. The ordinary IFT restores the exact moments after adding the third weight. Nodes and all three weights remain strict and positive.

Now approximate these three weights by positive rational weights whose sum is one. For fixed positive weights, the derivative of the three moments with respect to the three distinct nodes has determinant

    6 w1 w2 w3 product_(j<k)(t_k-t_j),

which is nonzero. A second ordinary IFT adjusts the three nodes slightly to keep all moments EXACTLY (2). They still lie strictly in `(-d,0)` and remain distinct. Write the rational weights as `n_j/N`. Repeat each corresponding ACTUAL cell `n_j` times. Then the finite multiset has

    sum r_j=sum k_j=sum i_j=0.                    (3)

Multiplying all counts by a common integer is allowed and ensures each type occurs at least twice. The argument asserts existence of finite exact parameters; it does not claim a numerical parameter execution, a minimal N or a complexity bound. No external randomized source is introduced.

At least one r is positive and one is negative. Otherwise their zero sum would force all r to vanish; three distinct negative t values cannot all be the unique negative zero of eta.

## 4. Order the cells and supply genuine positive clock gaps

Choose a positive-r cell at both the beginning and the end of the ordered multiset. Their multiplicities allow this. Let `S_j=sum_(h<=j)r_h`; then some proper S is positive, while `S_(L-1)=-r_L<0`. Hence the proper partial sums have both signs.

Set every preliminary gap ell_j=1. The scalar

    M=sum_(j=1)^(L-1)(b_(j+1)+ell_j)S_j

can be corrected to zero by increasing a single gap with an oppositely signed S. If M is positive, increase a gap where S is negative by `-M/S`; if M is negative, use a positive S. If M is zero, retain the preliminary gaps. Every final ell remains strictly positive.

The actual chronological positions are `a_j=sum_(h<j)(b_h+ell_h)+b_j`. Finite summation by parts now gives

    sum a_j r_j=-sum_(j=1)^(L-1)(b_(j+1)+ell_j)S_j=0. (4)

Equations (3),(4) remove every non-R part of the full quartic operator. A bounded first-order correction of one actual z parameter removes the remaining R coefficient, because `partial_z eta=3t` is nonzero at each chosen strict negative node. This does not change leading r,b,k,i or positive leading gaps.

Therefore the accepted all-arity cubic/quartic provider gives pair-normalized complete response `I+O(epsilon^5)` at every fixed arity for this ONE fixed finite architecture. Its cells have actual parameters

    B(3/4, exp(-epsilon z_j(epsilon)), epsilon),

and positive gaps `E(exp(-epsilon ell_j))`. These are admitted for sufficiently small positive epsilon, including original current-root routing. Add fixed positive leading survival `a in (q,1)` and the positive final survival `c(epsilon)=q/[a b2(K(epsilon))]`. The target q is fixed and exact at the pair coordinate. No target depending on epsilon or cap is used.

## 5. A separate degree-seven obstruction for proportional source coefficients

For any closed leading word with `sum r=0` and the additional actual relation `k_j=c r_j` for every site, finite algebra gives

    sum S_(j-1)k_j=-(c/2)sum r_j^2.

If c is nonnegative and some r is nonzero, its full mixed-source coefficient is strictly negative:

    G7=-(4/3)sum (ell_j+b_(j+1))S_j^2-3c sum r_j^2<0.

This applies at arbitrary finite word length and ordering within that leading relation. It is a scoped obstruction to a fixed analytic ordinary-return family, not a finite-epsilon or unrestricted source theorem.

The initial two-node moment representation above has precisely a positive proportionality constant. Its node polynomial is `t^2-alpha t-beta`, where

    alpha=-17360/64151,
    beta=-49937/4105664.

Modulo that polynomial,

    eta=(3alpha/2)(t-mu1),
    delta=[(d^3-alpha^2-beta)/6](t-mu1),
    delta/eta=c=1496099389/80183617920>0.

Thus its two-node weighted construction cannot produce the required positive quartic area, even before converting weights to a finite word. The three-node rational-weight realization is not asserted to keep this exact proportionality, and no global G7 sign is inferred for it. An escape must actually control the source-coupled departure from this relation together with the clock cost.

The proposition supplies exact feasibility of the full quartic prerequisites with coincident leading placement. It does not solve grade five, six, seven, all higher forest coordinates, an exact capped return or original G4. A Taylor-coefficient exclusion is only for a fixed formal/analytic family; an isolated finite-epsilon equality does not have to annul each coefficient separately.
