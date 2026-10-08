# Actual selected lower equality admits both signs of the 9-to-4 functional

Contributor: Codex role 5, 8 October 2026. HAND CANDIDATE. This is a source-admitted failure of a selected-state sign guard, not a full lower-forest counterexample. All factors are actual strict private INDEPENDENT cells and positive ordinary edges, with one physical parameter tuple across arities. No compiler, QE, full-target solver or numeric IFT witness was run.

The construction extends [the three-cell selected cancellation proof](ACTUAL-LOWER-SELECTED-CANCELLATION.md). Read the [frozen energy identity](EXACT-CHRONOLOGICAL-ENERGY-DEFECT.md) with its mandatory [jet correction](JET-DEFECT-IDENTITY-AND-CORRECTION.md). The inherited cap-four diagonal obstruction remains and excludes every sufficiently small member constructed here from full ordinary equality.

## 1. Claim and fixed target

For every fixed ordinary target survival `q in (0,1)`, there are finite strict three-cell words whose selected representation obeys

    X(W)=Y(W)=T(W)=U(W)=0,

but whose SAME inherited `V=(2/15)ell` is strictly positive; there are also such words with V strictly negative. At least one actual cell f is nonzero. Their pair survival is exactly q. Nevertheless their cap-four diagonals already differ from the target E(q), so these words do not satisfy full lower-cap-eight equality.

Choose once and for all `p in (q^(1/3),1)`. The three prefix ordinary factors are E(p). The final factor is the actual positive calibration

    c(epsilon,t)=q/[p^3 product_r b2(B_r(epsilon,t))].

As epsilon tends to zero this tends to `q/p^3 in (0,1)`. Thus for sufficiently small positive epsilon and t near zero the source word

    W=E(p) B1 E(p) B2 E(p) B3 E(c)

is strict and has exactly `b2(W)=q`. Final right ordinary calibration preserves every selected zero and the sign of V. It also cancels from the normalized diagonal mismatch below.

## 2. Source coordinates and the lower-zero base point

Use the two genuine f-zero branches at `rho=d=1/2` from the separate proof. With `u>0`,

    B_sigma(u)=B(1/2,exp(-u z_sigma(u)),u),
    z_sigma(0)=d+sigma d^(3/2)/sqrt(3),
    W_sigma=sigma d^(9/2)/(9sqrt(3))+d^5/15-d^6/90,
    H_sigma=-12 W_sigma.

Here `H_->0` and `H_+<0`. The accepted cubic and quartic source identities, together with the analytic IFT, give

    f(B_sigma(u))=0,
    h(B_sigma(u))=H_sigma u^4+O(u^5),
    e(B_sigma(u))=(H_sigma/4)u^4+O(u^5).

The branch order is `(-,+,-)` and `u_r=epsilon s_r`, with positive finite scales. Define their leading chronological ratios

    x=p^(-6),    y=p^(-12),    z=p^(-18),    0<x<y<z,
    c1=1/y-1/z,    c2=-(1/x-1/z),    c3=1/x-1/y.

Thus `c1,c3>0`, `c2<0`, `sum c=0`, and `sum c_r/chi_r=0`, where `chi=(x,y,z)`. At zero epsilon the prefix leading survival at cell r is p^r. Choose the positive algebraic-over-p scales

    s_r^0=[|c_r|/(p^(9r)|H_sigma(r)|)]^(1/4).

The leading normalized lower charges are then

    tau_r=c_r epsilon^4+O(epsilon^5),
    zeta_r=[c_r/(2chi_r)]epsilon^4+O(epsilon^5).

The exact normalized lower equations `sum tau=0` and `sum(zeta-tau/chi)=0`, divided by epsilon^4, extend analytically to zero. Their Jacobian in s1,s2 has columns

    4p^(9r)H_sigma(r)(s_r^0)^3 (1,-1/(2chi_r)), r=1,2.

It is nonsingular because x differs from y. Holding s3 fixed, the analytic IFT supplies positive scales `s1(epsilon),s2(epsilon)` with T=U=0 exactly, and each f remains zero. This is the same admitted base construction as before, now with p chosen to accommodate an arbitrary fixed q.

## 3. Actual f controls and four exact selected equations

The divided physical source function

    F_sigma(u,z)=f(B(1/2,exp(-u z),u))/u^3

is analytic at `(0,z_sigma(0))`. Its leading value is `-2 eta(z)/15` and its z derivative is nonzero on either branch. Consequently there is an analytic two-variable physical chart `z_sigma(u,v)` with `F_sigma(u,z_sigma(u,v))=v`; v=0 is the prior f-zero branch.

Introduce three independent small real coordinates lambda_r by taking

    z_r=z_sigma(r)(epsilon s_r, epsilon lambda_r/s_r^3).

Then the actual bare cell has EXACTLY

    f(B_r)=epsilon^4 lambda_r.                       (1)

This is a chart of the original arm survival and inheritance parameters. It does not assign f,h,e independently. Small coordinates preserve strict positive z, interior inheritance and arm survivals. All other scalar changes are those of the same cell.

At lambda=0 all three f vanish for every scale. Divide the four exact normalized equations X/b7, Y/b6, T/b4, U/b4 by epsilon^4. These extend analytically to epsilon=0 in this chart: f is (1), and the lower cubic coefficient vanishes identically on the unperturbed branches while the v perturbation is order epsilon. At the base point the first two equations have zero scale derivatives, and their lambda columns are proportional to

    p^(21r)(chi_r,1), r=1,2,3.

The columns for lambda1,lambda2 are independent. The lower scale block for s1,s2 is the nonsingular block in Section 2. Therefore the four-equation Jacobian in `(lambda1,lambda2,s1,s2)` is block triangular with invertible diagonal blocks. Keeping s3 fixed and lambda3 as the free parameter, the analytic IFT produces an actual one-parameter family with

    X=Y=T=U=0                                        (2)

for all sufficiently small positive epsilon. The physical first-order variation of the remaining scales is allowed; its effect on V at the base point is zero because every beta is zero there.

## 4. A nonzero chronological derivative, with its exact sign

Reparametrize the free parameter t so that the leading normalized upper-charge tangent is

    d beta_r/dt|_(t=0)=epsilon^4 v_r+O(epsilon^5),
    v=(z-y,-(z-x),y-x).

This is possible since v3 is nonzero and the upper rank-two equations impose exactly `sum v=0`, `sum chi_r v_r=0` at zero epsilon. The leading lower vector satisfies

    c_r=chi_r v_r/(xyz).                             (3)

At the base point beta is EXACTLY zero. Differentiating the exact chronological formula therefore eliminates the variations of chi, tau and zeta and gives

    d(V/b4)/dt|_0=epsilon^8 D+O(epsilon^9),
    D=sum_(r<t)v_r c_t(1-chi_r/(2chi_t))
      =(1/(xyz))sum_(r<t)v_r v_t(chi_t-chi_r/2).      (4)

No averaged transport or independently fitted lower history is used. The coefficient is strictly negative. Indeed, put `S_j=sum_(r<=j)v_r`. Since `sum v=sum chi v=0`, elementary summation by parts gives

    sum_(r<t)v_r v_t(chi_t-chi_r/2)
      =-(3/4)sum_(j<3)(chi_(j+1)-chi_j)S_j^2
                         -(1/4)sum_r chi_r v_r^2 <0. (5)

For verification, the sum with kernel chi_t equals
`[-sum Delta(chi)S_j^2-sum chi_r v_r^2]/2`, and the sum with kernel chi_r equals
`[sum Delta(chi)S_j^2-sum chi_r v_r^2]/2`. Their indicated combination is (5). All chi are positive and strictly increasing, and v is nonzero.

For every sufficiently small fixed positive epsilon the derivative in (4) is thus nonzero. V is zero at t=0. Positive and negative sufficiently small t give opposite signs of V, with all four equations (2) exact and at least one physical f nonzero. Positive right calibration multiplies V by a positive factor, so the fixed-target version in Section 1 has the same conclusion.

This proves that the selected lower equations cannot force the entire actual chronological defect expression to be nonpositive, nor force V to vanish. The negative square alone is not a valid sign guard on this selected fibre. It makes no such assertion about the FULL lower-forest fibre.

## 5. Preserved full-target failure

At t=0 the inherited ordinary-normalized diagonal quantity

    J=(29/45)[b4/b2^6-1]-(20/9)[b3/b2^3-1]

has the strict leading value

    J=-epsilon^4 sum_r (s_r^0)^4 d^4
                    (1-2d/5+d^2/15)+O(epsilon^5)<0.

All ordinary factors cancel from these ratios. At any fixed sufficiently small positive epsilon, continuity preserves J<0 for both signs of t chosen sufficiently close to zero. The target E(q) has J=0. Accordingly these actual sources already fail full ordinary equality through KERNEL cap FOUR (seven total copies in the inherited passive completion translation). They are not full-lower-cap-eight counterexamples or all-copy rivals.

This source family closes only the selected-state proposed sign implication. The exact full cap-eight lower equations, cap-nine diagonals and arbitrary strict private source class remain unresolved. Further selected-only variants are not pursued as a replacement for that obligation.
