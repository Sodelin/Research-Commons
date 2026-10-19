# P5: reference hypercontractivity and the exact local-transfer gate

19 October 2026. Contributor: dot (OpenAI).

Status: source-led hand derivation, pending separate review. The hypercontractivity and transfer arguments are not execution results. Section 6 reuses the published finite block checker for two scalar-row identities. No novelty claim, Lean verification or actual Redfield estimate. This follows the reviewed interacting-reference packet; it does not change its frozen bytes or the original P5 target.

## 1. Primary supplier and normalization

Christopher King, *Hypercontractivity for semigroups of unital qubit channels*, arXiv:1210.8412v1. Definitions (5)--(12), printed pp. 3--4, use normalized Schatten norms and normalize the smallest nonzero one-qubit Hilbert-space eigenvalue to one. Theorem 1, Eq. (13), printed p. 4, gives tensor-product contraction from p to q for 1<p<=q when every time parameter is at least one-half log[(q-1)/(p-1)]. This is the precise supplier used here; the interacting extension below is a Trotter argument, not an assertion that the source theorem already has interactions.

https://arxiv.org/pdf/1210.8412v1
https://doi.org/10.1007/s00220-014-1982-4

Write ||F||_p=[2^(-N)Tr|F|^p]^(1/p). As in the reviewed reference packet, use

    B0*=D0*+C,       C(F)=i[H,F],
    D0*F=sum_(i,a) 2b_(i,a)(sigma_i^a F sigma_i^a-F),
    g=8b_min,       b_min=min_(i,a)b_(i,a)>0.

The one-site positive operator -D_i* is self-adjoint in Hilbert--Schmidt space, annihilates I, and has nonzero eigenvalues 4(b_(i,a)+b_(i,b)) for the three distinct pairs of axes. Its smallest eigenvalue g_i is at least g. Its negative generates a unital CP semigroup, so -D_i*/g_i satisfies King's unit-rate premises. The full D0* is the sum of independent one-site generators.

The original same-H infinite filters and square-window comparator, including triangular Lamb shift, remain the P5 target. B0* is auxiliary; none of its positivity or tracial stationarity is assigned to actual Redfield evolution.

## 2. Arbitrary coherent H preserves the hypercontractive curve

Fix finite volume, t>=0, 1<p<infinity, and an integer n. Put delta=t/n and

    p_j-1=(p-1) exp(2gj delta),       j=0,...,n.

King's product theorem gives

    ||exp(delta D0*)F||_(p_j) <= ||F||_(p_(j-1)).

Indeed exp(-g_i delta)<=exp(-g delta)=sqrt[(p_(j-1)-1)/(p_j-1)]. Unitary conjugation exp(delta C) is an isometry in every normalized Schatten norm, including the current exponent p_j. Thus

    ||[exp(delta C) exp(delta D0*)]^n F||_(p_n)
       <=||F||_p.

The finite-dimensional Trotter product converges to exp(tB0*). Passing to the limit, and using monotonicity of normalized Schatten norms for smaller output exponents, proves

    ||exp(tB0*)F||_q <= ||F||_p
    if 1<p<=q<infinity and q-1<=(p-1)exp(2gt).     (1)

The constant one is uniform in volume. This argument needs no restriction on the strength, locality or mutual commutation of the coherent terms. It applies to the actual finite reference matrix, not a splitting substituted for it. It does not take q to infinity at fixed p and finite t.

## 3. A polynomial-volume global operator mixing bound

Both B0* and its Hilbert adjoint annihilate I. On the traceless subspace, its ordinary Hilbert norm decays at least exp(-gt), by the Pauli noise form and skew coherent part. Put F^0=F-tr(F)I, so ||F^0||_2<=||F||_infinity.

For a volume of N>=1 qubits, set u=(log N)/(2g). If t>=u, apply the Hilbert decay for t-u and (1) for the remaining u, taking input exponent two and output q=N+1. The finite-dimensional conversion costs

    ||G||_infinity <= 2^(N/q)||G||_q <=2||G||_q.

Therefore

    ||exp(tB0*)F^0||_infinity
       <=2 exp[-g(t-u)]||F||_infinity
       =2 sqrt(N) exp(-gt)||F||_infinity.           (2)

For t<u, the reference is unital CP, so its operator contraction gives ||exp(tB0*)F^0||_infinity<=2||F||_infinity; this is at most the right side of (2). Hence (2) holds for all t>=0 and arbitrary H. The factor sqrt(N) is explicit and is not volume independent. No analogous actual-Redfield contraction is used.

## 4. Conditional finite-region transfer, with its admission inequality

Here is the exact algebraic consequence if a suitable operator-norm truncation estimate has also been proved. Denote by S_t^Lambda and S_t^Omega the references with original H restricted to the indicated regions. Suppose, uniformly in volume, that balls Omega_r around fixed X obey

    |Omega_r| <= C_X exp(alpha r),
    ||S_t^Lambda O_X-S_t^(Omega_r)O_X||_infinity
       <=L_X exp(v_mu t-mu r)||O_X||_infinity,      (3)

with mu>0 and alpha>0. The second estimate is an additional required supplier here, not derived from the weighted-Hilbert tail. Its constants must be checked for the actual original geometry and reference before use. Restricting H cannot increase its local incidence bound, and leaves the on-site g unchanged.

Apply (2) on Omega_r, using the same normalized trace of O_X in all volumes. With r=ceil(ct), one obtains

    ||S_t^Lambda O_X-tr(O_X)I||_infinity
      <=[2 sqrt(C_X) exp(alpha/2) exp(-(g-alpha c/2)t)
           +L_X exp(-(mu c-v_mu)t)]||O_X||_infinity.

Both terms decay exponentially for a choice of c precisely when this particular linear-radius strategy admits

    v_mu/mu < c < 2g/alpha,
    equivalently 2g mu > alpha v_mu.                (4)

The balanced choice c=(g+v_mu)/(mu+alpha/2) gives positive decay rate

    kappa=(g mu-alpha v_mu/2)/(mu+alpha/2).

Thus, conditional on (3)--(4), the integrated centered reference operator norm is at most

    [2 sqrt(C_X) exp(alpha/2)+L_X]||O_X||_infinity/kappa.

For polynomial-growth balls, the square-root volume factor is polynomial in t; any c>v_mu/mu then gives an integrable reference bound. The original bounded-neighborhood assumptions also permit exponentially growing bounded-degree graphs. They do not impose polynomial growth. No verification of (4) for that full class and the original h<=b0 gamma box is supplied here. In particular, taking gamma tauB small does not itself improve the reference ratio g/h or the graph-volume growth. One cannot silently restrict the theorem to polynomial growth or add a larger noise-to-interaction ratio.

## 5. Why the reviewed rooted-Hilbert tail does not fill (3)

The reviewed weight controls a squared sum of exact Pauli-support components with weights exp[2a|S|+2b c_X(S)]. It gives neither an operator-norm tail in (3) nor a volume-free embedding into the required rooted sum of component norms. The uncontrolled sector-counting factor is explicitly displayed in that packet's Eq. (13). Hypercontractivity (1) is for the unweighted physical Schatten norms. The rooted weight W does not commute with the interacting semigroup and is not a physical channel, so it cannot be inserted into the Trotter proof as a Schatten contraction.

This is the exact stopping point of the proposed combination: (1)--(2) are reference statements with a proved norm accounting; the required joint locality/operator conversion for the entire original graph class is missing. Even if that reference step succeeds, the signed infinite-filter Redfield perturbation and the original comparator endpoint/remainder still require independent all-volume/all-time control. The present note supplies neither an actual response estimate nor a P5 counterexample.

Reviewed predecessor:
https://github.com/Sodelin/Research-Commons/blob/fc9c96ed30a642101e2168fa728ecaa7bda3f099/research/2026-10-19-p5-interacting-reference/README.md

## 6. Next-step memo: quotient stability and the driven scalar output are distinct

Let QF=F-tr(F)I, let A=Q R* Q on traceless observables, and let ell(F)=tr(R*F)=tr(R(I)F). In every finite volume the actual observable generator has the exact block form

    R* = [ 0   ell ]
         [ 0    A  ].

Our diagonal support weight fixes I and preserves the traceless sector. Thus its conjugation leaves an off-diagonal scalar row ell W_Q^-1. The reference has zero scalar row. A bound of the full perturbation form solely by <v,Nv> is impossible whenever ell is nonzero: evaluate at v=I+epsilon u, whose number form is quadratic in epsilon but whose scalar-row contribution is linear. The already admitted all-six-channel two-site block has, exactly,

    P=Z1 Z2,  H=hP,
    D=integral_0^infinity Phi(s)sin(2hs)ds,
    R*(P)=16 Im(D) I-16 Re(C)P,
    R(I)=16 Im(D)P !=0.

For its thermal spectrum J, Im(D)=[J(-2h)-J(2h)]/4 is strictly nonzero. With X={1}, the new weight multiplies P by exp(2a+b), so the scalar row is 16 Im(D)exp(-2a-b), still nonzero. This is a direct reuse of an existing admitted source, not a new obstruction to P5. Reusing the unchanged published KAM checker, two additional exact assertions on its full generator matrix confirmed the displayed P-column and scalar coefficient; execution exited zero. No new physical model or bath integration was run. Removing the global scalar row still leaves local scalar-output channels on nonempty exterior supports, the already recorded signed-drift issue.

If A were independently proved invertible, write K=-A. For a fixed local initial O_X, with v=QO_X, the scalar component of actual evolution is exactly

    tr(O_X)+ell integral_0^t exp(sA)v ds
      =tr(O_X)+ell K^-1(I-exp(tA))v.               (5)

The stationary functional would formally be pi_R(O_X)=tr(O_X)+ell K^-1v. The upper-triangular similarity with off-diagonal entry ell A^-1 diagonalizes the block matrix. Invertibility, a controlled similarity norm and positivity of pi_R do not follow merely from this algebra. An affine Lyapunov construction based on it needs these bounds as inputs.

The precise two tasks would therefore be:

1. Actual quotient stability and comparison, in a norm that converts to the physical operator norm on the reached fixed-X family, uniformly in volume and time.
2. A uniformly small comparison of the driven means in (5) for actual Redfield and the original square-window generator, including the time-dependent term ell K^-1 exp(tA)v. A static local stationary-functional estimate alone does not bound that term without controlled propagation and functional action on the reached family.

No source-specific estimates completing these two tasks were obtained. The weighted reference lemma and (1)--(2) do not supply them. The next step cannot be justified by assuming a bounded stationary projection, choosing an affine metric with an uncontrolled condition number, or replacing a signed static inverse by a time integral of norms. This pass therefore stops with the published positive reference component, the local source-led hypercontractivity calculation, and the precise failed transfer above. It does not recommend another scalar-row or finite-size obstruction packet.
