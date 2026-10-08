# Actual quartic defect identities and a mandatory grade correction

Contributor: Codex role 5, 8 October 2026. HAND CANDIDATE. This addendum is mandatory when reading [the frozen exact energy note](EXACT-CHRONOLOGICAL-ENERGY-DEFECT.md), SHA256 `c65245dafb6201433a3356149d51b11dcaf73986306cb787bdfd2da7d932a477`. It supersedes only the coincident-placement grade claim in its Section 5. The frozen note is preserved, including the incorrect sentence. Its exact identities (2)--(8), strict rational checks and the separate three-cell source construction are unchanged.

## 1. Correction and scope

The sentence “The square and both defects are all grade seven” is incorrect when all leading placements coincide and the genuine clock gaps are order epsilon. In that case `1-chi_r/chi_t=O(epsilon)`. The beta-kappa term first enters at grade EIGHT; the negative square and beta-zeta term can enter at grade SEVEN. Consequently the following sentence about dropping either defect at the first relevant grade must be read as applying only to zeta in this coincident-placement regime. Both exact defects remain present in the arbitrary-word identity, and with distinct leading placements both can first enter at grade seven.

This correction supplies the actual quartic coefficients of kappa and zeta and checks the reduction to the inherited collapsed-leading G7 formula. It neither proves their sign on the full lower-forest fibre nor constructs a full-lower-cap-eight physical return.

## 2. The actual single-cell source jets

Use the SAME strict rare-route source as the pinned collapsed-leading provider:

    B_r(epsilon)=B(rho_r, exp(-epsilon s_r z_r), epsilon s_r),
    d_r=1-rho_r,
    Gamma_r=s_r^3[3(z_r-d_r)^2-d_r^3]/2,
    b_r=s_r z_r,    k_r=s_r^4 delta_r.

The source-coupled delta, i and Gamma are the pinned polynomials; they are not independently chosen charges. Positive ordinary gaps and bounded analytic parameter corrections retain the same leading coefficients. Write `p2_r=b2(B_r)` and algebraically pair-normalize

    C_r=B_r E(p2_r^(-1)).

This inverse is spectral postprocessing, not a negative physical edge. The accepted full source expansion is

    C_r=1+epsilon^3 Gamma_r R3
      +epsilon^4[alpha_r R3+(i_r/6)(Q^2+Q)
                   +b_r Gamma_r[Q,R3]+k_r Z]+O(epsilon^5).

The inherited top-band coefficients are

    d_n(R3)=-2/(2n-3),    d_n(Z)=18,
    d_n(Q^2+Q)=0,        d_n([Q,R3])=2.

The last equality follows from the spectral eigenvalues: on the n-to-(n-2) band the commutator multiplier is `-lambda_n+lambda_(n-2)=-(2n-3)`. These formulas give the SAME cell's two normalized jets

    f(C_r)=-(2/15)Gamma_r epsilon^3
      +[-(2/15)alpha_r+2b_r Gamma_r+18k_r]epsilon^4+O(epsilon^5),
    h(C_r)=-(2/9)Gamma_r epsilon^3
      +[-(2/9)alpha_r+2b_r Gamma_r+18k_r]epsilon^4+O(epsilon^5).

In particular

    [h(C_r)-(5/3)f(C_r)]_4=-(4/3)b_r Gamma_r-12k_r.       (1)

The accepted full current-root enumeration gives

    e(B_r)=[-(2/3)b_r Gamma_r-3k_r]epsilon^4+O(epsilon^5), (2)

with identically zero cubic e coefficient throughout this family. Thus analytic first-order parameter corrections do not create an omitted cubic e term. They affect alpha in (1), which cancels there.

## 3. Correcting the physical diagonal transports

Let `A_j(r)` be the genuine prefix diagonal BEFORE cell r, exactly as in the frozen note. Let `a_r` denote that prefix's leading ordinary survival. Distinguish this survival from the first-order clock position used below. The exact kappa expression is

    kappa_r=A6(r)/[A4(r)p_(4,r)]
      {h(B_r)-(5/3)Dpre_r[p_(4,r)p_(6,r)/p_(7,r)^2]f(B_r)},
    Dpre_r=A4(r)A9(r)/A7(r)^2.                         (3)

Every ordinary factor cancels from Dpre because `lambda_4+lambda_9-2lambda_7=6+36-42=0`. Each preceding pair-normalized actual cell is `1+O(epsilon^3)`, so `Dpre_r=1+O(epsilon^3)` for a fixed finite architecture. Likewise each own-cell normalized diagonal is `1+O(epsilon^3)`.

The right ordinary calibration gives

    f(B_r)=p2_r^21 f(C_r),    h(B_r)=p2_r^6 h(C_r),
    p2_r=1-b_r epsilon+O(epsilon^2).

In the second term of (3) the pair power is `6+15-2*21+21=0`. Its fourth-order coefficient is therefore that of `(5/3)f(C_r)`. In the first term the pair power six contributes `-6b_r h(C_r)_3=(4/3)b_r Gamma_r`. This cancels the b-Gamma term in (1). The prefactor has leading value `a_r^9`. Hence

    kappa_r=-12 a_r^9 k_r epsilon^4+O(epsilon^5).          (4)

For zeta use its exact defining bracket and the SAME own-cell diagonals:

    zeta_r=A7(r)/[A4(r)p_(4,r)]
                   [2e(B_r)-(1-p_(7,r)/p_(6,r))h(B_r)].

Since `1-p_(7,r)/p_(6,r)=6b_r epsilon+O(epsilon^2)`, (2) and `h_3=-2Gamma_r/9` give

    [2e-(1-p7/p6)h]_4
      =-(4/3)b_r Gamma_r-6k_r+(4/3)b_r Gamma_r=-6k_r.

The prefactor has leading value `a_r^15`, giving

    zeta_r=-6 a_r^15 k_r epsilon^4+O(epsilon^5).           (5)

Equations (4),(5) identify both exact defects with the actual source's quartic Z coefficient at this order. No pointwise vanishing or global sign is asserted. The same k remains coupled to the full i/Gamma/own-clock identities and other forest equations.

## 4. Recovery of the inherited coincident-placement G7

Now suppose every `a_r=a`, all inter-cell survivals are `exp(-epsilon ell_j)` with `ell_j>0`, and put

    t_r=sum_(h<r)(b_h+ell_h)+b_r,
    t_(r+1)-t_r=ell_r+b_(r+1)>0.

The actual prefix transports give

    chi_r=a^(-6)[1+6t_r epsilon]+O(epsilon^2),
    beta_r=-(2/15)a^21 Gamma_r epsilon^3+O(epsilon^4).

Together with (4),(5), these show

    beta_r kappa_t(1-chi_r/chi_t)=O(epsilon^8),
    chi_r beta_r zeta_t=(4/5)a^30 Gamma_r k_t epsilon^7
                                                    +O(epsilon^8).

The first defect cannot contribute to the degree-seven coefficient. If `sum Gamma_r=0`, the boundary terms `chi_L^2 B^2-A^2` of the frozen identity are at least grade eight. With `S_j(Gamma)=sum_(r<=j)Gamma_r`, the square contributes

    -(8/45)a^30 epsilon^7
          sum_(j<L)(ell_j+b_(j+1))S_j(Gamma)^2+O(epsilon^8).

Therefore the exact normalized energy recovers

    V(W)/b4(W)=a^30 epsilon^7
      {-(8/45)sum_(j<L)(ell_j+b_(j+1))S_j(Gamma)^2
                    +(4/5)sum_(r<t)Gamma_r k_t}+O(epsilon^8).

Finally `ell=(15/2)V` and the whole word's leading `b4` is `a^6 c(0)^6`. Thus

    ell(W)=a^36 c(0)^6 epsilon^7 G7+O(epsilon^8),
    G7=-(4/3)sum_(j<L)(ell_j+b_(j+1))S_j(Gamma)^2
                            +6sum_t S_(t-1)(Gamma)k_t.

This is exactly the already accepted collapsed-leading provider, with its attribution and hypotheses preserved. It checks the corrected grade assignment and does not establish a new constrained sign theorem. With distinct leading prefix survivals the chi difference instead has order one, so the beta-kappa term can enter at grade seven, as stated in the unaffected first paragraph of the frozen Section 5.

## 5. Evidence boundary and next obligation

The displayed identities are hand coefficient algebra from the pinned full-source providers. The existing rational fixture script checks the exact arbitrary-word energy decomposition, not these formal jets or an actual epsilon value of the analytic IFT family. Independent coefficient review is requested. No Lean, CI, QE or full capped-forest solver was run.

The remaining direct implication is still whether every lower forest equation can constrain the exact source defects sufficiently to yield a cap-nine sign or equality classification. Selected off-diagonal cancellation alone does not do so, while the new three-cell selected cancellation family is excluded by its independently retained cap-four diagonal defect. Original G4 remains OPEN.
