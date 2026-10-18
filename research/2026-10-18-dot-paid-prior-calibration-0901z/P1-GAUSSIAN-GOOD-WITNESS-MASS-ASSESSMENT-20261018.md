# Adequate-witness mass on an admitted dense Gaussian Gibbs ensemble

18 October 2026 UTC. Author: dot (OpenAI), working with Nolan.

**Local hand-proof candidate for review.** This is a quantitative assessment of the sufficient prior-mass certificate in the reviewed nonlinear-mixture test. It is not a lower bound on the actual test's error, a new P1 testing lower bound, a proof that the requested o(M) mass cost is impossible, or a historical-novelty claim. No numerical execution or Lean verification is claimed.

## 1. Outcome and its limits

Fix beta>0 and locality k>=1. Write D=binom(N,k) and M=sum_{j=1}^k 3^j binom(N,j). For every fixed

    0<epsilon<=1/(1024*9^k),                         (1)

and every sufficiently large N, we construct a distribution over pairs of legal diagonal k-local Gibbs states with full trace distance at least epsilon. The construction uses exactly the N declared spins and all coefficients have magnitude at most one.

For an arbitrary fixed operator V with ||V||<=1, define the midpoint loss

    ell_(rho,sigma)(V)=Re Tr[(rho-sigma)V]
        +[Tr(rho V^*V)+Tr(sigma VV^*)]/2.             (2)

Set b=3^k epsilon and C=1+64b^2. For every g>0 the source ensemble satisfies

    Pr_source{ell(V)<=-g}
       <=(4/3) exp[-D g^2/(32b^2 C)].                (3)

Consequently, for EVERY source-independent probability distribution pi on contraction witnesses, there is a legal far pair with

    p_(rho,sigma)(g):=pi{V:ell_(rho,sigma)(V)<=-g}
       <=(4/3) exp[-D g^2/(32b^2 C)].                (4)

This controls the entire set of adequate witnesses, not only a parameter ball around a selected witness. It includes fixed mixtures of symmetry orbits, random orientations and predetermined scales, provided all their witnesses are contractions and the same threshold g is used.

At the current Fourier threshold g=epsilon^2/(8w), with w=B+2=Theta(log M), (4) gives only

    log(1/p)>=Omega_(k,epsilon)(M/log^2 M)-log(4/3).

This IS COMPATIBLE with log(1/p)=o(M). Thus it does not rule out the mass estimate requested for a logarithmic improvement. However, substituting any valid uniform mass lower bound into the present sufficient sample formula still requires assigning Omega_k(M/log M) copies. Changing only the fixed prior at this threshold cannot use that formula to certify an improved power of M. This is a limitation of the sufficient certificate, not a necessary budget for the actual POVM or every P1 method.

## 2. Original physical class and the good Gaussian set

Let z=(z_S)_{|S|=k} be a standard real D-dimensional Gaussian vector, drawn once. On the N-spin cube let U be uniform, chi_S(x)=product_{i in S}x_i, and

    a=b/sqrt(D),
    F_z(x)=a sum_(|S|=k) z_S chi_S(x),
    Z_c(z)=E_U exp(c F_z).

Use the source Hamiltonians

    H_z=-F_z/beta,       K_z=+F_z/beta,              (5)

and the associated diagonal Gibbs states rho_z and sigma_z, with relative densities

    f_z=exp(F_z)/Z_1(z),
    f_-z=exp(-F_z)/Z_-1(z).                          (6)

The original coefficientwise bound holds whenever ||z||_infinity<=beta sqrt(D)/b. There is no reservoir, auxiliary label, variable temperature or omitted physical spin. The same z is shared by every copy of its two fixed source states.

Define the closed, bounded, convex, symmetric set

    Cset={z: Z_2(z)<=C, Z_-2(z)<=C,
                 ||z||_infinity<=beta sqrt(D)/b},
    C=1+64b^2,                                      (7)

and the additional norm event

    Bset={z: D/2<=||z||_2^2<=2D},
    Aset=Cset intersect Bset.                        (8)

Convexity follows because each Z_c is an average of exponentials of linear functions; swapping z and -z exchanges the two constraints. The box is convex and symmetric. Zero belongs to Cset. The norm event Bset is used only for admission of the far alternative; it is not used as a convex domain in the Lipschitz argument.

For each fixed x, F_z(x) is a Gaussian of variance b^2. Thus E_z Z_2(z)=E_z Z_-2(z)=exp(2b^2). Also Z_c(z)>=1 for every z, by Jensen and E_U F_z=0. Since b<=1/2,

    exp(2b^2)-1<=4b^2.

Markov applied to the nonnegative variables Z_2-1 and Z_-2-1 gives a combined probability at most 1/8 of violating their bounds in (7). A Gaussian coordinate tail and the union bound give

    Pr{||z||_infinity>beta sqrt(D)/b}
       <=2D exp[-beta^2 D/(2b^2)].                   (9)

Finally E||z||_2^2=D and Var(||z||_2^2)=2D. Chebyshev on the two sides of (8) gives Pr(Bset^c)<=10/D. Choose N large enough that

    D>=160,
    2D exp[-beta^2 D/(2b^2)]<=1/16.                  (10)

Then Pr(Aset)>=1-1/8-1/16-1/16=3/4. These requirements hold eventually for every fixed beta,k,epsilon in (1). The source ensemble used below is the Gaussian law conditioned on Aset.

## 3. Full trace separation after conditioning

For z in Cset, Cauchy--Schwarz gives

    1<=Z_1(z),Z_-1(z)<=sqrt(C),
    Z_1(z)-1,Z_-1(z)-1<=32b^2.                       (11)

For z also in Bset, orthogonality of Walsh words gives

    b/sqrt(2)<=||F_z||_(L2(U))<=sqrt(2)b.

Put R=exp(F_z)-1-F_z>=0 and r=Z_1(z)-1. Then

    f_z-1-F_z=[R-r(1+F_z)]/Z_1(z),
    E_U|f_z-1-F_z|
       <=r(2+E_U|F_z|)/Z_1(z)<=96b^2.               (12)

The last inequality uses E_U|F_z|<=sqrt(2)b<=1. The same argument for -F_z gives the same bound. Therefore

    ||rho_z-sigma_z||_1
       >=2 E_U|F_z|-192b^2.                         (13)

The standard Boolean degree-k hypercontractive estimate gives ||F||_4<=3^(k/2)||F||_2. Interpolation ||F||_2<=||F||_1^(1/3)||F||_4^(2/3) consequently gives E|F|>=||F||_2/3^k. This is the same all-polynomial inequality already used in the reviewed dense localization calculation, not a statement about independent coordinate observations.

Using b<=1/(1024*3^k), (13) gives

    ||rho_z-sigma_z||_1
       >=sqrt(2)b/3^k-192b^2
       >=[sqrt(2)-3/16]b/3^k
       >=b/3^k=epsilon.                             (14)

Thus every retained source pair, not merely a high prior fraction of the conditional ensemble, lies in the original alternative. The trace convention is the full L1 norm, without the factor 1/2.

## 4. Concentration of the linear loss for every fixed witness

Fix any complex V with ||V||<=1, and put h(x)=<x|(V+V^*)/2|x>. Then h is real and |h(x)|<=1, even when V has off-diagonal entries. Define

    T_V(z)=Re Tr[(rho_z-sigma_z)V]
          =E_(f_z U) h-E_(f_-z U) h.                (15)

It is odd under z -> -z. For one term m(z)=E_(f_z U)h, differentiation gives

    partial_(z_S) m
      =a E_U[f_z(h-m(z))chi_S].                     (16)

The complete Walsh system is orthonormal under U. Bessel's inequality applied to the subset of degree-k words therefore yields

    ||gradient m||_2^2
      <=a^2 E_U[f_z^2(h-m(z))^2]
      <=4a^2 E_U f_z^2
      <=4a^2 C.                                    (17)

The last inequality uses E_U f_z^2=Z_2(z)/Z_1(z)^2<=C on Cset. The same estimate holds for the other term in (15). Hence

    ||gradient T_V(z)||_2<=4a sqrt(C)=:L
        on Cset,          L^2=16b^2 C/D.             (18)

Since Cset is convex, integrate the gradient along each contained line segment to conclude that T_V is L-Lipschitz on all of Cset. This argument keeps the density normalizers and the aggregate Fourier gradient; it does not sum separate coordinate bounds with an extra factor of D.

To apply ordinary Gaussian concentration before conditioning, take the scalar McShane extension

    h_ext(z)=inf_(y in Cset)[T_V(y)+L||z-y||_2],
    T_ext(z)=[h_ext(z)-h_ext(-z)]/2.                 (19)

The first extension is finite and L-Lipschitz and equals T_V on Cset. Symmetry of Cset and oddness of T_V imply that T_ext also equals T_V there, is L-Lipschitz on R^D, and is odd. In particular zero is a median for its standard Gaussian law. No convexity of T_ext is asserted or needed.

The classical Gaussian Lipschitz concentration inequality now gives the convenient (slightly weakened) bound

    Pr{T_ext(z)<=-g}<=exp[-g^2/(2L^2)]
                      =exp[-Dg^2/(32b^2 C)].         (20)

For the closed event the bound follows by taking thresholds tending to g from below. Since T_ext=T_V on Cset, and the quadratic part of (2) is nonnegative, the event ell(V)<=-g within Aset implies T_ext<=-g. Conditioning on Aset costs at most 4/3, proving (3).

This bound applies to every fixed contraction V, not only diagonal operators or witnesses individually derived from a Gibbs parameter triple. Off-diagonal entries can affect the nonnegative quadratic term but cannot invalidate the necessary linear condition used in (20).

## 5. All fixed priors and the exact certificate consequence

Let pi be any source-independent probability measure on contraction witnesses, with measurable good-loss sets. Fubini and (3) imply

    E_(z|Aset) pi{V:ell_(rho_z,sigma_z)(V)<=-g}
      <=(4/3)exp[-Dg^2/(32b^2 C)].                  (21)

At least one retained z has mass no larger than the right side. This proves (4). Finite mixtures, continuous random orientations, group averaging and predetermined multiscale mixtures are all included at this fixed threshold. No claim is made about a prior learned from the source copies.

The reviewed normalized-loss mixture formula has lambda=1/12 and requires

    n >= (24/g) log[2/(p_0 delta^2)],                (22)

where p_0 is a uniform LOWER bound on the good mass over every admitted far source pair. Equation (4) bounds how large such p_0 can be. If p_0=0 this certificate supplies no finite guarantee. Otherwise (4) and (22) entail

    n >= (24/g){Dg^2/(32b^2 C)+log[3/(2delta^2)]}
      >=3Dg/(4b^2 C),                              (23)

with delta<1/2. This is a lower bound on the sample count assigned BY THAT SUFFICIENT FORMULA, not a lower bound derived from distinguishability of source experiments.

For its current Fourier normalization g=epsilon^2/(8w), b=3^k epsilon, (23) becomes

    n>=3D/(32*9^k*C*w),
    TOTAL assigned copies 2n>=3D/(16*9^k*C*w).       (24)

For fixed k,beta,epsilon, D=Theta_k(M) and w=Theta(log M). Thus the generic certificate cannot certify a better power of M merely by replacing the fixed prior, at this same threshold. This does not exclude logarithmic improvements over O(M log M), a sharper analysis of the actual mixture measurement, a different threshold/margin tradeoff, or a paid adaptive procedure.

In particular, (4) gives only an Omega(M/log^2 M) lower bound on log(1/p_0) at the current threshold. It does not contradict an o(M) upper bound. The original requested positive mass guarantee is still unproved. It would be incorrect to call the route impossible or to convert (23) into a P1 testing lower bound.

## 6. Sources, prior attempts and stopping gate

The consuming nonlinear-mixture theorem is preserved with its separate assistant-context hand review at:
https://github.com/Sodelin/Research-Commons/blob/7ba73e425f8e26fdea8a03dea6bd536117c3e413/research/2026-10-18-dot-nonlinear-mixture-0654z/README.md

The earlier packing/Fano calculation supplied an admitted dense sign family and the hypercontractive L1 estimate. Its packing statement alone says nothing about the full good-witness sets; the Gaussian ensemble, convex normalization domain and fixed-witness concentration above supply the additional argument:
https://github.com/Sodelin/Research-Commons/blob/635139c505ac8ba72261e2f468bbd51fac3fce82/research/2026-10-16-g6-gibbs-certification/trace-localization-pilot-boundary-33/README.md

For the exact classical concentration input, I opened Petros Valettas, *On the tightness of Gaussian concentration for convex functions*, arXiv:1706.09446v1, Introduction Eq.(1.1), PDF page1:
https://arxiv.org/pdf/1706.09446 . That displayed upper bound is for every Euclidean Lipschitz function; convexity is an additional premise of the paper's separate reverse-concentration results, which are not imported here. Equation(1.1) attributes the underlying Gaussian isoperimetry to Borell and Sudakov--Tsirel'son. The stronger factor 1/2 in the source is not needed in (20). The primary passage was checked on18 October2026 UTC. The original Borell DOI resolver did not return the article during this pass; no fresh full-original-paper audit is claimed.

The proof uses established Gaussian concentration, Walsh orthogonality, hypercontractivity and a Lipschitz extension. Historical novelty is unestablished. There is no new measurement lower bound, hardware restriction or physical-model substitution. The current construction is a subset of the original noncommuting-allowed class.

**Next obligation:** a positive source-uniform mass theorem for the entire nonlinear adequate set, or a fully charged adaptive/alternative analysis that improves the accepted tester, is still required. The present calculation places a quantitative scale constraint on the fixed-threshold sufficient formula. It gives no justification for assuming a large mass, and it gives no reason to start another constant or logarithmic refinement ladder. The full optimal-copy P1 target remains open.
