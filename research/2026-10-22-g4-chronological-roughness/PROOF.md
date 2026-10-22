# A necessary microscopic scale-oscillation gate for bounded-budget fair-parabolic returns

22 October 2026. Contributor: dot (OpenAI-assisted research), prepared for Nolan.
Status: hand derivation for independent review. No new runtime execution, exact-return construction, historical novelty certification, or master G4 closure is claimed.

## 1. Source, quantifiers, and claimed consequence

Retain the actual complete labelled forest source, indivisible current roots, one shared physical tuple across all rows, and the source normalization of the accepted Oct8 fair-parabolic energy packet. Fix a compact shape set K with 0<h_min<=h<=h_max<4 and bounded ordinary target time H>0. Each cell has, for one common epsilon>0,

    x_i=2 h_i epsilon^2-4 u_i epsilon^3+8 v_i epsilon^4,
    y_i=2 h_i epsilon^2+4 u_i epsilon^3+8 v_i epsilon^4,
    g_i=1/2+epsilon w_i,
    (h_i,u_i,v_i,w_i) in K.

The coins need not be exactly fair; they have fair base. Exact fair routing is the subcase w_i=0. Strict physical arms and interior coins hold for small epsilon uniformly on K. All ordinary connectors are strictly positive. No physical inverse or external selector is admitted.

Claim. There are epsilon_0,c>0, depending only on K,H and the inherited finite representation, such that EVERY nonempty finite word of these cells whose COMPLETE forest kernel through cap nine equals E_T with 0<T<=H must satisfy, for epsilon<epsilon_0,

    sum_(i=1)^(N-1) (h_i-h_(i+1))^2 >= c epsilon^(-2).       (A)

The index order is physical chronological order (or its reversal, which leaves this sum unchanged). There is NO assumed bound on N, no separated limiting placements, and no small-total-bigon-budget hypothesis. Consequences include:

- constant leading arm scale h_i is impossible for all sufficiently small epsilon, at any bounded positive target hazard;
- more generally, mean adjacent squared scale variation tending to zero is impossible;
- any possible bounded-budget dust sequence in this compact source class must retain order-one adjacent scale variation on a positive fraction of cells, with N of order epsilon^(-2).

These are necessary conditions, not an existence claim for the remaining oscillatory branch. The constants are existential and not numerically evaluated. Arbitrary multiscale, noncompact, non-fair-base, non-weak, and nonserial rivals remain outside this result.

## 2. Inherited inputs and exact chronology

All coefficient identities below are reused, not newly computed. The accepted source representation has spectral vertices 9/7/6/4 and bare entries X=Y=f, T=H_source, U=-H_source+2e, V=0. Set

    alpha_i=h_i^3-12(w_i h_i-u_i)^2,
    c_i=-log b2(B_i), C_i=E_(-c_i) B_i, kappa=5/3.

The inverse is only an algebraic normalization. The Oct8 accepted uniform estimates are

    (h_min/2)epsilon^2 <= c_i <= 2 h_max epsilon^2,
    X_i=Y_i=xbar_i,
    xbar_i=(alpha_i/15)epsilon^6+O_K(epsilon^8),
    |T_i-kappa xbar_i|+|U_i+kappa xbar_i|=O_K(epsilon^10),
    V_i=0, diagonal(C_i)=I+O_K(epsilon^6),
    D4(B_i)=epsilon^8[-h_i^4+4 h_i alpha_i]+O_K(epsilon^10).

Use the inherited decreasing suffix positions s_1>...>s_N in [0,H]. Pair matching implies

    T=sum ordinary connector hazards + sum c_i,
    s_i-s_(i+1)>=c_(i+1)>=(h_min/2)epsilon^2.

Therefore

    S=N epsilon^2 <= 2H/h_min=:S_max.                       (1)

This bound is available at any bounded target hazard; S_max need not be small.

## 3. The earlier energy estimate extends to bounded S, not just small S

Put a_i=exp(15s_i)xbar_i and

    M0=sum a_i, Mplus=sum a_i exp(6s_i),
    Mminus=sum a_i exp(-6s_i).

The proof of the Oct8 count-uniform packet used S<=1 to simplify constants. Its displayed exact product estimates extend to S<=S_max as follows. Products of normalized diagonal entries are bounded by exp(C N epsilon^6)=exp(C S epsilon^4), uniformly. The horizontal error is

    O(N epsilon^10 + N^2 epsilon^12)
      =O((1+S) N epsilon^10),

and the central error is

    O(N^2 epsilon^16 + N^3 epsilon^18)
      =O((1+S) N^2 epsilon^16).

There are only the two inherited central off-diagonal paths XU and YT. Thus complete ordinary equality yields, with constants depending on K,H but not N,

    |M0|+|Mplus|+|Mminus| <= C N epsilon^10,
    |kappa sum_(i<j) a_i a_j[exp(6(s_i-s_j))-1]|
       <= C N^2 epsilon^16.                                (2)

No assertion that S is small is used here or subsequently.

Define on I=[-1,H+1]

    F(x)=sum_i a_i sinh(6|x-s_i|).

The inherited exact atomic identity, the boundary control from Mplus,Mminus, and (2) give

    F''-36F=12 sum_i a_i delta_(s_i),
    integral_I (F'^2+36F^2) <= C N^2 epsilon^16.             (3)

For completeness, the central ordered sum equals Q+(Mplus Mminus-M0^2)/2, where Q=sum_(i<j)a_i a_j sinh(6(s_i-s_j)); hence |Q|<=C N^2 epsilon^16. Integration by parts gives (3), with boundary terms O(N^2 epsilon^20). This retains chronology and does not replace ordered products with additive cell defects.

## 4. Pair energy with the actual scale profile, not pointwise traces

Let f be the continuous piecewise-linear interpolant with f(s_i)=h_i, extended constantly on either side of the outer nodes in I. For N=1 take f constant. Then |f|<=h_max and

    integral_I |f'|^2 = R_h,
    R_h=sum_(i=1)^(N-1) (h_i-h_(i+1))^2/(s_i-s_(i+1)).      (4)

Choose a fixed smooth cutoff chi compactly supported in the interior of I and equal to one on [0,H], and put psi(x)=chi(x) exp(-15x) f(x). This is an H_0^1(I) test function with

    ||psi||_(H^1) <= C_H(h_max+sqrt(R_h)).                  (5)

The distributional identity in (3), tested against psi, gives EXACTLY

    12 sum_i h_i exp(-15s_i)a_i
      = -integral_I F' psi' -36 integral_I F psi.

Testing with this piecewise-linear H^1 function is legitimate: F belongs to H^1(I), point evaluation is continuous on H^1 in one dimension, and smooth approximation preserves the weak identity. There is no differentiation of the unknown source parameters or assumption that they vary smoothly.

By (3),(5),

    |sum_i h_i xbar_i|
       <= C N epsilon^8 (1+sqrt(R_h)).                     (6)

Using the inherited uniform xbar expansion and bounded h_i,

    |sum_i h_i alpha_i|
       <= C N epsilon^2 (1+sqrt(R_h)).                     (7)

This is the change relative to the Oct8 proof: the Green energy is paired directly with the scale profile. No disjoint-cell trace lower bound is used.

## 5. Fourth diagonal matching forces maximal-order roughness

The exact additive D4 equation and its inherited expansion give

    sum_i h_i^4 = 4 sum_i h_i alpha_i + O(N epsilon^2).

Since h_i>=h_min, (7) implies

    h_min^4 <= C epsilon^2 (1+sqrt(R_h)).                   (8)

For sufficiently small epsilon, (8) forces

    R_h >= c_1 epsilon^(-4).                               (9)

On the other hand the physical intrinsic separation gives from (4)

    R_h <= (2/h_min) epsilon^(-2)
                 sum_(i=1)^(N-1) (h_i-h_(i+1))^2.          (10)

Combining (9),(10) proves (A).

Because h_i lie in a fixed compact interval, (A) also forces N>=c_2 epsilon^(-2). Together with (1), N is of this order. Dividing (A) by N and using (1) gives a strictly positive lower bound on mean adjacent squared variation. Since each squared variation is bounded above, a positive fraction of neighboring pairs must have variation bounded below by a positive constant. All such constants may depend on K,H.

An alternative immediate consequence of (8) is that any uniformly H^1-bounded interpolating profile is impossible. Uniformly Lipschitz or constant profiles are special cases. This conclusion concerns the leading arm scale h_i, not the total pair hazard or the target T.

## 6. Why this does not settle compactness or G4

The proof rejects smooth dust profiles at bounded positive expenditure, including arbitrarily long words. It does not reject microscopic alternation with correlated scale h_i and defect alpha_i. In a possible weak limit, cancellation of the signed alpha measure does not force cancellation of its product with the oscillating h_i. Such correlations are the exact surviving step; one may not replace the limit of h_i alpha_i with the product of two weak limits.

The all-copy finite-word asymptotic, the accepted all-cap diagonal theorem, and nonordinary interiority do not rule out these source-coupled oscillatory finite-cap returns. A continuum or Young-measure zero would itself remain only a necessary limit, not an actual strict finite word or exact full forest match. Nor does cap-nine rejection of this source subclass supply a finite legal panel against every unknown-size strict rival.

The master remains: one finite legal natural-INDEPENDENT panel for each fixed strict target forcing the required COMMON certificate against every admitted unknown-size finite strict rival, OR one fixed target with exact inequivalent admitted rivals after every finite legal panel. The present claim supplies neither alternative. The accepted cap4/cap5 returns, all-cap diagonal suppliers, and positive-budget/nonfair/nonserial gaps remain intact.

## 7. Attribution, source pins, and review limits

Inherited exact source and energy proof, with accepted review status in README:
https://github.com/Sodelin/Research-Commons/tree/efd8ed7a9d23be13eede73019618c4cd4b62c23e/research/2026-10-08-dot-g4-fair-energy-hazard-1220z

In particular WORD-COUNT-UNIFORM-FAIR-BIGON-HAZARD-BOUND-CANDIDATE.md supplies the source estimates, product accounting, and energy identity. ORDERED-GREEN-ENERGY-SEPARATED-FAIR-SOURCE-R1.md supplies the exact atomic identity and its original attribution. Their preparation-time candidate labels are superseded by that packet's acceptance README.

The stronger arbitrary-shape fair small-budget cap-six theorem is retained, not replaced:
https://github.com/Sodelin/Research-Commons/blob/941cb171242115236368c84774de1705c6fb3a44/research/2026-10-21-g4-count-uniform-hazard/PROOF.md

All-copy log-factor separation already belongs to the Oct1 source and is not new here:
https://github.com/Sodelin/Research-Commons/tree/64e1fa9f532439e5f63b660d295dc6b33dfe7ec0/research/2026-10-01-sol61-g4-allcopy-2237z

This proof has not yet received independent review. No mathematical program, compiler, QE engine, numerical search, or runtime test was executed for it. The bounded-S extension and weak-test argument require mathematical review; finite source coefficient checks alone would not establish their quantifiers. Prior-work comparison has recovered the specified Oct8 and Oct21 proofs and local stopped attempts, not certified exhaustive novelty.
