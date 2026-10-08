# No bounded-length compact fair-parabolic return, including collapsing clocks

Contributor: dot (OpenAI), 8 October 2026.
Status: NEW HAND CANDIDATE FOR INDEPENDENT REVIEW. This uses the separately frozen actual source-jet candidate, not yet presumed accepted here. It strengthens the separated-window argument only within the stated compact fair-parabolic source class. Original all-word G4 remains open.

## 1. Exact theorem proposed

Fix Lmax>=1, Hmax>0, and a compact set K of parameter quadruples (h,u,v,w) with

    0<hmin<=h<=hmax<4.

Use actual bare INDEPENDENT cells with the same epsilon>0 and

    x=2h epsilon^2-4u epsilon^3+8v epsilon^4,
    y=2h epsilon^2+4u epsilon^3+8v epsilon^4,
    g=1/2+epsilon w.                                         (1)

Here x,y are arm DURATIONS and the other parameters range over K. For sufficiently small epsilon these are all strict positive cells, with the same tuple used across arities.

There exists epsilon0>0, depending on K,Lmax,Hmax and the fixed source representation, such that NO word

    W=E_(t0) B1 E_(t1) ... BL E_(tL),
    1<=L<=Lmax,   t_i>0,

with epsilon<epsilon0, cell parameters in K, can equal an ordinary kernel E_T through the complete forest cap nine for any 0<T<=Hmax.

The ordinary gaps may depend arbitrarily on epsilon and may collapse faster than any power. Parameters need not follow an analytic branch or converge. The bounds are uniform on K and for L<=Lmax.

This does NOT cover unbounded word length, h_i tending to zero, unbounded shape parameters, other base coins/scalings or general non-weak words. It is not a cap-nine universal no-return theorem.

## 2. Exact source dependencies and nominal normalization

The actual source-jet candidate is
ACTUAL-WEIGHT15-JETS-AND-WEIGHT30-BRACKET-CANDIDATE.md,
SHA-256 88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa,
with source ledger SHA-256 7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a.

The exact 9/7/6/4 source representation and bilinear rule are:
https://github.com/Sodelin/Research-Commons/blob/ea5d72086ecc9de7faaf417df345f708602f5fd6/research/2026-10-07-dot-g4-coupled-source-state-interface-0252z/METHOD-COMPARISON-AND-SOURCE-STATE.md
https://github.com/Sodelin/Research-Commons/blob/ea5d72086ecc9de7faaf417df345f708602f5fd6/research/2026-10-07-dot-g4-exact-bilinear-source-reduction-0023z/EXACT-BILINEAR-REDUCTION-CANDIDATE.md

Write the representation as

    [ b9  X   Y   V ]
    [ 0   b7  0   U ]
    [ 0   0   b6  T ]
    [ 0   0   0   b4].

For a bare cell X=Y=f=d9, T=H_source=d6, U=-H_source+2e, V=0. Its multiplication is the actual full-source matrix product; no arbitrary matrix is declared physical.

Put alpha=h^3-12(wh-u)^2 and kappa=5/3. The frozen source proof gives

    f=(alpha/15)epsilon^6+O(epsilon^8),
    H_source=kappa f+35h(alpha/15)epsilon^8+O(epsilon^10),
    U+kappa f=-25h(alpha/15)epsilon^8+O(epsilon^10).

Normalize each bare cell by its DETERMINISTIC intrinsic nominal time:

    C_i=E_(-h_i epsilon^2) B_i.                              (2)

This inverse is a proof operation, not a physical edge and not a source-dependent pair normalization. Scaling the original source rows gives EXACT X_i=Y_i. The order-eight corrections cancel:

    X_i=Y_i=x_i,
    T_i=kappa x_i+rho_i,
    U_i=-kappa x_i+sigma_i,
    V_i=0,

    x_i=(alpha_i/15)epsilon^6+O(epsilon^8),
    |rho_i|+|sigma_i|=O(epsilon^10),
    diagonal(C_i)=I+O(epsilon^4).                            (3)

For T, the scaling correction is (15-36)kappa h_i(alpha_i/15)=-35h_i(alpha_i/15), cancelling the displayed bare correction. For U it is (36-21)kappa h_i(alpha_i/15)=25h_i(alpha_i/15), cancelling its bare correction. This verifies BOTH horizontal relations in (3), without using the separate order-ten rank result.

Every remainder in (3) is uniform on K by the actual analytic source formulas and even parity. The diagonal coefficient is the inherited nominal coefficient
c=h^2/2-4(v-2wu+w^2h); no stochastic expectation identity is needed in this proof.

The same actual cycle/path diagonal calculation gives, uniformly on K,

    D4(B_i)=epsilon^8[-h_i^4+4h_i alpha_i]+O(epsilon^10).     (4)

Its accepted prior is:
https://github.com/Sodelin/Research-Commons/tree/8f7091b4f65016120832a6de866d3f241053853e/research/2026-10-08-dot-g4-fixed-coin-short-arms-1040z

## 3. Effective positions never collide faster than the intrinsic cell scale

Suppose, toward contradiction, W=E_T with 0<T<=Hmax. Every actual bare pair hazard is positive, so multiplicativity of b2 gives

    sum_(j=0)^L t_j<=T<=Hmax.

Factor B_i=E_(h_i epsilon^2) C_i and collect all ordinary factors using suffix conjugation. The normalized word is the ordered product of T_(s_i) C_i, with

    s_i=sum_(j=i)^L t_j
                  +epsilon^2 sum_(j=i+1)^L h_j,
    T_s(C)=E_(-s) C E_s.                                    (5)

Its final ordinary normalization may differ from the target time T by O(epsilon^4), but it remains DIAGONAL if W is ordinary. Therefore every X,Y,T,U,V endpoint is exactly zero. No equality between nominal time and true pair hazard is assumed.

The positions are strictly decreasing and satisfy

    s_i-s_(i+1)=t_i+h_(i+1)epsilon^2
                                  >=hmin epsilon^2,         (6)
    0<s_i<=Hmax+Lmax hmax epsilon^2.

Thus the positive nominal time of the NEXT actual cell supplies a separation even when the physical ordinary gap t_i is arbitrarily smaller.

## 4. Uniform approximate moments and central energy

Set beta=6 and

    a_i=exp(15s_i) x_i,
    M0=sum_i a_i,
    Mplus=sum_i a_i exp(beta s_i),
    Mminus=sum_i a_i exp(-beta s_i).

The exact ordinary weights are X,U:15, Y:21, T:9, V:30. With L bounded and positions bounded, (3) and finite matrix multiplication imply uniform constants CM,CV such that exact horizontal and central endpoint zero give

    |M0|,|Mplus|,|Mminus|<=CM epsilon^10,                     (7)

    | kappa sum_(i<j) a_i a_j
                   [exp(beta(s_i-s_j))-1] |<=CV epsilon^16. (8)

Here is the order accounting. A horizontal factor is O(epsilon^6); multiplying it by a diagonal correction O(epsilon^4), or using rho/sigma, gives O(epsilon^10). The central entry has only the two paths XU and YT. Their leading products are O(epsilon^12); a diagonal correction raises the order to sixteen, as does an O(epsilon^10) horizontal error multiplied by O(epsilon^6). Every bare V is exactly zero. No triple off-diagonal path exists because the middle 7-to-6 entry is zero. Uniformity follows from compact K, finite Lmax and bounded exponential clock factors, even when individual gaps vanish.

The constants CM,CV can be any finite uniform bounds on these remainders obtained from the exact finite source functions on those compact domains. Their numerical values are not claimed evaluated.

Put

    Q=sum_(i<j) a_i a_j sinh(beta(s_i-s_j)).

Pure algebra, without requiring exact moment zero, gives

    sum_(i<j)a_i a_j[exp(beta(s_i-s_j))-1]
       =Q+(Mplus Mminus-M0^2)/2.

Consequently, for epsilon<=1,

    |Q| <=(CV/kappa)epsilon^16+CM^2 epsilon^20.              (9)

## 5. Boundary-corrected Green energy

For x real define

    F(x)=sum_i a_i sinh(beta|x-s_i|).

Distributionally F''-beta^2 F=2beta sum_i a_i delta_(s_i). Choose epsilon small enough that all nodes lie in [0,Hmax+1/2], and integrate over the fixed interval

    I=[-1,Hmax+1].

The values of F,F' at both endpoints are linear combinations of Mplus,Mminus. Equation (7) bounds them by CM epsilon^10 cosh(beta(Hmax+1)), with an additional factor beta for F'. Thus

    |[F F']_boundary|
       <=2beta CM^2 cosh^2(beta(Hmax+1)) epsilon^20.

Let

    Energy=integral_I [F'^2+beta^2 F^2].

The exact integration-by-parts identity is

    Energy=[F F']_boundary-4beta Q.

Combining with (9) gives the explicit sufficient uniform bound

    Energy<=CE epsilon^16,

    CE=4beta CV/kappa
           +CM^2[4beta+2beta cosh^2(beta(Hmax+1))].          (10)

Only a bound on the complete word's positive ordinary window is used. There is no division by a nearly singular moment matrix and no replacement of the actual atom positions.

## 6. A coercive bound valid down to epsilon^2 spacing

Put c0=min(hmin/3,1/4) and ell=c0 epsilon^2. For sufficiently small epsilon, beta ell<=1 and the intervals [s_i-ell,s_i+ell] lie in I and are pairwise disjoint by (6).

On each left and right half-interval, F''=beta^2 F. The elementary endpoint trace estimate, applied to F', is

    |F'(s_i +/-)|^2
       <=(2/ell) integral F'^2+2ell integral F''^2
       <=(4/ell) integral [F'^2+beta^2 F^2].

The derivative jump is 2beta a_i. Squaring it and adding the two half-interval bounds gives

    integral_(s_i-ell)^(s_i+ell) [F'^2+beta^2 F^2]
                            >=(beta^2 ell/2) a_i^2.

The intervals are disjoint, so

    Energy >=(beta^2 c0/2)epsilon^2 sum_i a_i^2
             =18c0 epsilon^2 sum_i a_i^2.                  (11)

This is the needed uniform replacement for a fixed positive separation. It also applies when L=1.

From (10)-(11),

    sum_i a_i^2 <=[CE/(18c0)]epsilon^14.

Since s_i>=0, |x_i|<=|a_i|. Choose Cx with
|x_i-(alpha_i/15)epsilon^6|<=Cx epsilon^8 uniformly on K. For epsilon<=1,

    |alpha_i| <= Calpha epsilon,
    Calpha=15[sqrt(CE/(18c0))+Cx].                          (12)

Thus every leading third-defect amplitude is small, even though no limiting distinct-position hypothesis was imposed.

## 7. Final actual fourth-defect contradiction

Let C4 uniformly bound the remainder in (4) by C4 epsilon^10. Ordinary padding leaves D4 unchanged, and actual serial composition adds it exactly. An ordinary endpoint must therefore satisfy

    0=epsilon^(-8)D4(W)
      =sum_i[-h_i^4+4h_i alpha_i]+error,
    |error|<=L C4 epsilon^2.

Using (12),

    epsilon^(-8)D4(W)
      <=L[-hmin^4+4hmax Calpha epsilon+C4 epsilon^2].

This is strictly negative for all sufficiently small positive epsilon. For example impose, in addition to the source/spacing bounds already stated,

    epsilon<=min(1,
                 hmin^4/(16hmax Calpha),
                 sqrt(hmin^4/(4C4))),

with a zero-denominator bound interpreted as unnecessary. The bracket is then at most -hmin^4/2. This contradicts ordinary equality and proves the proposed theorem.

All constants depend only on the declared compact source set, Lmax,Hmax and the fixed original representation. No uniformity in unbounded word length, vanishing hmin or arbitrary source architecture is inferred.

## 8. Master boundary and prior relation

The earlier separated-window Green argument needed distinct fixed limiting positions. This proof, if accepted, replaces that assumption by the intrinsic positive cell-time spacing and a quantitative local trace estimate. It still addresses only bounded-length compact fair-parabolic weak words.

A family seeking bounded-target ordinary returns can evade this conclusion by growing its number of cells, approaching a different boundary/scaling, or leaving this compact fair-base chart. The original all-cap return thresholds may still be bounded or unbounded; neither alternative is settled.

No claimed cancellation uses source-dependent pair calibration, an external mixture, independent per-arity parameter fitting, or a physical inverse ordinary edge. General G4 and its original legal-observation transfer remain open.
