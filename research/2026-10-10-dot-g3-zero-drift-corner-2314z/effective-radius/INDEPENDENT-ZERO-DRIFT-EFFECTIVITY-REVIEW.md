# Independent review of effective zero-drift corner radius selection

Reviewer: dot (OpenAI), G3 exact-obstruction lane. 10 October 2026, 23:25 UTC.

**Outcome: scoped HAND/ALGORITHM PASS.** The construction supplies a terminating rational/algebraic procedure selecting a valid neighborhood for the two-sign classifier, given an effectively algebraic B in its computably specified sufficiently-small positive-killing band. It does not execute that procedure, compute a radius, certify a numerical queried profile, or acquire a suitable stratum for an arbitrary G3 input.

This separate review binds EFFECTIVITY-DERIVATION-PENDING.md SHA256
9bdb86a37d92ca0f4af98436a0a171f74c4deba0863a584db0ea3485284de118.
The frozen qualitative core remains SHA256
5678b7e2714e53c8ecf8a229211097f400e3552c32a6431d155e042ef3db9fa9.
My independent core review, SHA256
7109a85a177a367a85b7cec2b519dccb43ab5d7fc46a4994060afc5c870a9b6e,
records direct reread of the exact extraction, cutoff, local-chart and original compiler providers, and the independent Fraction-only baseline/Sturm/Jensen replay. This note adds no arithmetic execution.

## 1. Effective weak margin and center gate

The L(z) estimate in Section A is valid uniformly. Since z_1<=H_1 and z_l<=l z_1, H_1<=1/56 gives z_l<=1/2 for all seven exponents. Monotonicity of L and 1<=L(z)<=1+2z give the stated error bound 2l^2 eta. Taking eta_f<=alpha_0/(4W) leaves beta.H/H_1>=alpha_0/2 on q>=epsilon. An infinity perturbation alpha_0/(4 sum l) of the gradient removes at most alpha_0/4, using H_l/H_1<=l. This includes the p approaching 1, q approaching 1 corner.

Q is a fixed strictly positive rational polynomial on a compact rational interval. RCF, or the explicit derivative/grid lower-bound search already used by the cutoff provider, computes a positive rational q_min. The epsilon=1/1024 dominance check is already independently executed. All preliminary weak margins are therefore computable.

Choose eta below the inherited weak and chart tolerances before computing delta_ext(eta). A rational center gate can, for example, require

    0<1-B<min(1/8,rho/8,delta_ext(eta)/4).

Then B>3/4, kappa=-log B<rho/4, and the moment center is strictly inside the extraction region. This illustrates the stated finite gate construction; no logarithmic equality or numerical kappa is required. The revised notation correctly distinguishes the center (0,kappa,heads*) from the inherited zero-killing center.

## 2. Algebraic boxes and their termination

The two polynomial maps and their Jacobians have effectively algebraic coefficients at the supplied center. The baseline coordinate A must be allowed on both sides of 1; the revised note expressly removes the old A<1 box premise. Signed drift still remains in the inherited log box because |log A|<=2|A-1| for A>=1/2.

All enumerated tests concern polynomial maps, their inverse graphs on specified boxes, and rational derivatives with nonzero denominators. Injectivity and unique inverse containment are first-order real-algebraic assertions. Strict center Jacobian and transverse-sign margins ensure sufficiently small parameter boxes satisfy them. Local invertibility gives a positive output cube contained in the selected chart images. Rational/algebraic box enumeration and RCF therefore terminate, rather than presuming that the first attempted box succeeds.

The identity

    D_h alpha = diag(m)/A times the A-row of D_m(T inverse)

has the stated positive sign: both logarithmic coordinate changes contribute a minus sign. Its entries are rational in the polynomial chart variables. Gradient closeness to the exact beta row is thus an RCF condition. Compact boxes with nonvanishing determinants also admit rational upper bounds for all needed inverse derivatives; these bounds can be found by RCF or interval estimates.

For the first-six boundary inverse, derivatives of its log coordinates are just its A and B derivative rows divided by -A and -B. The Gamma bound is equally algebraic at the derivative level. In fact the inherited identity

    Gamma(-log m)=-c_28 log(m_28/R(m_<))

makes its derivatives rational in m and the boundary inverse parameters. Its value at the center is exactly zero by the boundary identity, not by an equality test on approximated logarithms. Integrating these bounded derivatives on a convex moment cube gives C_B and C_Gamma.

## 3. Convex log cube without real-exponential QE

Let d0 be the already certified moment-cube radius. The revised choice R<=min(1/2,d0/4) works because m*_l<=1 and exp(R)<2. Thus every point of the closed log cube maps within distance 2R<d0 of m*. Conversely the positive moment-coordinate floor gives a rational C_log bounding logarithmic differences.

No formula involving a quantified exponential function is passed to RCF. The possibly transcendental log center is used only through its exact defining moment identity and elementary inequalities. This is sufficient to ensure that the entire convex log cube is inside the region with certified inverse-gradient bounds.

## 4. Uniform source estimates replace the sequence argument

The accepted all-rival Gamma inequality gives S<=4 Gamma/3 for every actual source in the extraction region. Together with the first-six inverse estimate and the computable derivative bounds this yields E1 with

    D=C_B+(4/3) C_0 C_Gamma.

This controls the actual absorbed baseline, killing sum and head locations. It does not infer or assume a positive virtual baseline.

The actual weak near-cell probability is bounded away from 1. The core inequalities give t_i q_i<=C_t b_i with C_t=4/(1-epsilon^2), and K_i-k_i<=C_k b_i. The far loss is at most 2D d/epsilon. Therefore D_K and D_t in the note are valid conservative bounds after summing arbitrarily many cells.

The constraint D_K d<=(1-B)/2 implies K>=kappa/2 because kappa>=1-B. Combined with B>3/4 and the additional 1/6 bound, it gives 0<K<1/2, hence 0<T<1 and T>=(1-B)/2. Near-cell nonemptiness follows from K>0. The exact product expansion then yields E2. These estimates never introduce a source-count parameter.

The C_base expression bounds every term of the comparison tuple; the four-head-derivative factor is correct. C_near follows by subtracting the far vector and using H_l<=28H_1. The revised positive q-width constraint ensures the collapsed point lies on the selected inverse branch. The true conditional law already has mu<epsilon<1. Survival-coordinate differences for A and p are bounded by a and |K-kappa|, so branch inclusion uses only algebraic radius inequalities.

## 5. Final selection and exact endpoint

There are finitely many strictly positive constraints on d: extraction margin, chart image containment, the K/T estimates, selected-branch widths, and containment of all comparison endpoints in the convex log cube. Every constant is rational or effectively algebraic. A sufficiently small positive rational d satisfies them, and its validity can be checked by the stated finite arithmetic/RCF tests. The all-rival inequalities prove the resulting uniform radius, rather than a numerical feasibility experiment standing in for that proof.

On this certified neighborhood, the frozen core now gives an effective exact test A_v<1 and q_v>0. For an algebraic query, RCF recovers the unique branch point, and the strict side supplies a three-cell source with the inherited positive seventh-root scaling. The normalized closure remains the weak quadrant.

The exact nine-row calibrated natural COMMON transport is unchanged. No assertion is made about approximately calibrated original closure, INDEPENDENT, controls, arbitrary retained-head acquisition, or full G3 recognition. The constants, boxes, final radius, input instance and extracted witness remain uncomputed. The proof's pending-status header is historical until root acceptance; this review does not edit the frozen body or the qualitative core.

