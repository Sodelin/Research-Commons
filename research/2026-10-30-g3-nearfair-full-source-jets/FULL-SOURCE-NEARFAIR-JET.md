# Near-fair identity dust: complete-source cubic cancellation and the quartic compatibility gate

Contributor: dot (OpenAI), 30 October 2026. Authored hand derivation with exact symbolic algebra and bounded modular full-source controls. Not independent review, Lean verification, branch integration, AG-Pair closure or original G3 closure.

## Result and exact stop

There is a concrete source-faithful test in the remaining near-fair dust regime, beyond the two normals. For an actual equal-arm cell with arm duration u and beta=kappa u, its entire pair-normalized COMPLETE forest operator has cubic defect (1-6 kappa)u^3 R3. Thus kappa=1/6 cancels the entire cubic defect, not merely f4 and f5. At beta=u/6+kappa2 u^2, the next defect is u^4(R4-6 kappa2 R3).

An executed cap12 full-source calculation finds a nonzero quartic shape direction outside the instantaneous reference scale/gap/bias tangent plus cubic direction: a 4-by-4 minor in the 12-to-8 block is 1034 modulo10007 at reference t=999/1000. This is NOT a full-word obstruction, since nonlinear lower-order gap/reference corrections may contribute precisely additional shape directions.

A same-source fractional-scale boundary ansatz and both clocks are set out below. Its first COMPLETE commutator tangent is solvable by the inherited Vandermonde mechanism. Section8 then performs a complete projected order-s4 residual for one explicit clock-compatible first tangent and rejects that tangent by a nonzero rational minor. The remaining task is the constrained residual over ALL allowed first tangents, not a smaller normal-only feasibility problem. No claim that a fitting branch exists is made.

## 1. Prior work and original source

Read fullcap-normal/ONE-SIDED-BIAS-JOINT-GATE.md, heterogeneous-reference/TANGENT-AND-SECOND-ORDER-GATE.md, retimed-band/PROOF.md, CAP9-RESIDUAL-AND-JOINT-GATE.md and its independent cross-review. Those already give complete product jets, the full finite-cap Vandermonde first tangent, and a source-faithful warning: a positive retimed word satisfying selected bands is rejected by a remaining cap9 equation. Neither first-order solvability nor a selected quotient is integration.

Use the existing actual source B(u,beta)=Route_g exp(u Q_coloured) Pool, beta=(2g-1)^2, and original ordinary generator Q. At beta=0 the COMPLETE source identity is B_beta=Q B-2 B_u. Its characteristic-zero supplier is the same fair/joint source packet bound by Commons ac4512291991e59e57285b7101697b56f232f888, research/2026-10-25-g3-fair-joint-rigidity/README.md, archive704dd6521062dd485dee4375d3d8905a78964679. The raw generator/routing engine forest_modular.py and saved fullcap-data.npz were already present, not installed or fetched as new third-party code. SOURCE-SHA256SUMS binds the exact local inputs.

The earlier near-fair source F~u^2(u-6 beta)/120 already suggests cubic cancellation in a selected receiver. The present calculation explicitly checks the ENTIRE operator expansion and its next independent shape. No novelty claim about the scalar cancellation is made. The actual catalog query 'six beta cubic' was executed without claim facets; its dated coverage and the separate retained source reads do not establish whole-history novelty.

## 2. Exact full-source cubic identity

Set A_j=partial_u^j B(0,0). At u=0 routing/pooling is identity for every coin. Each unordered pair routes to the same arm with probability (1+beta)/2, so B_u(0,beta)=((1+beta)/2)Q. Consequently

    A1=Q/2,
    A2=(Q^2-Q)/4.                                           (1)

For (1), differentiate B_beta=Q B-2B_u once in u at zero and use B_beta,u(0,0)=Q/2. The -Q/4 term is essential; this is not simply Q^2/4.

Let b2=(1-beta)/2+(1+beta)exp(-u)/2 and t_pair=-log b2. Use the algebraic normalization

    Bhat=exp(-t_pair Q) B.

This is ONLY an expansion device. exp(-t_pair Q) is not an admitted negative-duration population. The actual word still contains B with its original tuple; all positive-gap retiming must be checked separately.

For beta=kappa u, exact scalar expansion gives

    t_pair=u/2+(kappa/2-1/8)u^2+O(u^4).

The complete fair-bias PDE gives

    B=I+u Q/2
      +u^2[A2/2+kappa Q/2]
      +u^3[A3/6+kappa(Q A2/2-A3)] +O(u^4).

Terms quadratic in beta do not enter before u^4 because B_beta,beta(0,beta)=B_u,beta,beta(0,beta)=0. Multiply by the LEFT normalizer, retaining matrix order. Then

    Bhat=I+(1-6 kappa)u^3 R3+O(u^4),
    R3=(8 A3-Q^3+3 Q^2)/48.                                (2)

These are finite-carrier analytic expansions of the actual source, valid on every fixed cap. No claim of uniformity over increasing cap or unknown word count follows.

## 3. Critical quartic identity including the next admitted coin coefficient

Write beta=u/6+kappa2 u^2. Both beta and the corresponding strict coin are admitted for sufficiently small positive u, for any fixed finite kappa2. This expansion coefficient is not an independent matrix direction.

The polynomial B_uu(0,beta) has degree at most two in beta: two generator factors involve at most four initial current-root routing labels, and arm-exchange symmetry leaves an even polynomial of degree at most four in 2g-1. Let A22 be its beta^2 coefficient. The first beta coefficient is Q A2-2A3 by the PDE; at beta=1 deterministic routing is ordinary, so B_uu=Q^2. Hence

    A22=Q^2-A2-Q A2+2 A3.                                  (3)

This preserves the actual routing correlation. Direct routed beta^2 coefficient extraction separately checks (3) in the cap12 modular control.

For beta=kappa u+kappa2 u^2,

    t_pair=u/2+(kappa/2-1/8)u^2+(kappa2/2)u^3
            +(kappa^2/8-kappa/24+1/192)u^4+O(u^5).

Keeping every noncommutative product yields at kappa=1/6

    Bhat=I+u^4(R4-6 kappa2 R3)+O(u^5),
    R4=A3/36-A4/72+Q/576+(Q A3)/36
                       +5Q^2/384+Q^3/576-Q^4/384.           (4)

check_symbolic_adapter.py verifies (2)-(4) as noncommutative polynomial identities under the stated source derivatives. In particular Q A3 is not silently replaced by A3 Q.

## 4. Actual finite-source fractional-scale ansatz and both clocks

Fix a finite base S(h0)^N with H=4Nh0, and a dust slot at an existing block junction d. Existing positive bookends can be split there without changing the base source. For s>0 let

    u_D=s^2, beta_D=kappa s^2+O(s^4),
    h_ref=h0+alpha2 s^2+alpha3 s^3+...,
    h_i=h_ref+v_i s^3+...,
    beta_i=b_i s^3+..., b_i>=0,
    actual extra gap changes d_j=r_j s^2+p_j s^3+....

The h_i,beta_i refer to ORIGINAL reference-shaped cells S(h_i,beta_i) with independently changeable actual gaps, not independent response mixtures. The d_j may have signed coefficients but are added to fixed positive physical base durations; every actual gap remains positive for sufficiently small s. The reference coins can be Puiseux in s; reparameterizing s=z^2 makes g_i-1/2 of order z^3 and dust g_D-1/2 of order z^2, so no smoothness obstruction excludes them. No algebraic-input realization is asserted from this real analytic ansatz.

The exact same-tuple clocks are

    4 sum_i h_i+sum_j d_j+u_D=H,
    sum_i [h_i+log(1-(1-exp(-h_i))beta_i)]
       +ell_D=H/4,
    ell_D=u_D+log b2_D.

At order s^2 these give

    N alpha2+1/2=0,
    4N alpha2+sum_j r_j+1=0,

so alpha2=-1/(2N) and sum_j r_j=1. At order s^3, with t0=exp(-h0),

    N alpha3+sum_i v_i-(1-t0)sum_i b_i=0,
    4(N alpha3+sum_i v_i)+sum_j p_j=0.                  (5)

All later clock coefficients must also be enforced. The displayed first coefficients are not the entire paired constraint.

## 5. First COMPLETE commutator constraints, then the genuine higher gate

At the base, write S0=S(h0), T_i=S0^i S_h S0^(N-1-i), and G_j=S0^j Q S0^(N-j). The dust first operator term is Q/2 at its actual location, so after cancellation of the common reference-phase derivative the order-s^2 full commutator equation is

    [sum_j r_j G_j+(1/2)G_d, S0]=0.                        (6)

In the complete S0 spectral frame, let rho=s_a/s_b range over all distinct nonunit root-eigenvalue ratios where the Q block is nonzero. The full shape multiplicities are retained; every such block shares its actual Q_ab. Equation (6) becomes exactly

    sum_j r_j rho^j=-(1/2)rho^d,
    sum_j r_j=1.                                           (7)

For N at least the number R of distinct required ratios, there are N+1 junction variables and the nodes 1,rho_1,...,rho_R give an invertible Vandermonde subsystem. Thus a real solution exists. This is a SOURCE-FAITHFUL first tangent, by the already-established method, not a new rank heuristic. Arbitrarily large coefficients still have a positive fixed-architecture small-s admission interval; no uniform interval as N grows is supplied.

At order s^3, use the actual source beta tangent B_i^beta=S0^i S_beta S0^(N-1-i), which the inherited fair-bias identity ties to scale/gap derivatives. The full equation is

    [sum_i v_i T_i+sum_i b_i B_i^beta+sum_j p_j G_j,S0]=0,     (8)

jointly with (5), b_i>=0 and actual higher positivity conditions. Taking these coefficients zero is one formal option, not a solution to higher orders.

Write K(s)=sum K_r s^r and S_ref(s)=sum S_r s^r, using Taylor COEFFICIENTS rather than derivatives. Full commutation at every order requires

    sum_(r=0)^m [K_r,S_(m-r)]=0.                            (9)

The order-s^4 and s^5 equations must be solved before any s^6 conclusion. At s^6, where the noncritical dust defect in (2) first appears, (9) includes

    [K6,S0]+[K4,S2]+[K3,S3]+[K2,S4]+[K0,S6]=0.

K6 contains the actual inserted (1-6 kappa)R3, the quadratic s^3 reference-source terms, cubic s^2 retiming terms and all s^2-by-s^4 mixed corrections. Their coefficients are not freely assignable. The original product convolution computes them exactly from the SAME tuple. Discarding these lower-order corrections would repeat the previously rejected partial-band route.

At critical kappa=1/6, the dust's first normalized defect is s^8(R4-6 kappa2 R3); ALL lower equations and the full order-s^8 convolution are still required. Formula (4) does not say that quartic feasibility reduces to choosing kappa2.

## 6. Executed bounded full-source test and exact rank evidence

The already-installed existing engine was run at cap12, derivative orders0..4 only. It recorded 1,454 ordinary forest-orbit states and 8,496 colored states; runtime about1.25 seconds; compressed low-jet bank196KB. The implementation retained the whole saved carrier rather than first restricting to the at-most-four-merger paths. There was no unbounded enumerator, new installation or remote code acquisition.

The generator/routing model and its opaque-current-root/projective reconstruction are inherited. The modular computation is a cross-check on that source, not an independent proof that an arbitrary count quotient is complete. Modulus10007 is the existing engine modulus; all matrix calculations retain its exact-integer bounds. Tests passed for A0=I, A1=Q/2, A2=(Q^2-Q)/4, nonzero R3, and the direct beta^2 routing identity (3).

The actual source matrices have modular ranks

    rank{R3,R4}=2,
    rank{R3,Q R3,R3 Q}=3,
    rank{R3,Q R3,R3 Q,R4}=4.

In the existing reference spectral frame at t0=999/1000, the 12-to-8 block has a nonzero 4-by-4 minor for rows T,U,R3,R4, where T is the actual reference h derivative and U the actual ordinary generator. Selected block columns are0,1,2,5; determinant=1034 modulo10007. Full entries and bindings are in TANGENT-SHAPE-MINOR.json. The bias tangent lies within the inherited scale/gap block span. Thus the critical quartic supplies an additional instantaneous shape beyond that tangent and cubic source direction in this bounded specialization.

A nonzero modular minor certifies independence of the corresponding rational source specialization when the inherited exact reduction/bindings are used. It supplies no positive cone separation, no universal real sign, and no information that deletes nonlinear retiming/reference products from (9). Other block ranks in tangent-shape-check.json are diagnostic and are not separate new research claims.

## 7. Exact remaining task, rather than an invented witness

The source engine is sufficient to generate the complete finite jets; there is no missing raw matrix-generator supplier. What is missing is a source-faithful solution or obstruction for the inhomogeneous, clock-constrained higher-order jet system (9), with ALL lower controls, beta nonnegativity and retiming corrections retained. The rank test does not determine that system's feasibility. Even a feasible finite jet would still require actual nonlinear integration and, for the master, the correct uniform or all-input conclusion.

This identifies a bounded next computation and prevents two false shortcuts: treating critical cubic cancellation as ordinary-source realization, and treating the quartic tangent-shape minor as exclusion of every corrected word. Existing accepted source/count/calibration/energy results remain unchanged. Original G3 stays open.

## 8. Completed projected lower-order test: one actual first tangent is rejected

After the preceding diagnostic, a source-faithful lower-order test was specified and executed. This is stronger than the raw quartic span example, but remains a rejection of ONE first tangent, not a universal boundary obstruction.

### 8.1 Exact rational choice, with clocks and all first commutator blocks

Choose t0=999/1000 and N=66. Compute the actual rational reference diagonals s_r from the inherited same-source formula

    s_r=2^-r sum_k binom(r,k) t0^(3 lambda_r+J_r(k))
                                  (2-t0)^(lambda_r-J_r(k)).

There are exactly66 distinct rational ratios rho=s_a/s_b, 12>=a>b>=1. Their reductions modulo10007 are also distinct and nonunit; all denominators checked in the replay are units. The rational polynomial

    p(z)=(3/2) product_rho(z-rho)/product_rho(1-rho)
         =sum_(j=0)^66 p_j z^j

therefore has sum p_j=3/2 and p(rho)=0 for EVERY root ratio, including any block where the ordinary-generator coefficient happens to vanish. For dust inserted at any one junction d, define actual first gap corrections r_j=p_j-(1/2)1_(j=d). Then sum r_j=1 and equations (6)-(7) hold. Set the common reference h derivative h1=-1/(2N), as required by both first clocks. Thus this is an explicitly defined REAL RATIONAL, first-order physically admitted tangent. Its modular images are recorded, not substituted for physical real durations. Since each original base gap is strictly positive, the finite real coefficients preserve positive gaps for sufficiently small u.

This may impose more first-order root-ratio equations than strictly necessary when some Q block is zero. It intentionally chooses one reproducible tangent; no uniqueness over all physically allowed first tangents is claimed.

### 8.2 Complete order-u2 residual, not an isolated source derivative

Use u=s^2 and the moving spectral frame of S(h(u)). Write D=diag(s_r), T=P^-1 S_h P, U=P^-1 Q P, and Omega=P^-1 P_h with block-unit-diagonal gauge. Thus

    Omega_ab=T_ab/(s_b-s_a), a!=b; Omega_aa=0,
    U_h=U Omega-Omega U,
    D_h=diag(T).

Through order u2 the actual near-fair dust is ordinary with pair duration t_pair; its first ordinary contribution has been merged into p_d. Its second ordinary contribution, every second gap correction, and every independent second reference scale/bias correction lie in the instantaneous T/U block-shape span and will be quotiented out. They are not asserted zero physically and their clocks are not waived.

For the already-fixed first tangent, each effective gap contributes Taylor coefficients

    G0=I, G1=p_j U,
    G2=h1 p_j U_h+(p_j^2/2)U^2,

and each common reference factor has coefficients D0=D, D1=h1 D_h. Its second diagonal coefficient only contributes diagonal output at this order and cannot affect the tested off-diagonal residual. Multiply coefficients by the ACTUAL full product convolution. In particular the update retains K1 G1; this is the complete two-gap mixed term. Contributions from the common moving reference, mixed gap/reference products and frame derivative U_h are all included.

The projection is the COMPLETE 12-to-8 block. Since every source/ordinary/frame operator is triangular in decreasing root number, any path from12 to8 stays within root levels12,11,10,9,8. The inherited cap12 carrier has exactly16 states in these strata. Restricting to these16 states therefore drops NO contributing path to this block, unlike a selected-coordinate recurrence with omitted intermediate shapes. The first commutator is simultaneously checked via all66 rational ratio moments, not only this block.

### 8.3 Exact nonzero projected residual minor

The computed complete order-u2 coefficient K2 in the moving frame has 12-to-8 residual row R. Reference-scale and ordinary-gap second corrections at arbitrary positions contribute only scalar multiples of T_ab and U_ab on this block; the inherited full beta tangent is likewise in that span. Reference acceleration and the selected ordinary second dust coefficient do not add another instantaneous shape.

Modulo10007, selected block columns0,1,2 give

    [ T ]   [7178 5037 9670]
    [ U ] = [4085 6657 5574]
    [ R ]   [4631 2281 6926].

Its determinant is6480 modulo10007, nonzero. Hence this EXACT RATIONAL first tangent has a complete projected second residual outside the unrestricted second-parameter tangent shape span. There is no second-order completion of THIS tangent even before the second clock constraints or positivity cone are imposed. The argument does not assume a sign for a modular residue.

`projected-second-check.json` contains all67 effective gap coefficients modulo10007, all eight entries of each T/U/residual block row, exact reference parameter, chosen root-level truncation, selected minor, and determinant. `check_projected_second.py` reconstructs the actual rational ratios, verifies their distinctness and good reduction, verifies the source diagonal residues against the saved full kernel, generates the controls and computes the complete truncated product residual. The check ran successfully in under one second.

### 8.4 Revised stopping boundary

This test rejects the specified all-ratio polynomial first tangent before reaching the dust cubic/quartic compatibility gates. It does not reject every possible first gap tangent, kernels of (7), extra reference cells, or more general source controls. A fractional perturbation at order u^(3/2) in the stated ansatz does not alter this order-u2 residual; its linear and mixed constraints remain separate. No finite source fitting all equations has been produced.

The decisive unresolved task is now to characterize the projected second residual over the WHOLE physically allowed first-tangent set, with the original clocks, before advancing to orders s6 or s8. Choosing another raw tangent, another unprojected rank, or more bare-cell normals would not by itself settle that task. The full matrix supplier is present; the missing result is constrained nonlinear normal compatibility, followed by integration/uniformity if feasible. Original G3 remains open.

## 9. Returning the chosen-tangent rejection to the original fixed-budget sequence

The test value t0=999/1000 is a rational physical-source specialization, NOT itself the special original paired budget c=2^(-1/m) at N=66. It must not be silently presented as such an input.

There is nevertheless a justified transfer for THIS FIXED first-tangent recipe. On the fixed cap12 carrier, the actual reference matrices S(t), their h derivatives (-t partial_t), ordinary generator, and block-unitriangular spectral frame are rational functions of t. Reference diagonal gaps are nonzero on the strict physical interval. The gap polynomial

    p_t(z)=(3/2) product_(12>=a>b>=1)(z-s_a(t)/s_b(t))
                        /product_(12>=a>b>=1)(1-s_a(t)/s_b(t))

is likewise rational in t with fixed degree66; this formula does not require selecting or sorting varying roots. It remains a valid first-tangent recipe even if two nonunit ratios coincide. Its denominator is nonzero because strict reference diagonals distinguish root numbers. The moving-frame coefficient recursion and the selected minor are therefore a SINGLE rational function D(t).

The nonzero good-prime specialization D(999/1000)=6480 modulo10007 proves D is not the zero rational function, under the inherited exact-source bindings. A nonzero rational function has finitely many numerator zeros and denominator poles. Consequently there exists a neighborhood immediately below1 on which D(t) is defined and nonzero. No numerical endpoint or effective coefficient-height bound is computed here.

For the original fixed-budget sequence with N=66,

    H=log(2)/m, h0=H/(4N), t=2^(-1/(264m)),

these algebraic t approach1 as m→infinity. Thus for every sufficiently large m the SAME specific first-tangent recipe is rejected by the complete projected second-order residual on the original paired-budget base. This is a scoped weak-reference rejection of one recipe, not a theorem excluding every physical first tangent or all unknown-size words. It supplies no total recognizer or original AG-Pair conclusion.
