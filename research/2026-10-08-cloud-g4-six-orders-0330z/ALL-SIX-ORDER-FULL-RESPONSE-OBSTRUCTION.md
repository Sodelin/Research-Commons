# The exact 1:6:10 diagonal family has no full ordinary response in any order

Contributor: Codex Cloud G4 / CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 03:30 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No deterministic symbolic exploration, coefficient harness, source producer, parameter scan, numerical job, API or compiler ran.

The preceding [general-ratio source proof](../2026-10-08-cloud-g4-general-ratios-0318z/GENERAL-RATIO-DIAGONAL-FEASIBILITY-AND-RESPONSE-GAP.md) constructs actual strict three-half-coin words with ratios (1,6,10) and ordinary no-merger diagonals through five roots. Its displayed order fails the full four-root C/H response. This note analyzes ALL SIX chronological orders, allowing arbitrary positive internal connectors and positive exterior pads. The two interleaved sign orders also fail, because their exact C/H equations force a connector gap smaller than the original source permits.

## 1. Exact statement and source premises

Use three natural private INDEPENDENT bigons, each routing every CURRENT ROOT independently with coin 1/2. Arms are

    x_i=1-A_i t-sqrt(w_i)t^(3/2),
    y_i=1-A_i t+sqrt(w_i)t^(3/2),                       (1)

where the three A labels are 1,6,10, t>0, w_i>=0, and every arm is strictly in (0,1). Parameters are shared across all arities. The chronological order may be any permutation. Internal connectors z1,z2 and exterior pads are arbitrary survivals in (0,1); no assumption that their hazards divided by t are bounded is imposed.

Suppose the SAME actual word satisfies

    b3=b2^3,          b4=b2^6,          b5=b2^10.       (2)

There is a sufficiently small t0>0 such that no source of this class with 0<t<t0 has C=H=0 in the complete original four-root quotient, whatever its order, positive connectors or ordinary pads. Thus it cannot be an ordinary full cap-five return. In particular the analytic family previously constructed from the three diagonal equations cannot be made a full ordinary return by reordering its cells or varying only its connectors/pads.

The proof actually applies to every actual w satisfying (2) in this fixed-ratio near-identity class, not merely an analytic IFT path. Exact third matching forces bounded w by the inherited positive-ratio argument; the normalized leading three equations have invertible Vandermonde matrix. Hence, after attaching weights to their A labels,

    w_i=w_i^0+O(t),
    w^0=(393/50,327281/2400,9377/160).                 (3)

This is derived from the actual source and exact equalities. There is no free formal realization or independent higher-arity fitting.

Let q_i=b2(B_i), r_i=b4(B_i), c_i=C(B_i), H_i=0. The original source polynomials give

    q_i=1-A_i t/2,
    c_i=(A_i^3/12-w_i/2)t^3+(A_iw_i/4)t^4.             (4)

The leading c coefficients attached to labels 1,6,10 are respectively

    -Psmall=-577/150,
    -Plarge=-240881/4800,
    Qpositive=51869/960.                              (5)

They obey Qpositive=Psmall+Plarge. Thus cell 10 is positive, and cells 1 and 6 are negative, uniformly for sufficiently small t.

## 2. Exact composition already excludes four orders

For a chronological triple, the exact original quotient product gives

    C=alpha1 c1+alpha2 c2+alpha3 c3,
    D=C+H=beta1 c1+beta2 c2+beta3 c3,
    alpha1=z1 z2 q2 q3,
    alpha2=r1 z1^6 z2 q3,
    alpha3=r1 r2 z1^6 z2^6,
    beta1=1,    beta2=r1 z1^6,    beta3=alpha3.         (6)

All coefficients are positive, with strictly decreasing ratios

    beta1/alpha1=1/(z1 z2 q2 q3)
       >beta2/alpha2=1/(z2 q3)>beta3/alpha3=1.         (7)

Orders (1,6,10),(6,1,10) have signs (--+). If C=0, subtract the last ratio from D; both negative terms remain strictly negative, so D<0. Orders (10,1,6),(10,6,1) have signs (+--). If C=0, subtract the first ratio; both remaining negative terms multiply negative ratio differences, so D>0. In neither case can C=D=0. This argument uses the exact source coefficients and permits any strict connectors.

The remaining orders are (1,10,6),(6,10,1), both with signs (-,+,-). Their two-sign-change pattern defeats the preceding separator. The next source identity controls them.

## 3. An order-independent fifth-order source identity

For one cell put s=1-At, h^2=wt^3, q=1-At/2, r=b4, and define its original diagonal differences D3,D4,D5. The accepted finite source coefficients extend through the needed order as

    D3=(-A^3/8+3w/4)t^3
           +(-3A^4/16+3Aw/8)t^4-(3A^5/16)t^5+O(t^6),
    D4=(3A^4/16-3Aw/2)t^4+(3A^5/8)t^5+O(t^6),
    D5=(-3A^5/8+15A^2w/4)t^5+O(t^6).                (8)

The D5 line is the preserved finite-routing derivation. Here is a direct hand reproduction of the extra D3,D4 coefficients. The exact third ratio is

    b3/q^3=1+t^3[(3/4)(1-At)w-A^3/8]/q^3.

Expansion of q^-3 through t^2 gives the first line; its squared log correction begins at t^6. For the four-root source polynomial, expansion of the original expression gives

    r-q^6=(-A^3/2+3w)t^3
             +(15A^4/16-9Aw)t^4
             +(-9A^5/16+45A^2w/4)t^5+O(t^6),
    q^-6=1+3At+(21/4)A^2t^2+O(t^3),
    log(r/q^6)=(-A^3/2+3w)t^3
                    -(9A^4/16)t^4-(3A^5/8)t^5+O(t^6).

Since D4=log(r/q^6)-4D3, this proves its line in (8). All remainders are uniform for the bounded physical w derived from (2), so substituting arbitrary nonanalytic w(t) remains legitimate.

The same expansion of the exact c in (4) now gives

    c/q^6=-(2/3)D3+(2/3)D4-(1/2)D5
                              -(A^5/8)t^5+O(t^6).    (9)

For a transparent coefficient check, its t^3,t^4,t^5 coefficients are respectively

    A^3/12-w/2,
    A^4/4-5Aw/4,
    7A^5/16-15A^2w/8;

these agree term by term with (8),(9). Equation (9) is a source identity with the SAME arm parameters; it is not a freely chosen central coordinate.

Every ordinary connector/pad has D3=D4=D5=0, and all three differences add. Under (2), summing (9) therefore yields the order-independent necessary invariant

    sum_i c_i/q_i^6=-(S5/8)t^5+O(t^6),
    S5=1^5+6^5+10^5=107777.                           (10)

For a chronological triple define the AUXILIARY algebraic quantity

    T=c1+(r1/q2^6)c2+(r1 r2/(q2^6 q3^6))c3.           (11)

This is not the kernel of an admitted positive connector choice. It is used only to normalize the exact equations. If k_i=r_i/q_i^6=1+O(t^3), then exactly

    T/q1^6=c1/q1^6+k1 c2/q2^6+k1 k2 c3/q3^6.

Each c_i/q_i^6=O(t^3), so the extra products affect only O(t^6). Equations (10),(11) prove, for EVERY permutation,

    T=-(S5/8)t^5+O(t^6).                             (12)

No positive word is constructed with an inverted ordinary edge. In particular the algebraic normalization in (11) must not be mistaken for actual source membership.

## 4. Exact scalar reduction for the two interleaved orders

For either interleaved order set

    P=-c1>0,      Q=c2>0,      S=-c3>0,
    u=z1 q2,      v=z2 q3,
    alpha=r1/q2^6,           beta=r2/q3^6.             (13)

These alpha,beta are algebraic ratios of actual diagonals, not ordinary survivals. The physical connector constraints are EXACTLY

    0<u<q2=1-A2 t/2,      0<v<q3=1-A3 t/2.           (14)

From (6), D=0 and H=D-C=0 are

    -P+alpha u^6 Q-alpha beta u^6 v^6 S=0,
    -P(1-uv)+alpha u^6 Q(1-v)=0.                      (15)

Divide only strictly positive quantities in (15). Eliminating the common term gives

    u=(Q-beta S v^5)/(Q-beta S v^6),
    alpha (Q-beta S v^5)^6/(Q-beta S v^6)^5=P.         (16)

For sufficiently small t, Q-beta S>0, since the corresponding leading amplitude is P0>0. Thus all denominators in (16) are uniformly positive after normalization, on 0<=v<=1.

Normalize amplitudes p=P/t^3, q=Q/t^3, s=S/t^3, B=beta s. Their limits are P0,Q0,S0, with Q0=P0+S0. Define

    f_t(v)=alpha (q-B v^5)^6/(q-B v^6)^5.             (17)

The second equation of (16) is f_t(v)=p. Its exact logarithmic derivative is

    f_t'(v)/f_t(v)
       =-30Bq v^4(1-v)/[(q-Bv^5)(q-Bv^6)]<0          (18)

for 0<v<1. The limit f_0 is strictly decreasing on that interval and f_0(1)=Q0-S0=P0. Therefore any actual solutions of (16) as t->0 must have v->1; otherwise a subsequential limit v<1 would give f_0(v)>P0. The first equation then gives u->1. This derives shrinking connectors from the exact equations; no bounded hazard or near-identity connector premise has been assumed.

At v=1, equations (11)-(13) give

    f_t(1)-p=T/t^3=-(S5/8)t^2+O(t^3).                 (19)

Furthermore f_t'(1)=0 identically and

    (1/2) f_t''(1)=15 alpha Bq/(q-B)
                            ->15S0 Q0/P0>0.          (20)

The finite rational functions in (17) have uniformly bounded derivatives near one because their denominators stay away from zero. Hence (19),(20), together with f_t(v)=p, force

    (1-v)/t -> eta,
    eta^2=S5 P0/(120 S0 Q0).                          (21)

In particular 1-v=O(t); Taylor's positive limiting curvature justifies the scale, rather than a guessed connector expansion. Since the first function in (16) equals one at v=1 and has derivative beta S/(Q-beta S) there,

    (1-u)/t -> xi=(S0/P0)eta,
    xi^2=S5 S0/(120 P0 Q0).                           (22)

The strict physical constraints (14) imply the NECESSARY limiting inequalities

    xi>=A2/2,             eta>=A3/2.                  (23)

The limiting inequalities are weak: a strictly positive connector at each t may have duration o(t). No strict limiting margin is assumed.

## 5. Both possible interleavings violate actual positive admission

For order (1,10,6), P0=Psmall, S0=Plarge, Q0=Qpositive. The smaller gap is eta. The exact rational values (5) give the coarse strict bounds

    Psmall<4,     Plarge>50,     Qpositive>54,
    S5<108000.

Consequently

    eta^2=S5 Psmall/(120 Plarge Qpositive)
           <108000*4/(120*50*54)=4/3<4.              (24)

Thus eta<2, whereas (23) requires eta>=A3/2=3. No actual positive connector can solve this order.

For order (6,10,1), the amplitudes P0,S0 are swapped. Its xi^2 equals the same smaller-gap expression in (24). Hence xi<2, whereas (23) requires xi>=A2/2=5. This order also has no admitted positive solution.

Together with Section 2, this excludes ALL SIX permutations for sufficiently small positive t. The substantial margins in (24) show that allowing connectors to approach a zero-duration boundary cannot repair the failure. Connectors staying away from identity were already excluded by the exact monotone scalar reduction, rather than silently omitted.

## 6. Exterior calibration, original observations and the exact scope

For ANY positive leading/trailing ordinary survivals zeta,u_out, the original quotient composition gives

    C_full=zeta^6 u_out C,
    H_full=zeta^6[H+(1-u_out)C].                       (25)

Thus C_full=H_full=0 implies the body C=H=0; padding cannot escape the obstruction. If the pair survival is to be ONE fixed a in (0,1), its genuine calibration must have zeta=a/(q_body u_out) in (0,1), with duration -log zeta>0. The theorem excludes the joint response even without imposing that additional fixed-a constraint, so it excludes every admissible such calibration as well. No negative population, source inverse or zero-duration realizing edge is used.

C/H belong to the original complete four-root quotient reconstructed by authorized topology tomography. Matching the ordinary no-merger diagonals through five is compatible with actual sources but does not imply that quotient equality. No hidden routes, latent forest access, sampled calendar or independent cross-arity fits are added.

This decides this particular near-identity THREE-cell ordinary-return architecture with exact 1:6:10 ratios, for all orders and all positive connector/pad choices. The fifth diagonal is attainable, but its simultaneous full four-root response is not. Other mean ratios, more cells, other inheritance weights and other original admitted architectures remain open. Prescribed padded factors P_epsilon,R_epsilon generally have NONZERO C/H; their two separate source-membership equations are not the zero-response equations analyzed here. Their concatenation would have six cells, outside this three-cell theorem. Therefore no general factor nonmembership or full G4 conclusion follows.

Original G4 still requires actual finite positive inequivalent exact rivals after every full legal finite prefix of ONE fixed target, or full-rival forcing with effective detectable stopping. The fixed q,r budget, all higher forest grades, arbitrary core/menu completeness and unknown rival size remain controlling dependencies. No compiler theorem or historical novelty claim is made.

Attribution: original current-root routing, quotient composition and tomography retain their inherited contributors. Dot supplied the original exact cap-four source polynomials; Cloud's prior coefficient/moment proofs are linked. The source identity (9), all-order normalized scalar analysis and positive-gap obstruction are this packet's hand-derived contribution. Classical finite Taylor expansion and rational monotonicity are used; no original controls were rerun.
