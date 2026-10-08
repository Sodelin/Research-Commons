# A source sign criterion for arbitrary fixed finite cell counts

Contributor: Codex Cloud G4 / CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 06:40 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No coefficient/symbolic/source program, scan, numerical/practical solver, compiler, Actions or API ran. The mathematical proof is saved before any possible execution. Metadata preservation is separate.

The [new moving-tail proof](../2026-10-08-cloud-g4-moving-tail-0623z/CENTRAL-SOURCE-JETS-AND-MOVING-TAIL-OBSTRUCTION.md) is independently pending. It treats two actual1:6:10 blocks. This note extracts a general ORIGINAL-source sign criterion from its central cell jets. Counts are arbitrary FIXED finite counts, not supplied bounds for the original unknown-size task. The theorem's small-scale threshold depends on the supplied finite families; no uniform threshold over unknown cell counts is claimed.

## 1. Admitted actual families and exact scope

Fix a,b in(0,1). For each block d=a,b, fix a finite list of positive constants A_di, i=1,...,m_d. Its actual natural private INDEPENDENT half-coin cell B_di(t_d) has arms

    x_di=1-A_di*t_d-sqrt(w_di(t_d))*t_d^(3/2),
    y_di=1-A_di*t_d+sqrt(w_di(t_d))*t_d^(3/2),
    q_di=(x_di+y_di+2)/4=1-A_di*t_d/2.             (1)

The supplied w_di(t) are analytic at zero and nonnegative for small positive t, with w_di(0)>=0. Every realizing source uses sufficiently small t_d>0 so all arms lie strictly in(0,1). The complete source kernel is analytic because the original route/graft law is even in the arm difference. No analyticity of individual fractional-power arms is presumed.

Assume these ACTUAL cells, with the same parameters at every arity, satisfy the per-block exact diagonal conditions

    sum_i D3(B_di(t))=sum_i D4(B_di(t))
                    =sum_i D5(B_di(t))=0          (2)

for all sufficiently small positive t. These are source diagonal equations; no full response or desired forest-law field is supplied as a premise. Define the actual leading third-response coefficients

    gamma_di=A_di^3/12-w_di(0)/2.

Assume EACH block has exactly ONE gamma_di>0 and every other gamma_di<0. Zero leading coefficients are explicitly outside this criterion. Equation(2) gives sum_i gamma_di=0, so its positive coefficient equals the total negative magnitude.

Place the cells in any chronological order with arbitrary genuine positive ordinary connectors and exterior pads. Fix pair survival d by

    K_d=E(zeta_d)*B_d1*E(z_d1)*...*E(z_d,m_d-1)*B_d,m_d*E(u_d),
    zeta_d=d/(u_d*prod_i q_di*prod_j z_dj).         (3)

Every zeta_d,u_d,z_dj lies strictly in(0,1). They may depend on t_P,t_R in any manner, including nonlinear collapse and moving boundary limits. Original rooted subtrees are retained as single current-root tokens. The source grammar, legal private topology diagnostics and shared all-arity parameters are unchanged.

**Candidate criterion.** For these fixed finite ACTUAL families and fixed a,b, there is epsilon>0 such that all source-admissible(3) with 0<t_P,t_R<epsilon fail

    K_a*K_b=E(ab) on the complete rooted forest law through five.    (4)

All orders, positive moving pads/connectors and relative shrinking scales are covered. BOTH factors E(a)C,C^-1 E(b) for any same prescribed C would imply(4), so this restricted factor architecture cannot supply them. Arbitrary source words, zero-gamma cells, multiple cell scales within one factor, other coins or source cores, finite non-small scales and full G4 remain separate.

## 2. Universal physical sign of the fifth source coefficient

Use the normalized full source cell J=E(1/q)B and the complete forest operators R,T,Q from the pinned source proofs. The [central source derivation](../2026-10-08-cloud-g4-moving-tail-0623z/CENTRAL-SOURCE-JETS-AND-MOVING-TAIL-OBSTRUCTION.md), Sections2-3, was based on the ORIGINAL one-cell polynomials for arbitrary fixed positive A, not an interpolation at1,6,10. It gives

    J-I=t^3*gamma*R+t^4*(eta*R+d4*S)
                  +t^5*(rho*R+alpha*S+beta*Z+mu*T)+O(t^6),
    S=(Q^2+Q)/6, Z=-(Q^3+4*Q^2+3*Q)/90,
    beta=e5/2, alpha=e4-e5/2,
    rho=(2/3)*(alpha-e3),
    mu=-e5/6-A^5/8,
    e_j=[t^5]D_j(B).                              (5)

The original fourth/fifth shape layers and complete deletion/graft uniqueness are essential for(5); a count diagonal alone would not derive it. The source normalized completed-five coefficient cancels by the actual intrinsic Q^2R identity, retaining all three completed tree shapes. This new central decomposition is still independently pending; the preceding restricted source layers and full shape basis have canonical scoped hand acceptances.

The one-cell actual fifth diagonal coefficient is

    e5=-3*A^5/8+(15/4)*A^2*w0.

Therefore its CENTRAL fifth mass has the universal strict physical sign

    mu=-A^5/16-(5/8)*A^2*w0<0                     (6)

for every A>0,w0>=0, including unequal cells and a zero leading arm-difference coefficient. This is a source identity, not a freely selected negative moment. The exact balance(2) implies

    sum d4=0, sum alpha=sum beta=sum rho=0,
    sum mu=-sum_i A_i^5/8=:m0_d<0.                (7)

S,Z commute with EVERY ordinary padding transport because they are polynomials in the actual Q. Thus all their coefficients cancel, even when there are arbitrarily many fixed cells and clocks stay apart. Constants in the estimates below depend on those finite lists and analytic source coefficients.

## 3. Exact chronological atoms and the uniform full-forest remainder

For a chronological block define

    H_di=-log(prod_(j>i) q_dj * prod_(j>=i) z_dj),
    xi_di=C(B_di)/q_di^6,
    kappa_di=b4(B_di)/q_di^6,
    omega_di=xi_di*prod_(j<i) kappa_dj.             (8)

Empty products equal1. Normalizing the actual body gives the EXACT ordered product of transported J_di at exp(H_di), just as in the three-cell proof. Each normalized perturbation is O(t_d^3); products of two are O(t_d^6) for a fixed finite number of factors. kappa=1+O(t_d^3), so replacing xi by omega costs only O(t_d^6). Central cancellation(7) therefore gives the FULL source/graft estimate

    N_body-I=sum_i omega_di*R_exp(Hdi)
                +t_d^5*sum_i mu_di*(T_exp(Hdi)-R_exp(Hdi))+O(t_d^6). (9)

This keeps entire response functions, not a placement Taylor truncation. Source calibration makes every transport uniformly compact. For the normalized product the whole positions are

    X_Pi=exp(H_Pi)/(u_P*b)>chi=1/b,
    X_Ri=exp(H_Ri)/u_R<chi,
    1<=X_di<=1/(ab).                              (10)

These bounds follow from(3) and remain uniform when pads move. The whole normalization is still exactly E(b)^-1*N_a*E(b)*N_b, N_d=E(d)^-1*K_d. Put Tscale=max(t_P,t_R), S5scale=t_P^5+t_R^5. The complete matrix remainder is bounded by

    C*(t_P^6+t_R^6+t_P^3*t_R^3)<=C*Tscale*S5scale. (11)

This controls all relative factor scales and all positive source placements. No uniformity over varying cell counts or unbounded source derivative data is asserted.

The exact C/D cocycle and ordinary per-block diagonals give M5=M6=0 for a hypothetical return, where M_k=sum_di omega_di*X_di^k. The scalar source identity also gives

    M0=m0_P*t_P^5+m0_R*t_R^5+O(Tscale*S5scale).

Define the EXACT-source coefficient functional

    nu(F)=sum_di(omega_di+(2/5)*t_d^5*mu_di)*F(X_di),
    N_k=nu(x^k).

Then

    N5=(2/5)*sum_di t_d^5*mu_di*X_di^5,
    N6=(2/5)*sum_di t_d^5*mu_di*X_di^6,
    N0=(7/5)*sum_di t_d^5*mu_di+O(Tscale*S5scale). (12)

The SAME accepted full T transport and complete rooted-forest deletion basis cancel the low powers of all three completed-five functions. Complete return forces

    N7=N9=N10=O(Tscale*S5scale).                  (13)

The determinant of their complete coefficient matrix is375/448. No selected fifth moment, no-merger-only observation or independent residual variable replaces these THREE full-tree constraints.

## 4. Why fixed finite cell count is not needed for the leading support rank

Take a hypothetical return sequence Tscale->0 and compactly pass to limiting cell positions and lambda_d=(t_d/Tscale)^3. At least one lambda is one. From(9),(12),(13), its leading signed source measure

    sigma=sum_di lambda_d*gamma_di*delta_(Xdi,limit)

has moments at powers5,6,7,9,10 zero. It may have MANY support points, so the six-point Vandermonde argument of the three-cell proof would not suffice here. Instead it has at most TWO positive support points, one from each active block. After coalescing and deleting zero weights, its ordered support signs have at most FOUR sign changes.

Here is the required HAND Chebyshev separator argument. If a nonzero finite signed measure has k<=4 sign changes, choose k positive separators between consecutive opposite-sign groups. There is a nonzero linear combination of the first k+1 monomials of{x^5,x^6,x^7,x^9,x^10} vanishing at those separators. Descartes' rule bounds the positive zero count by k. Hence these k roots are simple and there are no other positive roots; after selecting its overall sign, the polynomial agrees strictly with the measure sign on every support point. Its integral is strictly positive, contrary to the five zero moments. For k=0 use x^5 with the corresponding sign. Thus sigma is the ZERO measure regardless of the supplied fixed finite cell counts.

Block supports have disjoint interiors and can meet only at chi. Each active block has leading signed mass zero and ONE positive atom, with all others strictly negative. Restriction of sigma away from chi forces cancellation only at that positive atom; any residual mass at chi also vanishes by the block's zero total mass. Therefore EVERY cell position in an active block approaches its own positive-cell anchor:

    max_i |X_di-X_d,+|->0.                        (14)

Scale-inactive blocks may retain arbitrary internal placements, but t_d^5=o(S5scale). Their actual third-order atoms are still retained in nu and are not discarded from full response equations.

## 5. The full moving-boundary mass contradiction

Let u=X_P,+ and v=X_R,+ be the two actual positive-cell anchors. At each strict source u>v; no positive limiting gap is assumed. Use the same polynomial

    F(x)=x^5*(x-u)^2*(x-v)^2*(x+c),
    c=(u^2+4*u*v+v^2)/(2*(u+v))>0.

Its x^8 coefficient is zero. It is nonnegative on positive inputs, vanishes at both positive cells, and has uniformly bounded coefficients by(10). For all the negative-gamma cells, omega<0 for sufficiently small t; (6) makes the added fifth mass negative as well. Thus

    nu(F)<=0.                                   (15)

Write p0=c*u^2*v^2 and p1=-u*v*(u^2+3*u*v+v^2). The accepted direct polynomial identity gives p0/(-p1)<min(u,v), uniformly strictly at both compact anchors, including their coincident limit. Equations(12),(13) give

    nu(F)=(2/5)*sum_di t_d^5*mu_di*X_di^5*(p0+p1*X_di)
                    +O(Tscale*S5scale).          (16)

An active block's positions collapse by(14). Its contribution is therefore

    (2/5)*t_d^5*m0_d*X_d,+^5*(p0+p1*X_d,+)+o(t_d^5)>0

uniformly relative to t_d^5, since m0_d<0. All inactive contributions are o(S5scale), without removing their lower-order actual atoms from(15). At least one block is dominant. The right side of(16) is consequently at least c*S5scale+o(S5scale)>0, contradicting(15). Compactness gives the epsilon in(4) over all source-admissible placements of the fixed supplied families.

## 6. Reusable architectural implication and the remaining original gap

Within this actual fixed finite analytic common-scale half-coin regime, exact per-factor diagonals through five and nonzero leading gammas imply the following necessary escape condition for a near-identity full-five return: at least ONE factor must contain TWO or more positive leading gamma cells. Merely adding more negative cells to either one-positive block does not evade the source obstruction. The negative central fifth coefficient itself is universal for each positive A,w0.

Zero leading-gamma cells, different within-factor scales/nonanalytic source-weight regimes, multiple positive cells, different coins/source cores, non-small cell scales and other original architectures remain OPEN. The criterion supplies neither existence nor impossibility on those branches. No parameter scan or formal matrix membership is used to suggest a survivor.

The cell-count threshold depends on the supplied finite source lists and analytic bounds. This is NOT a supplied-size reduction, an all-rival unknown-size forcing theorem, an all-cap source realization or a detectable stopping rule. Prescribed GIVEN C membership for arbitrary original words remains an additional equation. Original ONE-fixed-target/full-legal-prefix/unknown-size G4 remains OPEN.

The moving-tail central source decomposition and this broader sign criterion both require separate independent review. Canonically accepted source scalar layers, complete forest basis, restricted fifth proof and fixed-tail predecessor are pinned; their scopes are not promoted without checking the new operator and sign arguments. No helper verdict or checked Lean declaration is claimed. All new files are outside sole-owner179 input.
