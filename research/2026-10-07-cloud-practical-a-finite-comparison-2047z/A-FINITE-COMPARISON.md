# Finite A/rAB comparison using an explicit auxiliary positive-source rectangle

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. The root lane proposed aligning the two endpoints at a common T/R; this lane derives the endpoint costs and a truncated-profile comparison. **Hand-derived candidate; independent review pending.** No arithmetic job, scan, provider call, observation replay, sampling, inverse run or compiler occurred. Whole original-D useful precision and all-nine normalized widths at most 1/20 remain open.

This extends the [earlier A/rAB component](../2026-10-07-cloud-practical-a-conditioning-2038z/A-ERROR-CONDITIONING.md). Its exact residuals and partials remain valid; its sufficient whole-D componentwise determinant gap was proved impossible. The finite argument below uses neither that gap nor an inverse-Jacobian path in mean space. The inherited [two-stage Jacobian/profile](../2026-10-05-dot-msci-joint-jacobian-contractor-1257z/THEOREM.md) and exact identifiability retain their attribution. Level-set calculus and conservative finite bounds are established methods; this is a source-specific application, not a claimed new general inverse principle.

## Original endpoints and the auxiliary comparison domain

The two ENDPOINTS remain in original D: h,u,v in [1/32,1/8], all five rates in [1/2,6], and g in [1/6,2/3]. Write A_i=h_i+u_i, T_i=h_i+u_i+v_i, d_i=rAB_i, R_i=rR_i, c=8/3 and Delta=value0−value1. The [frozen original pair source](../2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 `c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`, gives, for z=kc, k=1,2,

    B_z=exp(−zT)*R/(R+z),
    M_z(A,d;T,R)=exp(−zA)*d/(d+z)*(1−exp(−(d+z)(T−A)))
                    +exp(−d(T−A))*B_z,
    f_k=(1+M_(kc))/2=(mu_ABk−g*mu_ACk)/(1−g).

The exact original-source residual is

    E_k=Delta mu_ABk−g0*Delta mu_ACk
           +(g0−g1)*(mu_ABk1−mu_ACk1)/(1−g1),
    Delta f_k=E_k/(1−g0).                       (1)

Choose T*=max(T0,T1) and R*=R0. The auxiliary endpoints are f_ki*=f_k(A_i,d_i;T*,R*). Both satisfy T*−A_i≥v_i≥1/32. Every A between the two endpoints therefore satisfies that lower duration bound, while

    A in [1/16,1/4], T*≤3/8,
    L=T*−A in [1/32,5/16], d,R in [1/2,6].     (2)

The larger duration 5/16 is an AUXILIARY analytic comparison range. It changes neither original D nor the admitted observation/source architecture. The auxiliary expressions need not be full sources in original D; all bounds used on them are proved below from their positive two-stage formulas. No original v≤1/8 bound or provider acceptance is presumed there.

## Endpoint lifting with signed shared nuisance costs

Direct differentiation of the positive two-stage expression, also on (2), gives

    tau_z=partial_T f_z
          =(z/2)*exp(−d(T−A)−zT)*(d−R)/(R+z),
    zeta_z=partial_R f_z
          =(z/2)*exp(−d(T−A)−zT)/(R+z)^2 >0.

Move each endpoint's T_i up to T* at fixed R_i, then move endpoint 1's R1 to R0 at T*. These paths stay in (2). Define the signed exact costs

    C_ik^T=integral_(T_i)^(T*) tau_(kc)(A_i,d_i;t,R_i)dt,
    C_1k^R=integral_(R1)^(R0) zeta_(kc)(A1,d1;T*,r)dr,
    e_k*=f_k0*−f_k1*
          =E_k/(1−g0)+C_0k^T−C_1k^T−C_1k^R.   (3)

Endpoint 0 has no rate-lifting cost. At least one time-lifting cost is zero. Hence the total time length is |Delta T|, with no factor two.

On the entire auxiliary range, exp(−dL−zT)≤1 and |d−R|≤11/2. Therefore new auxiliary fallback constants are

    |tau_c|≤44/19,       |tau_(2c)|≤88/35,
    zeta_c≤48/361,       zeta_(2c)≤96/1225.

Write these as t_k and r_k. Then

    |e_k*|≤|E_k|/(1−g0)+t_k*|Delta T|+r_k*|Delta R|. (4)

The signed identity (3) should be enclosed before magnitudes when possible. This preserves actual AB/AC/g and T/R dependence; (4) is only a scalar fallback.

## New derivative and profile bounds on the auxiliary range

At fixed T*,R*, let S(t) be 1 before A, exp(−d(t−A)) on [A,T*], and exp(−dL−R*(t−T*)) afterward. For t≥A put v(t)=min(t,T*)−A. Define

    A_z=integral_A^infinity exp(−zt)*S(t)dt,
    V_z=integral_A^infinity exp(−zt)*v(t)*S(t)dt,
    p_z:=−partial_A f_z=zd*A_z/2>0,
    q_z:=partial_d f_z=z*V_z/2>0,
    D_stage=p_(2c)*q_c−p_c*q_(2c)>0.

The inherited strict sign proof applies to every positive A<T*,d,R*. For a NEW quantitative bound, choose ell=1/32, which fits before T* at every auxiliary point. The ordered integral identity gives

    D_stage=(c^2*d/2)*integral_(A≤s<t)
       S(s)S(t)*(v(t)−v(s))*exp(−c(t+2s))
                              *(1−exp(−c(t−s))) ds dt.

Restrict to s in [A,A+ell/4] and t in [A+3ell/4,A+ell]. The area is ell²/16, v(t)−v(s)≥ell/2, S(s)S(t)≥exp(−2d*ell), exp(−c(t+2s))≥exp(−3c(A+ell)), and

    1−exp(−c(t−s))≥(c*ell/2)*exp(−c*ell/2).

Consequently

    D_stage≥c^3*d*ell^4/128
                *exp(−3c(A+ell)−(2d+c/2)*ell).

Using A≤1/4,d≤6,d≥1/2, the exponent is at most 8/3<3. Thus e<3 yields the explicit auxiliary bound

    D_stage>1/(2^19*3^6).                       (5)

Restricting to the first minimum-length window, rather than all L≤5/16, avoids a much larger exponent. No old original-D determinant constant is reused.

Since v(t)≤L and S(t)≤1, q_c≤L*exp(−cA)/2≤5/32. Along a constant-f_1 profile, implicit differentiation gives

    d'(A)=p_c/q_c,
    −d f_2/dA=D_stage/q_c >beta0,
    beta0=1/(5*2^14*3^6).                       (6)

Two other bounds will keep the profile construction finite. On the first ell after A, S(t)=exp(−d(t−A)). Hence

    p_(2c)≥c*d_min*ell*exp(−2c*A_max−(2c+d_max)*ell)
              =(1/24)*exp(−27/16)>1/216>beta0,
    q_c≥c*ell²/4*exp(−c*A_max−(c+d_max)*ell)
              =(1/1536)*exp(−15/16)>1/4608.

Finally p_c≤d/2≤3. The common positive integral weight gives

    q_(2c)/q_c=2*V_(2c)/V_c≤2*exp(−cA)≤2.     (7)

All constants (5)–(7) were derived for the auxiliary range. Equal rates need no exception.

## A bounded profile comparison between any two auxiliary endpoints

Relabel the endpoints for this proof so A0≥A1; absolute bounds are unchanged. If A0=A1 the A bound is immediate. Write m_i=f_1(A_i,d_i;T*,R*).

If d0≤d1, increasing A and decreasing d both decrease f_2. A horizontal then vertical path stays in the endpoint rectangle and gives

    −e_2*≥(1/216)*(A0−A1)>beta0*(A0−A1)

for A0>A1. Now suppose d0>d1.

If m0≥m1, for EVERY A in [A1,A0] the level m1 lies between f_1(A,d1) and f_1(A,d0). Continuity and q_c>0 give a unique smooth profile d(A) in [d1,d0], starting at d1 and ending at some d_hat≤d0. Follow that constant-f_1 profile to A0, then increase d_hat to d0 at fixed A0. The profile decreases f_2 by at least beta0*(A0−A1). The final rate segment increases f_1 by exactly e_1*=m0−m1 and increases f_2 by at most 2*e_1*, using (7). Therefore

    beta0*(A0−A1)≤−e_2*+2*e_1*.               (8)

If m0<m1, f_1(A1,d0)>m1 and f_1(A0,d0)<m1. Strict onset monotonicity gives a unique A_x in (A1,A0) with f_1(A_x,d0)=m1. Follow the level m1 only from A1 to A_x; its rates stay in [d1,d0]. Then hold d0 and move A_x to A0. The first segment decreases f_2 with slope at least beta0, and the second with slope at least 1/216>beta0. Thus

    beta0*(A0−A1)≤−e_2*.                       (9)

This truncated construction is the rate-range guard: no hypothetical profile rate below d1 or above d0 is used. It avoids the previous gap about applying compact physical constants to an unbounded profile. Every derivative is evaluated at a positive auxiliary source within the explicitly proved range (2).

The three cases imply the finite GLOBAL auxiliary fallback

    |Delta A|≤beta0^(-1)*(|e_2*|+2*|e_1*|).     (10)

For the oriented proof a stronger one-sided version is beta0*Delta A≤−e_2*+2*max(e_1*,0). With narrower certified profile/rate-segment derivative ranges, retain the exact integral signs and slopes from (8)–(9), rather than independent marginal maxima.

To recover d, swap only d at the fixed auxiliary A0,T*,R*. The entire swap stays between the endpoint rates. The q_c lower bound and a separate A segment give

    |Delta d|≤4608*(|e_1*|+3*|Delta A|).         (11)

This uses the first-moment difference and an already bounded A; it does not feed a d estimate back into the A proof.

## Scope of the new finite gate

Equations (3), (10) and (11) apply to ANY two original endpoints after the proved auxiliary alignment. The earlier failed whole-D entrywise-gap certificate is not needed. The reciprocal A constant `5*2^14*3^6` is deliberately coarse; this note establishes a finite comparison, not useful precision on current data. Complete certified narrower endpoint/auxiliary ranges can refine the ordered-window, profile, rate and lifting bounds, but must include every stated comparison path. No cell was evaluated, contracted or discarded.

The earlier [noncircular dependency graph](../2026-10-07-cloud-practical-a-conditioning-2038z/A-ERROR-CONDITIONING.md) still applies: original AC bounds feed T/R, CC1 feeds rC, BC ratio feeds h, the tied-C residual feeds g, and this finite AB block feeds A/d before AA1. Original u/v errors are Delta u=Delta A−Delta h and Delta v=Delta T−Delta A; their normalized widths divide by 3/32, while d divides by 11/2. These shared signed differences should be preserved. A itself is not an original accuracy coordinate.

Still missing: useful admitted joint mean-error control, quantitative composition across all nine original coordinates including tied rB, complete source/uncertainty coverage and actual exported union widths at most 1/20. No new confidence event or sampling plan is introduced; archived-record admission and retrospective confidence remain unverified. This is one HAND finite-source gate, not closure of the original practical solver.
