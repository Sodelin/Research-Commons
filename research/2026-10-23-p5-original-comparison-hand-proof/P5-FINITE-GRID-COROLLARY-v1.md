# A completely finite real-parameter witness grid

21 October 2026. Conditional HAND corollary of the explicit I13 assembly
in P5-INTERPOLATION-AND-ADMISSION-v1.md, SHA256
963c61d9c337cd8dc099a19cd2aec5c57b22f7bd30e78f31b88fd562aa9bb753.
It adds finite grids for observation time and physical bath modulation
to the already finite r/u grids. It is not an executed witness search,
independent proof acceptance or a new model/compiler job.

## The elementary grid lemma

Let p have degree at most n>=1 on a real interval[a,b] and let
J_g=8n^3. At the grid x_j=a+(b-a)j/J_g, j=0,...,J_g,

    max_j|p(x_j)| >=(3/4)max_(x in[a,b])|p(x)|.     (G1)

Indeed I2 after interval rescaling gives
||p'||<=(4n^3/(b-a))||p||. A maximizing point has a grid point within
(b-a)/(2J_g). Integrating p' along that real segment changes its value
by at most(2n^3/J_g)||p||=||p||/4. This also holds for complex p.
Endpoint maxima cause no issue because the endpoints belong to the grid.

## The actual physical grid and lower bound

Retain ALL notation and conditional supplier premises of I1-I15. In
particular rho_N is the one predeclared POSITIVE initial density based
on t_N, and n=N^2. Use the finite sets

 R_N_grid={r_N/2+j r_N/(2m_r): j=0,...,m_r},
 U_N_grid={1+j/m_u: j=0,...,m_u},
 T_N_grid={t_N j/J_g: j=0,...,J_g},
 V_N_grid={-1+2j/J_g: j=0,...,J_g}.

Here m_r=ceil(N^(1/4)), m_u=ceil(sqrt(N)/sqrt(log N)) and J_g=8N^6.
Every tuple is REAL and fully admitted: r>0, u in[1,2], v in[-1,1],
s in[0,t_N], the SAME original static H_r and all physical bath channels.
Neither u=0 nor a complex parameter is a grid member.

Let G_N,theta_min,eps_t,eps'_t,eps_u,D_N,eps_v be exactly those in
the I13 source. Define

 B_N_grid=[3t_N/(16n^3)](theta_min G_N-eps'_t)-eps_t,

 L_N_grid=[3/(8n^3)]
            [12^(-m_u)B_N_grid-eps_u-D_N]-eps_v.     (G2)

Then the finite maximum of ORIGINAL full-filter predictions obeys

 max_(r,u,s,v in the displayed grids)
       |Tr[rho_N exp(s R(r,u,v)*)O]| >= L_N_grid.   (G3)

To prove this, choose r_* from the already finite I4-I5 interpolation
grid. Its degree-n TIME Taylor polynomial p_t has derivative at t_N
of modulus at least theta_min G_N-eps'_t. I2 and G1 give

 max_(time grid)|p_t|
    >=[3t_N/(16n^3)](theta_min G_N-eps'_t).

Subtract eps_t. Thus some displayed time s_* has
|F(0,s_*)|>=B_N_grid. The finite u interpolation of I9-I10 then
selects u_* with

 |F(u_*,s_*)|>=12^(-m_u)B_N_grid-eps_u.

I11 transfers this to the SAME full physical first derivative with loss
D_N. Its degree-n v Taylor polynomial p_v has EXACT derivative F_full
at zero, so I2 gives ||p_v||>=|F_full|/(2n^3). Apply G1 on[-1,1] and
subtract eps_v to obtain G2-G3. The only extra losses are two fixed
factors3/4. All analytic remainders and initial states are unchanged.
If a displayed lower expression is negative the inequality is vacuous;
the asymptotic claim is for the sufficiently large N where it is positive.

Consequently the I14-I15 asymptotic remains valid:

    max_(finite physical grid)|prediction|
                 >=exp[y^2 sqrt(N)/55296]          (G4)

eventually. In particular the parameter existence does not rely on
choosing an unspecified continuous maximizer. The size of this grid is
finite and polynomial in N; evaluating its matrices remains enormously
more expensive because physical Hilbert-space dimension is exponential
in M=O(N log^3 N). No efficient algorithm is claimed.

## An exact sequence without deciding ties

For a computable witness specification fix gamma=1, a positive rational
tau in the original box and epsilon_clock=1/32. One can avoid any exact
real-ceiling decision by the following equivalent certified roundings.
For x=4096D^2[1+log(32G_cD)], compute a rational upper bound q_x with
x<=q_x<=x+1, then take d=2ceil(q_x). If d_*=2ceil(x) is the candidate's
original length, d_*<=d<=d_*+2. The C4 error E_d is decreasing for
d>=256D^2: differentiating its displayed linear prefactor times the
exponential proves this directly. Since d_*>=8192D^2, the larger length
still gives E_d<=epsilon_clock and the same hardware/runtime orders.

Similarly, a rational upper bound q_u in
[sqrt(N)/sqrt(log N),sqrt(N)/sqrt(log N)+1] gives m_u=ceil(q_u), at most
one above the original m_u. Use these chosen integers consistently in
the clock construction, I7-I13 and G2. Their proofs are unchanged: Cauchy
and interpolation apply to ANY chosen integer degree, and all asymptotic
orders and strict exponent separations stay the same. Such rational
enclosures of elementary positive functions are computable by convergent
series and bisection. For example log z=2sum_(k>=0)w^(2k+1)/(2k+1),
w=(z-1)/(z+1), after dyadic range reduction has an explicit geometric
remainder with |w|<=1/3. Thus this variant needs neither transcendence
claims nor comparisons of an unknown exact real with an integer.

For each integer B>=2 enumerate balanced-tree sizes and the finite
physical grids, dovetailing certified interval precision. Stop at the
first tuple whose ORIGINAL prediction is certified in modulus>B.
G4 guarantees a strict successful tuple at all sufficiently large sizes,
so this procedure terminates conditional on the candidate proof.
Restrict each next search to a larger tree depth to obtain an increasing
sequence of volumes for B=2,3,... . No comparison of equal maxima or
uncertified rounded density is required.

Full filters are computable by finite integration with their common
exponential envelope tail; the delayed pulse is retained until that tail
bound applies. The finite-block kappa(t_N) and positive mixture weights
are computable exact real expressions. This is the finite-grid version
of P5-FINITE-WITNESS-SELECTION-v1.md's rational-dovetail specification.
Neither version has been executed. Their termination remains conditional
on the complete mathematical suppliers and admission audit, as recorded
in P5-CANDIDATE-REVIEW-LEDGER.md.
