# A thermal symmetric amplifier and positive clock preimages

21 October 2026. Self-reviewed hand proof, with finite exact controls
reported separately in PROGRESS.md. This is a bounded supplier for the
same-H clock route. It is not connected finite-time amplification, static
root reachability or P5 closure.

## Original admitted model, with every physical channel present

Keep H_c=(J/2)(Z1 X2+X2 Z3), h=J, k=2, m=nu=3. Let

    Phi_*(s)=gamma/(2sqrt(2)tau) sech(s/tau+i pi/4),
    b_*=pi/(4sqrt(2)), beta=pi tau/2,
    b0=b_*/2, 0<J<=b0 gamma, gamma tau<=1/288.

All three channels on sites 1 and 2 have Phi_*. All three channels on site
3 have (1/2)Phi_*. Positive scaling preserves positive type, the SAME
KMS temperature beta and covariance symmetry. The common ORIGINAL
envelope remains gamma/tau exp(-|s|/tau); the smallest floor is b0 gamma.
All nine channels are strictly present. Their full filters use this H_c.

Set y=J tau, v=y/144, psi_+=|000>, psi_-=|111> and

    phi_A=(iv|100>+|110>)/sqrt(1+v^2),
    phi_B=(-iv|001>+|011>)/sqrt(1+v^2),
    P_-=|phi_A><phi_A|+|phi_B><phi_B|
                              +|101><101|+|111><111|,
    W=I-2P_-,            G=X1 Y2 X3,           S=Z1.

Exactly W is a balanced Hermitian unitary, W psi_+=psi_+,
W psi_-=-psi_-, and

    [H_c,W]=[H_c,G]=[H_c,S]=[S,W]=0,
    G W G=-W,            S G S=-G.                    (1)

For example H_c vanishes on both rotated two-dimensional sectors. G
interchanges them and reverses the majority reflection; the two opposite
rotation angles in phi_A and phi_B preserve that reversal.

## Actual full-filter transition and an explicit physical time

Let C1=integral_0^infinity Phi_*(s)cos(Js)ds and
D1=integral_0^infinity Phi_*(s)sin(Js)ds, with r=Re C1, d=Re D1.
The complete filters, including those that anticommute with both commuting
Hamiltonian terms, are still exactly the expansions (2) in
ENERGY-COMMUTING-LOCAL-AMPLIFIER.md, with a factor 1/2 on site 3.
No filter or channel is removed by using the following transition rule.

Only X1,Y1,X3,Y3 have P_- A psi_+ nonzero. First-site contributions are
4(rv^2-dv)/(1+v^2) in total, while third-site contributions are
4 alpha(rv^2+dv)/(1+v^2), with alpha=1/2. Consequently

    Tr[P_- R_c(|psi_+><psi_+|)]
      =4[(1+alpha)rv^2-(1-alpha)dv]/(1+v^2)=-a.      (2)

The earlier thermal moment proof gives r<=gamma and
d>=gamma y(1/22-y^2)>=gamma y/24 for y<=1/288. Thus

    a>=gamma y^2/[3456(1+y^2/20736)]
      >=gamma y^2/6912=:a0>0.                       (3)

Equal bath strengths alpha=1 would cancel the useful linear d term and
would NOT establish this amplifier. The unequal admitted strengths are
essential here. They do not break the covariance used next: conjugation
by a physical Pauli string only changes each channel's sign, not its site.

Every filter has norm <=gamma and ||H_c||=J<gamma, so the conservative
bound ||R_c^*||<=38gamma still holds. The same explicit Taylor remainder
argument, with t_s=a0/(38gamma)^2, yields

    t_s=y^2/(9980928 gamma),
    kappa=<psi_+|exp(t_s R_c^*)W|psi_+>
      >=1+y^4/68988174336>1.                        (4)

Indeed the linear term is >=2a0 t_s and the remainder is at most
(38gamma)^2 t_s^2, since exp(38gamma t_s)<2. There is no quadrature or
unquantified small-time limit in this lower bound.

## Exact Pauli covariances, not a logical-noise assumption

Both G and S are physical Pauli strings commuting with H_c. For any bare
channel A, conjugation sends A to epsilon_A A and its SAME-H full filter
to epsilon_A K_A. These signs cancel in each Redfield channel, so R_c^*
and its exponential commute exactly with conjugation by G and S, even
with the unequal bath strengths.

Define an embedding pi of the logical two-by-two algebra by

    pi(X)=G,       pi(Z)=W,       pi(Y)=i G W,       pi(I)=I.

Equation (1) gives exactly the Pauli algebra and pi is a unital
*-embedding. All pi observables commute with H_c. Since each logical
eigenspace has dimension four, this is a fixed logical-qubit/gauge
decomposition inside the three physical qubits.

The initial densities rho_+=|000><000| and rho_-=|111><111| are invariant
under conjugation by S. pi(X),pi(Y) change sign under S, so their actual
expectations at every time are zero. Conjugation by G maps rho_+ to rho_-
and changes the sign of pi(Z). At the EXACT physical time t_s, their
restricted logical functionals therefore have density representatives

    D_+=diag(1+p,-p),       D_-=diag(-p,1+p),
    p=(kappa-1)/2>=y^4/137976348672>0.              (5)

These are Hermitian trace-one REPRESENTATIVES; they are not positive
logical states. The PHYSICAL INITIAL densities rho_+,rho_- are positive.

## Positive physical inputs with pure logical clock output at one time

Let

    w=(1+p)/(1+2p)=(kappa+1)/(2kappa),
    rho_clock,0=w rho_+ +(1-w)rho_-,
    rho_clock,1=(1-w)rho_+ +w rho_-.

Both initial physical clock densities are positive, normalized mixtures.
Linearity and (5) show EXACTLY, for every logical matrix Q,

    Tr[rho_clock,c exp(t_s R_c^*)pi(Q)]=<c|Q|c>,
                  c=0 or 1.                       (6)

Thus a prescribed pure logical clock functional at this ONE time can be
obtained with an allowed positive physical initial density and all nine
thermal noise channels. No claim of a noiseless clock trajectory is made.
The mixture depends on the exact finite-block kappa; this is a legitimate
specified initial density, not an independently assumed inverse-positive
channel or a postselection step.

For INDEPENDENT base blocks, put these mixtures on clock blocks and rho_+
on n data blocks. The full actual base functional on ANY encoded logical
operator Q is exactly

    Tr_data[D_+^tensor n <c|Q|c>_clock].             (7)

Hence, at this base-functional level, an operator-norm statement about the
prepared clock compression IS sufficient. If that compression approximates
Z^tensor n with norm error <=delta, its expectation is at least

    (1-delta)(1+2p)^n.                              (8)

The arbitrary-clock-state obstruction in the previous encoding note is
not being treated as a universal no-go: it applied to putting the
indefinite amplifier witness on every clock as well as on the data.
Equation (6) supplies a different allowed clock initial density.

## Exact remaining gap

An arbitrary fixed-locality static logical K can be embedded with this pi,
exactly as in the earlier encoding note. On a distinguished root block
one may use pi_root(Z)=Z1, pi_root(X)=G and pi_root(Y)=iGZ1 instead,
so the root Z is a bare one-site physical channel. Then, on the COMPLETE
Hilbert space,

    U_phys(s) Z1_root=pi_all[exp(-isK)Z_root exp(isK)]. (9)

If K has block incidence eta and logical neighborhoods M,nu_L, the same
physical bounds h<=J+eta, k<=max(2,3r), m<=3M, nu<=3nu_L hold.
For any bare channel, the ACTUAL full filter differs from its independent
base by <=2gamma eta tau. These are same-H Hamiltonian/filter suppliers,
not a replacement of the actual physical noise by a logical channel.

This reduction retains fixed-dimensional, fully noisy physical blocks and
the same base Hamiltonian, so it removes the proposed unavoidable clock
damping/complement penalty at the INDEPENDENT reference-functional level.
It does not make the independent base generator the actual generator of
a connected clock/computation Hamiltonian.

Embedding a logical static K using this pi still changes the actual full
filters and physical-time response. A fast prepared-sector static root
flow, its bounded physical incidence, a connected actual-response control,
the delayed-filter error and the ORIGINAL-comparator lower bound remain
to be proved together. No tensorized response, inverse-positive full
evolution, constant-time static fanout or P5 counterexample follows from
(6)-(8). General P5 remains OPEN.
