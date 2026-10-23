# C2: actual Gaussian amplifier and every-duration clock functional

21 October 2026. A literal HAND supplier for the analytic counterexample.
It isolates the Gaussian version of the symmetric block and the
intermediate-duration property required by D5. No independent acceptance,
formal check or new finite-control run is asserted.

## The actual complete block, with all nine channels

On three physical qubits take

 H_c=(J/2)(Z1X2+X2Z3),
 Phi(s)=(gamma*c/tau)exp[-2(s/tau)^2]exp[-is/(4tau)],
 c=exp(-1/8), y=Jtau in(0,1/288], J<=gamma.

The independent baths on sites1,2 have Phi; those on site3 have Phi/2.
Every site has ALL three bare Pauli channels. The spectrum, thermal KMS
condition, common exponential envelope and nonzero floor are derived in
GAUSSIAN-THERMAL-RESPONSE-REDUCTION.md, SHA256
d0f48bc9ef7ae94786f6fb4de60c5c5057b01002df03db94474dee392b6f996e.
In particular ||K_A||<=gamma for EVERY full filter
K_A=integral_0^infinity Phi_p(s)exp(-isH_c)Aexp(isH_c)ds.

Use the actual Heisenberg Redfield generator

 B(F)=i[H_c,F]+sum_A([A,F]K_A-K_A^dagger[A,F]).

It is unital and preserves adjoints; it is not assumed positive or
contractive. Since ||H_c||=J, a valid cb bound is

    ||B||cb<=2J+36gamma<=38gamma=:b.                (A1)

Put v=y/144 and define the EXACT physical vectors and operators

 phi_A=(iv|100>+|110>)/sqrt(1+v^2),
 phi_B=(-iv|001>+|011>)/sqrt(1+v^2),
 P=|phi_A><phi_A|+|phi_B><phi_B|
                         +|101><101|+|111><111|,
 W=I-2P, G=X1Y2X3, S=Z1,
 rho_+=|000><000|, rho_-=|111><111|.

These give W^dagger=W, W^2=I, Tr W=0, W|000>=|000>,
W|111>=-|111>, and

 [H_c,W]=[H_c,G]=[H_c,S]=[S,W]=0,
 GWG=-W, SGS=-G.                                  (A2)

For completeness H_c vanishes on the two sectors spanned by{100,110}
and{001,011}. It exchanges000,010 and exchanges101,111, on each of
which W is scalar. Explicitly

 G phi_A=(-i|001>-v|011>)/sqrt(1+v^2),
 G phi_B=(-i|100>+v|110>)/sqrt(1+v^2),
 G|101>=i|010>, G|111>=-i|000>.

The first two are orthogonal to phi_B and phi_A respectively. Thus G
maps the entire four-dimensional P range onto its orthogonal complement,
which proves GWG=-W. The other relations follow from the displayed
Pauli products and the S-invariance of each sector.

## Full-filter transition, without removing other channels

Let C1=integral_0^infinity Phi(s)cos(Js)ds,
D1=integral_0^infinity Phi(s)sin(Js)ds, r=Re C1, d1=Re D1.
Since P|000>=0, the transition under the ACTUAL Schroedinger adjoint is

 Tr[P B_*(rho_+)]=sum_A 2Re <A000|P K_A|000>.       (A3)

The Hamiltonian contribution vanishes since[H_c,P]=0. The two
anticommutator terms vanish because P|000>=0. A channel with P A|000>=0
contributes zero even if P K_A|000> is nonzero. Thus only X1,Y1,X3,Y3
can contribute to this transition; no channel is omitted from B itself.

Here are the literal vectors needed for those four terms, before the
site3 scaling1/2 is applied:

 K_X1|000>=C1|100>+iD1|110>,
 K_Y1|000>=iC1|100>-D1|110>,
 K_X3|000>=C1|001>+iD1|011>,
 K_Y3|000>=iC1|001>-D1|011>.

For example exp(isH_c)|000>=cos(Js)|000>+i sin(Js)|010>,
while H_c vanishes on the first-flipped sector; this gives the first
two FULL integral vectors. Their P overlaps yield a combined
4(rv^2-d1*v)/(1+v^2). The last two give the opposite sign and their
site3 strength alpha=1/2. Hence

 Tr[P B_*(rho_+)]
   =4[(1+alpha)r v^2-(1-alpha)d1*v]/(1+v^2)
   =-a.                                           (A4)

The full Gaussian moments give r<=gamma and

 integral_0^infinity s Re Phi(s)ds
   >=gamma*c*tau(1/4-1/256)
   >=(441/2048)gamma*tau,
 integral_0^infinity s^3|Phi(s)|ds<=gamma*tau^3/8.

The first follows from cos(z/4)>=1-z^2/32 and c>=7/8. The ABSOLUTE
sine remainder bounds the sign-changing tail correctly, giving

 d1>=gamma*y[441/2048-y^2/48]>=gamma*y/24.

Consequently

 a>=gamma*y^2/[3456(1+y^2/20736)]
   >=a0=gamma*y^2/6912>0.                          (A5)

The bath asymmetry is essential: alpha=1 would cancel the linear d1*v
term. All physical channels remain strictly present at alpha=1/2.

## Monotonicity for every required duration

Define the ACTUAL base expectation

    kappa(s)=Tr[rho_+ exp(sB)W].

Unitality and A4 give kappa(0)=1, kappa'(0)=2a>=2a0.
For s>=0 the finite-dimensional exponential and A1 give

 |kappa'(s)-kappa'(0)|<=b(exp(bs)-1).

For0<=s<=t_*=a0/(2b^2), bs<=log2. Therefore
exp(bs)-1<=bs exp(bs)<=2bs and the last bound is at most2b^2s<=a0.
The expectation is real, since B preserves adjoints. Thus throughout
this WHOLE interval

    kappa'(s)>=a0,
    1+a0s<=kappa(s)<=exp(bs).                       (A6)

This supplies monotonicity; a positive derivative only at s=0 would not
have sufficed for the clock argument. Fix ANY t in(0,t_*].

## Physical Pauli covariance and restricted logical representatives

Let pi be the unital *-embedding determined by

    pi(X)=G, pi(Z)=W, pi(Y)=iGW, pi(I)=I.

A2 gives the exact Pauli algebra, with two four-dimensional logical
eigenspaces. Neither pi's existence nor the following calculation
requires B to preserve pi(M_2).

Conjugation by G or S sends each bare physical Pauli A to its sign
epsilon_A times A. Because it commutes with H_c, it sends K_A to the
SAME sign times K_A. The signs cancel in every Redfield channel.
Thus B and exp(sB) commute with those two Pauli conjugations, even with
the unequal site bath strengths. Both rho_+ and rho_- are S-invariant;
pi(X),pi(Y) are S-odd, so their actual expectations vanish for all s.
G maps rho_+ to rho_- and sends W to-W. Their restricted logical
functionals therefore have the exact density representatives

 D_+(s)=diag((1+kappa(s))/2,(1-kappa(s))/2),
 D_-(s)=diag((1-kappa(s))/2,(1+kappa(s))/2).         (A7)

For0<=s<=t these have trace norm kappa(s)<=kappa(t). They need not be
positive, and that failure is precisely the amplifier. The PHYSICAL
INITIAL rho_+,rho_- are positive normalized states.

## Positive clock preimages, with norm one at ALL intermediate times

Set w=(kappa(t)+1)/(2kappa(t)) and prepare the POSITIVE initial mixtures

 rho_clock,0=w rho_+ +(1-w)rho_-,
 rho_clock,1=(1-w)rho_+ +w rho_-.

Since kappa(t)>=1, these are convex normalized mixtures. At EVERY
duration0<=s<=t their logical X,Y expectations are zero and Z is
plus or minus kappa(s)/kappa(t). A6 puts that number in[-1,1]. Thus
each restricted functional is POSITIVE of norm EXACTLY1 at every
duration, and at s=t it is exactly the desired pure logical bit.

The later D5 use takes a partial contraction at a post-probe duration
between0 and t. It uses these EVERY-duration logical norm-one suppliers,
not positivity of the full physical evolved clock or merely its final
pure logical value. The mixtures are fixed from t while the observation
time may vary. They are never redefined inside interpolation.

For N data blocks with one separately treated root and t=N^(-1/2)/gamma,
the non-root product norm is A=kappa(t)^(N-1). For sufficiently large N,
log(1+a0t)>=a0t/2 and N-1>=N/2, so

 y^2 sqrt(N)/27648<=log A<=38sqrt(N).               (A8)

All statements here concern the exact independent BASE functional.
The connected actual dynamics remains subject to D3/D5, physical C4,
the cutoff transfer and the analytic assembly. No coupled propagator has
been tensorized. Separate independent acceptance of this actual C2
supplier and the remaining assembly is still pending.
