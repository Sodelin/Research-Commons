# An admitted local balanced amplifier that commutes with its Hamiltonian

21 October 2026. Self-reviewed hand-proof candidate, with finite executed
controls recorded in PROGRESS.md. This is a growing-support amplifier
supplier, NOT a fixed-X P5 counterexample, static root-reachability theorem,
independent review, formal verification or historical novelty claim.

## Original physical model

On THREE qubits take the two commuting Pauli interaction terms

    H_c=(J/2)(Z1 X2 + X2 Z3),  0<J<=b_* gamma,
    b_*=pi/(4sqrt(2)),  gamma tau<=1/288.

The ORIGINAL operator incidence is h=J. Both neighborhoods and their
multiplicity have common bounds m=nu=3; k=2. Thus these are exactly the
original P5 inequalities for this fixed geometry. Every qubit has all
three independent thermal channels, with the same full covariance

    Phi(s)=gamma/(2sqrt(2)tau) sech(s/tau+i pi/4),

and every filter uses this SAME H_c and integrates to infinity. No qubit
is a noiseless auxiliary, and qubit 3 now participates in H_c.

Let y=J tau<=1/288, v=y/48, psi=|000>,

    phi=(iv|100>+|110>)/sqrt(1+v^2),
    P_minus=|phi><phi|+|101><101|+|011><011|+|111><111|,
    W_c=I-2P_minus.

Exactly W_c^dagger=W_c, W_c^2=I, Tr W_c=0, ||W_c||=1 and W_c psi=psi.
The projector's matrix entries are rational functions of y.

## Exact zero energy commutator

H_c=J X2(Z1+Z3)/2 vanishes when the first and third Z signs differ.
Consequently it vanishes on span{|100>,|110>} and span{|001>,|011>}.
It swaps |000> with |010> inside W_c's plus space and |101> with |111>
inside W_c's minus space. Therefore

    [H_c,W_c]=0                                       (1)

for every v. This is not an approximate small-y statement.

Equivalently H_c=(H_old+W_0 H_old W_0)/2 for H_old=J Z1 X2 and the
three-bit majority reflection W_0 from AMPLIFIER-TIME-AND-GAIN.md. The
projection onto its even part removed the earlier extensive commutator
while leaving an actual nonpositive transition below.

## Keep every original full filter

Write

    k0=integral_0^infinity Phi(s)ds,
    C1=integral_0^infinity Phi(s)cos(Js)ds,
    D1=integral_0^infinity Phi(s)sin(Js)ds,
    C2=integral_0^infinity Phi(s)cos(2Js)ds,
    D2=integral_0^infinity Phi(s)sin(2Js)ds,
    P1=Z1 X2, P2=X2 Z3.

P1 and P2 commute. For a bare Pauli A:

- if it commutes with both, K_A=k0 A;
- if it anticommutes with just P_l, K_A=C1 A+i D1 A P_l;
- if it anticommutes with both,

    K_A=((k0+C2)/2)A
       +(i D2/2)A(P1+P2)-((k0-C2)/2)A P1 P2.         (2)

These are exact expansions of the two commuting unitary rotations. In
particular K_X1=C1 X1+D1 Y1 X2 and K_Y1=C1 Y1-D1 X1 X2. Equation (2)
also retains the Y2/Z2 filters, rather than silently omitting their noise.

Set r=Re C1 and d=Re D1. Only the X1 and Y1 bare channels have nonzero
P_minus A psi. The full transition rule from the earlier witness therefore
gives EXACTLY

    Tr[P_minus R_c(|psi><psi|)]
      =4(rv^2-dv)/(1+v^2)=-a_c.                      (3)

Every other channel's transition is zero because P_minus A psi=0, whatever
its complete filter in (2). The Hamiltonian term is also zero. Hence

    <psi|R_c* W_c|psi>=2a_c.                          (4)

## Explicit physical lower bound

The retained thermal family has Re Phi(s)>0 and
Re Phi(s)>=gamma/(11tau) for 0<=s<=tau. Thus

    integral_0^infinity s Re Phi(s)ds>=gamma tau/22.

The envelope gives the third absolute moment <=6gamma tau^3. Using
sin z>=z-z^3/6 for z>=0 now at frequency J, rather than 2J, yields

    d>=gamma y(1/22-y^2)>=gamma y/24.                 (5)

The final inequality holds for y<=1/288. Also r<=gamma directly from the
ORIGINAL envelope. Since v=y/48, (3) implies

    a_c=4(dv-rv^2)/(1+v^2)
      >=gamma y^2/[576(1+y^2/2304)]
      >=gamma y^2/1152=:a0_c>0.                      (6)

No quadrature or unspecified smallness threshold is used in (5)-(6).
If desired, r>=b_* gamma-gamma y^2>0 follows from 1-cos z<=z^2/2, but
positivity of r is not needed in the denominator of this explicit profile.

All nine filters satisfy ||K_A||<=gamma, and ||H_c||=J<gamma, so
||R_c*||_(infinity->infinity)<=38gamma. The SAME fixed-block Taylor
argument as before gives the explicit physical time and gain

    t_c=y^2/(1663488 gamma),
    <psi|exp(t_c R_c*)W_c|psi>
      >=1+y^4/1916338176.                             (7)

For N independent blocks, all at the SAME t_c,

    [H_ref,W_c^tensor N]=0,
    ||exp(t_c R_ref*) W_c^tensor N||op
      >=(1+y^4/1916338176)^N.                         (8)

This is an explicit tensor PRODUCT of balanced reflections, not a nonlocal
functional-calculus dilation or a time-averaged contraction. Each local
profile has zero energy commutator. All 9N physical channels remain.

## A growing amplifier matching a bare root's entire energy-derivative budget

There is an even closer candidate profile for a future reached-family
construction. Take B=Z2 on the first block and put

    G_N=B tensor W_c^tensor(N-1).

This is still a traceless Hermitian unitary of norm one. Because every
other block's W_c commutes with its H_c, for EVERY integer r>=0,

    ad_(H_ref)^r(G_N)
      =ad_(H_c)^r(B) tensor W_c^tensor(N-1),
    ||ad_(H_ref)^r(G_N)||op=||ad_(H_c)^r(B)||op.        (9)

Thus it matches the norm of EVERY Hamiltonian energy derivative of the
BARE on-site root Pauli B, not only a volume-independent first commutator.
This is a reference-H compatibility statement, not static reachability.

Since <psi|B|psi>=1 and ||exp(tR_c*)-id||<=exp(38gamma t)-1, the physical
t_c in (7) gives <psi|exp(t_c R_c*)B|psi>>1/2. For example
38gamma t_c=y^2/43776<1/4 and exp(1/4)<3/2 suffice. Exact independent
block tensorization therefore proves

    ||exp(t_c R_ref*)G_N||op
      >=(1/2)(1+y^4/1916338176)^(N-1).                (10)

Its support still grows. Equations (9)-(10) show concretely that even
control of ALL these energy-commutator norms alone cannot provide a
general uniform actual-response bound on arbitrary global observables.
A valid positive proof must use fixed initial support or more of the
actual reached family. A negative proof must still realize that family
with one admitted static connected H and retain its actual filters.

The root insertion also has the right literal Redfield algebra. If the
ROOT channel is A_root=Z2, O_X=X2 and a REAL filter difference were c G_N,
its exact generator contribution would be

    [A_root,O_X](cG_N)-(cG_N)[A_root,O_X]
      =-4c X2 tensor W_c^tensor(N-1).                 (11)

The output has the amplifying outer-block profile and only a fixed root
factor. This is a conditional algebra identity, NOT a claim that an actual
source filter has that form. Actual static reachability, integration of
the delayed covariance, propagated remainders and the full comparison
still have to be established. No independently tensorized reference may
be substituted after adding the required connected Hamiltonian.

## Exact reachability gap remains

The extensive-J commutator obstruction in
STATIC-ENERGY-BANDWIDTH-OBSTRUCTION.md applies to the earlier H_old product
profile with weak links. It does NOT apply to H_c and (8). The new model
shows concretely why that obstruction cannot be generalized to every
physical amplifier or used alone to prove uniform actual response.

However, under the independent H_ref a bare root orbit stays within its
own block. Adding connecting terms changes both the original full filters
and the actual propagation. The FULL new static H must obey
||[H,U_L A_root]||=||[H,A_root]||, not merely commute with H_ref. No such
same-H fixed-root construction or original-comparator lower bound has been
supplied. The source family even lies inside the accepted commuting branch;
the GROWING initial support in (8) makes that entirely consistent.

The decisive next task is an energy-compatible SAME STATIC connected
reached family with controlled actual response, or a different full-class
positive comparison proof. Balanced spectrum, a local gate circuit,
zero reference-energy commutator and tensor amplification are useful
suppliers, but still insufficient to close P5.
