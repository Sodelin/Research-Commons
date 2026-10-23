# C4: the literal same-static-H clock interface

21 October 2026. A bounded HAND proof interface for review. This is not a
compiler result, acceptance of the remaining analytic suppliers or P5
closure. Its source is the COMPLETE STATIC-PARALLEL-CLOCK-FANOUT.md,
SHA256842927d32cbd03eb1bf077e5cfce199d7e20de2ccb1d7428625467e89d59ce25,
together with the embeddings in
SYMMETRIC-AMPLIFIER-AND-CLOCK-PREIMAGES.md,
SHA256ca496356d8fbd7c889976df747c1b78fa49c96a9f9f035f48813a6e623a5490b.
The thermal Gaussian replaces the earlier sech bath in the final candidate;
the static algebra below has no bath premise.

## Exact finite Hamiltonian and target

There are N=2^(q+1)-1 DATA qubits on a binary tree. List CNOT(child->parent)
in bottom-up depth order, with two disjoint rounds at each depth. Set
G_c=N-1 and let D be the number of these nonempty rounds, so
1<=D<=2ceil(log2 N). Each vertex participates in at most three gates.
Number layers l=0,...,D-1; gates in each layer have disjoint data supports.
Within a layer choose any fixed gate order. Write C=U_G...U_1.
Direct Pauli conjugation, depth by depth, gives

    C^dagger Z_root C=product_(all data) Z_i.          (S1)

Every gate involving the root has it as TARGET, so CNOT and the static
Hamiltonian terms below commute with X_root. Fix omega_0>0 and even
d>=16D. Each gate g has a SEPARATE chain of d+1 physical clock qubits,
positions j=0,...,d, initially with its single excitation at j=0.

    Delta=pi d/(4D omega_0),
    omega_l=omega_0 D/(D+l),
    a_(l,j)=(omega_l/d)sqrt((j+1)(d-j)),
    L_0=2D Delta=pi d/(2omega_0).

The FULL-qubit-space static Hermitian Hamiltonian K_0 is the sum, for
each clock bond j,j+1, of

 a_(l,j)[|01><10| tensor V_(g,j)
                         +|10><01| tensor V_(g,j)^dagger],

where V_(g,d/2)=U_g and V_(g,j)=I on every other bond. The forward hop
increases j. The norm of this term is a_(l,j)<=omega_0 and it occupies at
most four qubits. One excitation per chain is invariant under K_0.
This invariant sector is used ONLY to prove the prepared compression.
K_0 itself is defined on the complete clock Hilbert space.

For the product one-excitation clock input |c>, the literal target is

 ||<c|exp(iL_0 K_0)Z_root exp(-iL_0 K_0)|c>
                       -product_(data)Z_i|| <=2E_d,

 E_d=[pi d G_c^2+2sqrt(G_c)]exp[-d/(256D^2)].       (S2)

No approximation on arbitrary clock inputs is asserted. Choosing
d=2ceil(4096D^2 log(e G_c D/epsilon_clock)) gives E_d<=epsilon_clock.
In the candidate epsilon_clock<=1/32 and delta_c=2E_d<=1/16.

## The ordering estimate needed in the proof

Remove V from each chain and call its one-excitation Hamiltonian K_free.
It is a sum of INDEPENDENT spin-d/2 chains (2omega_l/d)J_x. Starting at
position0, the exact squared amplitudes are Binomial(d,p_l(t)), where

    p_l(t)=sin^2(omega_l t/d).

On 0<=t<=L_0 these probabilities are monotone. Their central arrival
times are t_l=(D+l)Delta. In particular the LAST layer arrives at
L_0-Delta; it does not arrive at L_0. At least Delta/2 before or after
its arrival, p is below or above1/2 by at least1/(8D). The minimum angular
margin is pi/(16D), and the elementary sine bound gives that constant.

Fix an earlier-layer gate g and a strictly later-layer gate h. Before
the midpoint of t_g,t_h, h is on the right (j_h>=d/2+1) with probability
at most exp[-d/(32D^2)]. After that midpoint, the probability that g is
at either of its central sites j_g in{d/2,d/2+1} is at most
exp[-d/(128D^2)]. The one-site offset1/d is at most1/(16D), since d>=16D.
The free clocks have independent position distributions. Thus uniformly
in t in[0,L_0],

 Pr[g central AND h right] <=exp[-d/(128D^2)].       (S3)

At L_0, each chain is left (j<=d/2) with probability at most the same
bound. These estimates are uniform in every data input; the data do not
enter K_free.

For a configuration z define x_g=1 if j_g>d/2 and zero otherwise, and

    W(z)=U_G^x_G ... U_1^x_1,
    K_id=W K_free W^dagger

on the invariant one-excitation sector. W is block diagonal and unitary;
W(c)=I. A central forward hop of clock g in K_id applies

    U_later U_g U_later^dagger,

where U_later is the ordered product of already-right gates later than g.
K_0 instead applies U_g. Gates in g's own layer commute with U_g. The
difference therefore vanishes unless at least one strictly later-layer
clock h is already right while g is central. For each pair g,h its
contribution on the ideal evolving state has norm at most

    2omega_0 sqrt(Pr[g central AND h right]).

This follows also for the reverse hop: the two central source/target
subspaces are orthogonal, and each difference of unitary gate factors
has norm at most2. A union bound on the relevant orthogonal clock
projections followed by sqrt(sum p)<=sum sqrt(p) bounds the norm by the
sum over pairs. The data-dependent W(z) preserves each position
probability. There are at most G_c^2 ordered pairs. Unitary Duhamel gives

 ||(exp(-iL_0K_0)-exp(-iL_0K_id))|c,psi>||
        <=2omega_0 L_0 G_c^2 exp[-d/(256D^2)]       (S4)

for EVERY normalized data vector psi. If all clocks are right,
W(z)=C. The union bound on a late left clock shows that the final ideal
state differs from exp(-iL_0K_free)|c> tensor C psi by at most
2sqrt(G_c)exp[-d/(256D^2)]. Combined with S4 this is the isometry error
E_d in S2. For a norm-one observable, two isometries at distance E_d have
compressions differing by at most2E_d. Applied to Z_root and S1 this
proves the literal prepared-clock target.

The deliberately conservative d choice is explicit: if
u=log(e G_c D/epsilon_clock)>=1, then d<=8194D^2u and
the prefactor of E_d is at most32778D^2uG_c^2. Use32778<exp(11),
u<=exp(u), (G_cD)^2<=epsilon_clock^2 exp(2u) and
d/(256D^2)>=32u. The resulting bound is at most
epsilon_clock^2 exp(-18u)<=epsilon_clock.

## Physical embedding, SAME H and uniform geometry

Each data or clock qubit becomes one three-physical-qubit block, with

    H_c=(J/2)(Z1X2+X2Z3), G=X1Y2X3, S=Z1,
    pi(X)=G, pi(Z)=W, pi(Y)=iGW.

The W here is the balanced local reflection from the symmetric amplifier
source, not the clock-configuration gauge W(z). Its exact defining
relations are W^2=G^2=I, GW=-WG, [H_c,W]=[H_c,G]=0. On the ROOT instead
use pi_root(X)=G, pi_root(Z)=S, pi_root(Y)=iGS. There S^2=I,
SG=-GS, and [H_c,S]=0. These are unital isometric *-embeddings of the
two-by-two matrix algebra on the COMPLETE physical block spaces. No
prepared gauge state is needed for these algebra identities.

All encoded clock terms therefore commute with H_0=sum H_c, exactly.
For EVERY real r, use the ONE static physical Hamiltonian

    H_r=H_0-r pi_all(K_0)+h_*Z_isolated.

The isolated qubit is independent. S_root commutes with H_0 and with its
term. Hence for L(r)=L_0/r and r>0 the original source convention gives

 U_(H_r)(L(r))S_root
   =exp(-iL(r)H_r)S_root exp(iL(r)H_r)
   =pi_all(exp(iL_0K_0)Z_root exp(-iL_0K_0)).       (S5)

This is a full-Hilbert-space identity; only its later base clock
functional uses the prepared compression S2. Likewise
[H_r,G_root]=0, since all root gates have the root as target. The same
H_r must be used in EVERY original Redfield filter. No effective logical
noise or deletion of physical clock noise is part of S5.

A data vertex has at most three adjacent data vertices and two central
clock sites for each incident gate: its closed logical neighborhood has
size at most10. A clock vertex has at most two clock neighbors and, only
if central, the gate's two data vertices: size at most5. The interaction
neighborhood relation is symmetric, so its multiplicity has the same
bound. Encoding each logical block in three physical sites gives

    k<=12, m<=30, nu<=30,
    h_active<=J+3|r|omega_0,
    M=N+(N-1)(d+1)=O(N log^3 N).

With 0<r<=1 and the candidate's J,omega_0 this is below h_*. The
unrelated term fixes EXACT h=h_* independently of N and r. Embedding
does not increase term norms. All physical blocks retain their full
on-site baths in the admitted model; C4 is solely a Hamiltonian and
prepared-operator lemma.

## Review boundary and next connection

These arguments have been hand-derived and finite clock/gauge/geometry
identities checked, but this C4 supplier has not received an independent
complete hand audit or formal check. The original static source's final
historical gap paragraph predates the analytic counterexample assembly;
the current open supplier list is in P5-CANDIDATE-REVIEW-LEDGER.md.

The later use is ONLY at the independent base r=0: the positive clock
preimage mixtures make their logical functional exactly |c><c| at t_N;
then S2 is contracted with the product data functional of norm A_N.
Connected actual evolution is handled separately by D3/D5 and the
analytic interpolation chain. C4 does not tensorize coupled evolution,
prove those interpolation steps or establish P5 closure.
