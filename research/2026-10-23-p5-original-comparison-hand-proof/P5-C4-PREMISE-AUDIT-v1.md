# Quantitative free-clock and full-space embedding premises

21 October 2026. Self-reviewed HAND completion of the PREMISES left
outside LEAN-P5-C4-GAUGE-ISOMETRY-09's bounded agreement. That return
conditionally agrees with the gauge/isometry/S5 argument; it does not
independently accept the probability constants or all block algebra.
This note is not a new independent review, test run, compiler job or
request for a further P5 proof lane.

The pinned C4 interface is P5-STATIC-CLOCK-C4-INTERFACE-v1.md, SHA256
7198285e1e2c621f66a758a11903a8dfd02be6d8c51d24b20fbaa6d30eb778c2.
Its underlying static source is842927d32cbd03eb1bf077e5cfce199d7e20de2ccb1d7428625467e89d59ce25.

## Exact distribution, derived on a finite representation

The free one-excitation chain has basis|j>, j=0,...,d, and matrix element
(omega_l/d)sqrt((j+1)(d-j)) between j and j+1. On the symmetric subspace
of d mathematical spin halves, the sum of their X operators has exactly
the matrix element sqrt((j+1)(d-j)): count the zero spins that can be
flipped between the normalized weight-j and weight-(j+1) sums.
Thus the two finite matrices are unitarily identical. These mathematical
spins are a representation, not new physical clock sites.

Starting at|0>, its evolution is therefore the symmetric tensor power
of cos(theta)|0>-i sin(theta)|1>, theta=omega_l t/d. The EXACT position
distribution is Binomial(d,p_l(t)), p_l(t)=sin^2(theta). With
omega_l=omega_0 D/(D+l), l=0,...,D-1, and
L_0=pi d/(2omega_0), every angle on[0,L_0] lies in[0,pi/2], so p_l
is monotone. Its central arrival is t_l=(D+l)Delta,
Delta=pi d/(4D omega_0). The last arrival is L_0-Delta.

## Tail constants with both central endpoints

For a Bernoulli variable X with parameter p, the centered log moment
generating function f(lambda)=log(1-p+p exp(lambda))-p lambda has
f(0)=f'(0)=0 and f''(lambda)=q(1-q)<=1/4, where
q=p exp(lambda)/(1-p+p exp(lambda)). Integrating this bound in either
direction gives f(lambda)<=lambda^2/8. Independence of d such variables
and exponential Markov, optimized at lambda=4a or-4a, give

 Pr[J/d-p>=a], Pr[J/d-p<=-a] <=exp(-2d a^2).        (P1)

The deterministic cases p=0,1 satisfy the same inequalities directly.

At distance at least Delta/2 from arrival, the angular distance a_theta
from pi/4 is at least pi/(16D), since omega_l>=omega_0/2. It lies in
[0,pi/4]. Concavity of sine gives sin(2a_theta)>=4a_theta/pi, hence

 |p_l(t)-1/2| >=1/(8D),                            (P2)

with the sign determined by before/after arrival. For strictly ordered
layers g before h, their arrival separation is at least Delta. Split
time at their arrival midpoint. Before it, h's right event J_h>=d/2+1
requires an upper fluctuation of at least1/(8D), so its probability is
at most exp[-d/(32D^2)]. After it, g's TWO central sites are contained
in J_g<=d/2+1. Because d>=16D,

 p_g-(1/2+1/d)>=1/(8D)-1/d>=1/(16D),

so the probability of that event is at most exp[-d/(128D^2)]. Free
clock positions are independent, and in each half of the interval the
other event has probability at most1. Thus at EVERY time

 Pr[g in{d/2,d/2+1} AND h right]
                             <=exp[-d/(128D^2)].   (P3)

At time L_0 every arrival is at least Delta earlier. Apply P2 and P1 to
the event J_l<=d/2; its probability is at most exp[-d/(32D^2)], also
bounded by the weaker P3 constant. These are precisely the two estimates
used by the audited gauge/isometry proof. No coupled noisy-clock
probability law is being substituted for these FREE-clock identities.

The stated epsilon_clock choice follows from the elementary E_d bound
already displayed in C4. With u=log(e G_c D/epsilon_clock)>=1,
8192D^2u<=d<=8194D^2u and the prefactor is at most32778D^2uG_c^2.
Then E_d<=epsilon_clock^2 exp(-18u)<=epsilon_clock, as in the interface.

## Exact physical embedding, including its norm

The Gaussian C2 source gives the physical balanced W, G and S with
W^2=G^2=S^2=I, GW=-WG, SG=-GS, and each of W,G,S commuting with H_c.
On a non-root block choose an orthonormal basis e_1,...,e_4 of W=+1;
the vectors G e_1,...,G e_4 are an orthonormal basis of W=-1. The
identification|0,j>->e_j, |1,j>->G e_j makes W=Z tensor I_4 and
G=X tensor I_4. Thus pi(Q) is EXACTLY a unitary copy of Q tensor I_4,
not a restriction to a code subspace. It is a unital *-embedding and
||pi(Q)||=||Q||. At the root the SAME construction uses S instead of W.
All statements hold on the COMPLETE eight-dimensional physical blocks.

The algebra premises themselves are explicitly derived in
P5-GAUSSIAN-AMPLIFIER-C2-v1.md, SHA256
10b7507cf809a22348b9b5ac82eabd1c868b9de76ec7b25074366339a0ff3f54.
In particular G maps phi_A to a vector orthogonal to phi_B, and phi_B
to a vector orthogonal to phi_A, exchanging the full negative and
positive W eigenspaces. No assertion G phi_A proportional phi_B is used.

Tensoring these exact block identifications makes the entire pi_all
isometric. Since H_c commutes with the logical X and Z, every encoded
logical operator commutes with H_0's block term. Finite matrix power
series give pi_all(exp K)=exp(pi_all K). Each static clock term therefore
keeps its norm, support on at most four blocks, and exact H_0 commutation.
No assumption of base Redfield code invariance follows or is needed.

## One isolated term, one common Hamiltonian

To remove a notation ambiguity across the sources, define ONCE

 H_blocks=sum_b H_(c,b), H_iso=h_*Z_isolated,
 H_total,0=H_blocks+H_iso,
 H_r=H_total,0-r pi_all(K_0).                       (P4)

C4 writes H_0=H_blocks and lists H_iso separately. T1 and W2 include
H_iso in their H_0. In the I13 premise, "H_0 plus the independent
incidence-fixing qubit" means H_blocks plus ONE H_iso. These are aliases
for P4, never a second copy of H_iso. D6's reference U_(H_0) is U_(H_total,0).
The isolated channels retain their full filters; their increments are
identically zero. Their observable factor is I and their generator is
unital, so they contribute exactly1 to the root expectation. Their real
onsite Pauli term fixes the exact original h=h_*, once.

With P4, [H_total,0,pi_all(K_0)]=0 and [H_total,0,S_root]=0 give S5
with its PLUS iL_0 pi_all(K_0) sign, exactly as the peer audited.
Every physical filter and every physical evolution uses this SAME H_r.
The prepared-clock sector enters only the independent-base compression.

The neighborhood/incidence counts in C4 are unchanged: at most10 logical
blocks in a data closed neighborhood and5 at a clock, hence k<=12,
m<=30,nu<=30 after the three-site encoding. Active h<=J+3r omega_0<h_*.
An unrelated single-qubit neighborhood adds no larger bound. The
logical-clock error and the physical-generator error remain distinct.

This supplies a complete self-reviewed proof of these C4 premises.
Independent acceptance still has exactly the conditional scope of the
peer's actual return; writing this note is not an additional peer audit
or full P5 closure. The analytic and original-prediction assembly is a
separate source obligation, not implied by prepared clock reachability.
