# A code-functional Dyson bound for weak local interactions

21 October 2026. Authored mathematical proof candidate, self-reviewed.
This is not an actual online Lean check or an independent acceptance.
Its intended application and remaining audit are in
P5-STATIC-CLOCK-ANALYTIC-COUNTEREXAMPLE-v1.md.

## Finite tensor-product setting

Physical block i has a finite matrix algebra B_i, a unital *-embedding
pi_i of a logical matrix algebra C_i, and a positive normalized initial
functional rho_i. Let B=sum_i B_i^0 be a sum of block generators, each
annihilating I. On all ordinary blocks assume

    ||B_i^0||_cb <= b.

At the selected real time t, suppose the actual base functionals restricted
to their logical algebras obey, for EVERY 0<=s<=t,

    ||rho_i exp(s B_i^0) pi_i|| <= a_i,    a_i>=1.       (D1)

These functionals need not be positive. A distinguished finite set of
root blocks can instead be included in the touched set throughout and
bounded by exp(b_root t). Write A=product_(ordinary i) a_i. All norms of
functionals here are matrix functional norms, equivalently trace norms of
their density representatives. A scalar-valued matrix functional has
completely bounded norm equal to its norm. Tensor products of those
functionals have the product norm.

Let V=sum_Z V_Z, where V_Z acts only on physical blocks Z. The decomposition
can be finite or absolutely summable in the following weighted cb norm:

    W_t(V)=sum_Z exp(b t |Z outside root|) ||V_Z||_cb.   (D2)

Let rho be the product initial functional. For any logical Q,

    |rho exp(t(B+V)) pi_all(Q)|
       <= A exp(b_root t) ||Q|| exp[t W_t(V)].         (D3)

It is enough for (D3) alone to assume (D1) only at s=t. The intermediate
times in (D1) are needed for the one-insertion variant below.

## Proof of (D3): retain exactly which blocks were touched

Expand exp(t(B+V)) in its time-ordered Dyson series around B. Fix a term
with n specified insertions V_(Z_1),...,V_(Z_n), and let S contain the
root and the union of their supports. No insertion touches any block
outside S. Its full base evolution there can therefore be moved past all
insertions and contracted against rho_i. Applied to the logical input Q,
these untouched contractions have cb norm at most
product_(i outside S) a_i. Their partial contraction leaves a logical
operator on S of norm at most that product times ||Q||.

On S use the PHYSICAL cb norm of every base segment and every insertion.
The durations of the base segments sum to t, giving the bound

    A ||Q|| exp(b_root t) exp(b t |S outside root|)
          product_j ||V_(Z_j)||_cb.

The replacement of the untouched product by A is valid because a_i>=1.
Since |S outside root|<=sum_j |Z_j outside root|, this is bounded by
A||Q||exp(b_root t) times the product of the weighted terms in (D2).
Sum the supports and integrate the n-simplex, of volume t^n/n!.
Summing n proves (D3). The same absolute estimate justifies an absolutely
summable interaction decomposition and limits of its partial sums.

No actual propagator contraction, positivity, invariant logical algebra
under B, or tensorization after adding V was used. Only the untouched
BASE blocks were contracted using their actual restricted functionals.
The touched blocks were estimated in their full physical algebras.

## A single global logical probe applied to a local observable

Let O be supported on the designated root. Consider a probe superoperator
P consisting of a fixed finite sum of elementary left/right products
whose non-root factors are GLOBAL logical operators. More explicitly the
Redfield probe used here is

    P(F)=[A_root,F] Q - Q_sharp [A_root,F],            (D4)

with A_root local, ||A_root||<=1, and Q,Q_sharp in pi_all(C_all).
For real physical parameters Q_sharp=Q^dagger; their complex analytic
continuations are kept separately. Put

    p=2(||Q||+||Q_sharp||).

Define the single-probe response

    F(t)=d/dv rho exp(t(B+V+v P)) O |_(v=0).

Under (D1),

    |F(t)| <= p ||O|| t A exp(b_root t+t W_t(V)).     (D5)

To prove this, expand in V and retain exactly ONE P. Fix the V supports
and include the root in their union S. Before P, the observable outside S
is I: O is local, B annihilates I, and no V insertion touches those blocks.
The four terms in (D4) insert one global logical Q or Q_sharp, multiplied
on either side by operators on S. On each untouched block, its base
duration AFTER P lies between 0 and t. Thus its contraction has norm at
most a_i by (D1). Partially contract that ONE global logical factor first;
its norm is at most its original norm times the product of the untouched
a_i. Everything remaining is a physical map on S and is bounded just as
in (D3). There are n+1 positions for P among n V insertions. Their ordered
time integrals total (n+1)t^(n+1)/(n+1)!=t^(n+1)/n!.
Summing gives (D5).

This argument permits base dynamics to leave the logical algebra and
permits arbitrary entanglement of the logical input. It would NOT apply
unchanged to several global probes: then an untouched block could carry
a genuine multi-time logical correlation rather than the ONE restricted
functional in (D1). The application below needs only the first derivative.

## Uniform weak-link interaction estimate for the P5 auxiliary

Use three-qubit blocks, H_0=sum_i H_(c,i), and the logical static clock
Hamiltonian K_0=sum_Z K_Z from STATIC-PARALLEL-CLOCK-FANOUT.md, at frequency
omega_0. Each K_Z occupies at most four blocks. Its block incidence is
at most eta_0=3omega_0. Every encoded K_Z commutes with H_0.
The physical Hamiltonian is H_r=H_0-r K_0. Let M be its number of blocks.
Scale the root's nine unshifted bath channels by u, and all other bath
channels as in the Gaussian amplifier. Allow r,u to be complex only for
analytic estimates; the physical family later uses real parameters.

For each channel A define an auxiliary filter by its FULL base filter plus
the truncated SAME-H increment:

    K_tilde(A;r)=K(A;0)
       +integral_0^S Phi(s)[U_(H_r)(s)A-U_(H_0)(s)A]ds.  (D6)

For complex r use the analytic exponential commutator extension, and
define the sharp filter with conjugate scalar covariance but the SAME
complex r. Do not conjugate r or u in that extension. On the real axis
these sharp filters are precisely the adjoints needed by Redfield.
Let R_tilde(r,u)=B(u)+V(r,u) include the SAME i[H_r,.].

For b=38gamma, bt sufficiently small, gamma*tau<=1 and

    6 eta_0 |r| S exp(3bt) <= 1/2,

there is a numerical constant C, independent of M,r,u,S,t, such that

    W_t(V(r,u)) <= C eta_0 |r| (M+1+|u|).             (D7)

Here B(u) has the independent full-filter generators. Its root cb norm
is at most 2J+36gamma|u|. All ordinary block norms are at most 38gamma.
Only the root channel sum carries |u|; it must not be multiplied by M.

For completeness, expand the increment in nested K_Z commutators.
Starting from one block, after n insertions its support has at most
1+3n blocks. The summed product of the interaction norms over overlapping
sequences is bounded by

    eta_0^n product_(j=0)^(n-1)(1+3j) <= (3eta_0)^n n!.

Including commutator factors 2^n and the exponential's 1/n!, the summed
norm at order n is at most (6eta_0 |r| s)^n. Base conjugation by H_0 is a
product of unitary conjugations and preserves both support and norm;
commutation of K_0 and H_0 licenses this expansion without an extensive
||H_0|| factor. Weighting supports multiplies order n by at most
exp[bt(1+3n)]. Under the displayed smallness condition the geometric sum
for n>=1 is bounded by a constant times eta_0 |r|s. Integration uses

    integral_0^S s|Phi(s)|ds <= gamma*tau.

Each resulting Redfield elementary map has cb norm at most four times
the filter term's norm. There are nine channels per block, with an extra
factor |u| only for the nine root channels. The Hamiltonian difference
has weighted norm at most 2|r|sum_Z exp(bt|Z|)||K_Z||.
These estimates prove (D7), with constants that can be enlarged uniformly
when gamma*tau<=1. The series is absolutely summable in (D2).

## A bounded analytic global probe

Let A be the bare root Z1, which commutes with H_0. Let L_0 be the virtual
clock runtime and Y_0=exp(iL_0 K_0) A exp(-iL_0 K_0). This is a GLOBAL
logical Hermitian unitary. Define

    Q_r=(1/2)integral_(-S)^S Phi_G(v)
                  exp(irvK_0) Y_0 exp(-irvK_0)dv.     (D8)

Because conjugation by exp(iL_0K_0) commutes with the short-time
conjugation in (D8), the latter can first be applied to the LOCAL A.
The same nested-commutator estimate, with no support weights, gives

    ||Q_r||,||Q_r_sharp|| <= 2gamma

when 6eta_0 |r|S<=1/2. This holds on a complex r disk, uniformly in M.
The long REAL unitary conjugation exp(iL_0K_0) preserves this norm.
Bounding the complex conjugation of the already global Y_0 by ||K_0||
would lose this locality and give an unusable volume factor.

At r=0,

    Q_0=b_S gamma Y_0,
    b_S gamma=(1/2)integral_(-S)^S Phi_G(v)dv.

Hermitian covariance symmetry makes b_S real. As S/tau tends to infinity,
b_S tends to the positive b_G from the Gaussian source, so b_S>=b_G/2
eventually. The analytic sharp version at r=0 is the same Q_0.

This completes the stated finite-dimensional bounds. Their use in an
original-generator counterexample is a separate assembly and is not
asserted merely by the presence of this source.
