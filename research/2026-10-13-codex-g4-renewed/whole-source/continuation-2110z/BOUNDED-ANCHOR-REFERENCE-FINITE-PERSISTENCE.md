# Finite persistence from the actual bounded-anchor reference comb

Contributor: Codex delegated laplace_recovery researcher, 13 October 2026.
Publisher: Codex lead G4 researcher. **Hand-derived synthesis; independent
review pending.** Its conclusion is conditional on the displayed exact
law-level scalar identity. It is not a finite legal observation certificate
and does not close the original G4 master. Hand proofs, computation and
formal verification remain distinct; no new computation or Lean proof is
asserted here.

## 1. The scalar theorem and what it quantifies over

For each side X in {T,R}, take one finite opened rooted ordinary meeting
tree with at most two A ports and at most two B ports, one shared A routing
coin and one shared B routing coin. Edge population lengths are finite and
nonnegative. Routing coins may lie in [0,1] for this auxiliary theorem;
zero-probability routes are removed first. All parameters stay fixed across
arities. Let v_X(n) be its actual reference-comb probability for n distinct
A inputs and one B input, and let

    C_X(n)=v_X(n)/kappa_(n+1).

The reference comb first merges B with a_1, then attaches a_2,...,a_n.
Ordinary populations above the meeting are completed by the inherited
infinite ordinary completion. Let each side also have finitely many private
cell factors, with finite nonnegative arms and coins in [0,1], and a finite
ordinary clock A_X. Deterministic coins reduce to ordinary factors; cells
with both arms zero are identities.

Suppose, for every integer n>=0, the exact scalar identity holds:

    exp(-A_T lambda_n) product_(r finite) d_n(a_r,b_r,g_r) C_T(n)
      =exp(-A_R lambda_n) product_(r finite) d_n(a'_r,b'_r,g'_r) C_R(n)
                       product_(i in I) d_n(t_i,t_i,g_i),         (1)

where every t_i>0, every g_i is interior, and sum_i t_i<infinity. The family
I may initially be finite or countable. The products are defined by the
usual no-merger bounds. No source-size bound is assumed.

**Theorem.** Under (1), I is finite.

Only the analytic finite-persistence implication is asserted. The
[anchor theorem](../continuation-1900z/ANCHOR-AND-MEETING-INVARIANT.md)
supplies the bounded meeting representation and the exact finite-source
reference factorization in its stated source setting. Producing (1) for a
particular compactified limit must still respect that supplier's one-source
contract and the countable-clock compactification. A finite observed prefix
alone is not asserted to imply (1) in this theorem.

The allowance for zero lengths and endpoint coins is for auxiliary limits.
Actual original targets and rivals retain their strict admission rules.

## 2. Complete classification of one-B components by the A backbone

With one B input, its routing coin gives a positive mixture of at most two
ordinary selected B-port trees. Suppress its unused port, but retain the
same A routing coin and the same original edge lengths. There is no merger
on a population occupied only by that one B root.

If only one A route survives, every selected component is simply an
ordinary no-A-merger factor exp(-L lambda_n): all n A roots must survive to
their first common population with B, after which the topology law is the
ordinary completion. This case has no phase variable.

Suppose two A routes survive. Let V be the lowest common ancestor of A_0
and A_1 in the opened ordinary tree, and let L_0,L_1>=0 be their full arm
lengths to V. Any common A passage below the routing split is an ordinary
factor shared by all B components and can be absorbed into A_X.
There are precisely two types of selected B placement:

* If B first meets an A arm below V, say arm i, let T>=0 be the length
  from that first meeting to V. Then 0<=T<=L_i. The component is the mixed
  three-tip tree with arm lengths (L_i-T,L_(1-i)), internal length T,
  and the inherited routing coin, relabelled if necessary. There is no
  common A-only pad above the A join before B enters.
* If B joins at V or above it, the component is the private-cell diagonal
  d_n(L_0,L_1,g), followed by an ordinary no-A-merger pad of length L>=0
  from V to its first meeting with B. Its value is
  exp(-L lambda_n)d_n(L_0,L_1,g).

These assertions follow by restricting the rooted ordinary tree to the
three selected tip ports. Populations above their common meeting do not
alter the completed topology law. Zero lengths allow equality of meeting
vertices but do not add a third placement type. This backbone argument
covers all four-tip colour shapes and all port relabellings, including
mixed balanced and either mixed caterpillar placement. It avoids assuming
that the two B components have unrelated arm parameters.

## 3. Component rates and the endpoint/strict separation

For a,b>0 put

    c(a,b)=ab/[2(a+b)],
    ell_cell=2c+H(alpha)+alpha log(g)+(1-alpha)log(1-g),
    ell_mixed=2c+2H(alpha)+alpha log(g)+(1-alpha)log(1-g),
    alpha=b/(a+b).

A strict private cell has exact normalized factor F_cell with asymptotic
order n^(-1/2). A strict mixed component with T>0 has F_mix of order n^(-2).
Both have positive, uniformly bounded-away-from-zero leading phase
coefficients. The mixed component at T=0 is exactly the private cell,
with its cell rate; no interchange of an infinite spectral sum at T=0 is
used. An ordinary pad of length L adds L/2 to the quadratic rate and L/2
to the linear rate, because exp(-L lambda_n)=exp(-Ln^2/2+Ln/2).

The endpoint components are phase-free:

| Component | Quadratic rate before a common pad | Linear factor | Remaining multiplier |
|---|---:|---|---|
| One zero arm, private cell | 0 | probability of choosing the zero arm to the power n | reviewed zero-type endpoint E |
| One zero arm, mixed T>0 | 0 | probability of choosing the zero arm to the power n | E_early or E_late |
| Both arms zero, mixed T>0 | 0 | (1+2sqrt(g(1-g)))^n | Jacobi/semicircle E |
| Both arms zero, T=0 | 0 | 1 | 1 |
| One surviving A route | L/2 | exp(Ln/2) | 1 |

Every E in this table is holomorphic of zero exponential type on the right
half-plane, positive at nonnegative integers, has log E(n)=o(n), and is
meromorphic globally with finite-order poles. Their proofs are linked in
Section 8. No inverse-density expansion is claimed for endpoint E.

The following homogeneity fact is essential.

**Least-quadratic homogeneity.** After removing a common A ordinary factor,
the least-quadratic B-component class consists entirely of strict-arm
analytic factors, or entirely of phase-free endpoint factors.

Proof. If L_0,L_1>0, every sister component has strict arms and positive
quadratic rate c(L_0,L_1)+L/2. A mixed component is either strict, with
positive c, or has one zero reduced arm, with c=0. If an endpoint mixed
component exists, it strictly precedes every strict component in quadratic
rate. If none exists, all components are strict. If one of L_0,L_1 is zero,
every mixed component retains a zero arm, and every sister component has
a zero-arm private factor. Thus all components are phase-free; their
ordinary pads may change their quadratic rates but cannot create a strict
component. The one-A-route case was already phase-free. QED.

In particular, a zero-arm sister component with a positive ordinary pad
cannot secretly tie a strict mixed component: the zero full A arm also
appears in the mixed component. This rules out the additive endpoint/strict
coefficient gap that a purely numerical comparison of arbitrary rates
would leave open.

## 4. The actual core rate and resource normalization

Each core is a finite positive mixture of the components above. Write c_X
for its least quadratic rate and ell_X for the largest linear rate among
that least class. Then

    log C_X(n)=-c_X n^2+ell_X n+o(n).                  (2)

For a strict least class, its finitely many normalized terms have positive
uniform leading phase coefficients and polynomial orders n^(-1/2) or
n^(-2). Among a tied largest linear class, the smallest algebraic order
has a positive leading coefficient. Higher linear and quadratic classes
cannot cancel it because the original component probabilities are positive.
This gives an O(log n) remainder in (2). For an endpoint least class,
normalize each term by its known linear exponential. The remainder is
positive and subexponential, with a lower bound of polynomial order for at
least one leading term, so the logarithmic remainder is o(n). Higher
quadratic terms have logarithm -delta n^2+O(n)+o(n) relative to the leading
class. All asymptotics are for fixed component parameters; no uniformity
as T tends to zero is required.

Private finite factors have the same quadratic-plus-linear-plus-o(n)
form. Apply the inherited resource proof to (1), retaining (2) in its
finite logarithmic side. In detail set

    phi_i(n)=log[exp(lambda_n t_i)d_n(t_i,t_i,g_i)],
    psi_i(n)=t_i n^2/4-phi_i(n),
    b_i=log cosh(h_i/2), h_i=logit(g_i).

The inherited bounds are

    0<=phi_i(n)<=t_i n^2/4,  phi_i(n)/n^2 ->t_i/4,
    0<=psi_i(n)/n<=b_i+t_i/4,  psi_i(n)/n ->b_i.

Taking logs in (1) gives sum phi_i(n)=r_2 n^2+r_1 n+o(n).
Dominated convergence at the quadratic scale yields r_2=sum t_i/4.
Subtracting this term and applying nonnegative Fatou at the linear scale
gives sum b_i<infinity. The now-summable upper bound then permits linear
dominated convergence and exact linear matching. In particular

    sum_i h_i^2<infinity.                              (3)

Thus the inherited equal-arm product P(z)=product_i U(z;t_i,h_i) is a real
holomorphic zero-type function on the right half-plane, with its reviewed
meromorphic continuation and off-pole-zero theorem. The quadratic and
linear exponential normalizations match exactly. This resource argument
uses the actual positive core mixture; it does not assume an unexplained
bias budget or a size bound.

## 5. Normalized least classes and the analytic contract

Now restrict to n=2m, which is a subsequence of the same physical identity.
Use the exact finite-factor and core normalizations, and remove the matched
least quadratic and largest linear rates. The identity has the form

    E_T(m) A_q(m,theta_m)+A_h(m)
       =P(m)[E_R(m) B_q(m,theta_m)+B_h(m)],             (4)

where theta_m=m omega lies in its compact cyclic orbit closure H containing
zero. Every actual strict cell or strict mixed component contributes its
own coordinate 2alpha to omega; all rational relations and resonances are
retained. The shared physical parameters determine this one orbit.

Here are the precise properties in (4):

1. A_q and B_q are finite sums of real linear exponentials e^(-d z), d>=0,
   times finite products of strict fixed-phase private and mixed factors
   evaluated at 2z. The same finite private strict factors multiply each
   component on a side. A phase-free least core is absorbed into E_X,
   leaving just that side's finite private strict product. Empty products
   are allowed.
2. E_X contains the finite private endpoint factors and, when applicable,
   the entire endpoint least-core sum. That sum is

       sum_(b in least class) w_b exp[-2(ell_X-ell_b)z] E_b(2z).

   It is zero type on the right half-plane, positive at nonnegative
   integers, globally meromorphic with finite-order local poles, and
   log E_X(m)=o(m). Finite sums here have no phase dependence. A common
   positive scalar may be put in either E_X or the finite coefficient.
3. At integer m, the higher-quadratic tails obey

       |A_h(m)|+|B_h(m)| <= exp[-delta m^2+O(m)+o(m)]                 (5)

   for some delta>0 if either tail is nonempty. There is no claimed
   holomorphic interpolation of these quadratic exponentials.
4. The strict coefficient class has a uniform full expansion on a common
   half-integer grid. Its leading denominator, after the largest linear
   class is selected, is m^(-beta)[b_0(theta)+o(1)] with inf_H b_0>0.
   This follows from the positive leading coefficients of every actual
   strict component and the finite positive B-route weights.
5. Finite sums and products of strict coefficients have analytic-density
   uniqueness: if their entire Puiseux expansion vanishes at a fixed
   phase, the function vanishes identically. To see closure when mixed
   and private factors coexist, divide the finite expression by a large
   common integer power z^J. Convolve the direct mixed inverse densities
   v times analytic germs and the once-integrated private inverse densities
   v^(1/2) times analytic germs, with any further b_rho integration needed.
   The finite result has a convergent half-power germ, is analytic along
   v>0, and is of exponential order. Watson plus analytic continuation
   proves uniqueness. Empty products are handled by taking J>=1.

All finite multipliers above are meromorphic globally with finite-order
germs at every fixed point. Different finite pole lattices cause no local
accumulation of poles. They are real on the positive real axis. E_X(m)
has a subexponential reciprocal bound at integers by log E_X(m)=o(m);
no complex reciprocal is used.

## 6. Weighted finite-mixture phase removal

This section spells out the extension of the reviewed finite-mixture lemma
needed for the multiplicative endpoint factors in (4). Put

    R(z)=P(z)E_R(z)B_q(z,0)-E_T(z)A_q(z,0),
    C(z,theta)=A_q(z,theta)B_q(z,0)-A_q(z,0)B_q(z,theta).

Using (4) and the positive strict denominator at large integers gives

    R(m)=E_T(m) C(m,theta_m)/B_q(m,theta_m)
                                  +Gaussian-small error.         (6)

The exact error is [A_h(m)-P(m)B_h(m)]B_q(m,0)/B_q(m,theta_m).
It remains Gaussian-small after division by E_T(m), or multiplication by
any fixed real exponential or power, by (5), the polynomial denominator
bound and the subexponential bounds for P and E_T and its sampled reciprocal.

Group the cross-product into its finitely many linear classes:

    C(z,theta)=sum_(d in D) exp(-d z) C_d(z,theta).

At theta=0, every C_d is identically zero. Indeed C(z,0)=0; select the least
d. Its coefficient is exponentially small relative to later groups on the
positive real axis, hence flat to all orders. Analytic-density uniqueness
annihilates it, and finite induction handles every remaining group.

For general theta in H, proceed through the same ordered groups. Once
earlier groups have vanished, division by B_q and its uniform reciprocal
expansion gives, for a suitable fixed power kappa,

    exp(dm)m^kappa R(m)
      =E_T(m)[sum_(lambda<=L) a_lambda(theta_m)m^(-lambda)
                                      +o(m^(-L))],                (7)

to every order on the actual half-power grid. Later linear classes and the
quadratic tails are flat in this formula. Inductively subtract the already
constant coefficients multiplied by E_T(z), and multiply by the next power
of z. Then subtract c E_T(z) for real c. Each resulting holomorphic function
has finite global exponential type in the right half-plane and
subexponential growth in both directions of a fixed positive vertical line:
real linear exponentials are bounded on that line, while P, E_T, E_R and
the strict factors are zero type. The reviewed extended zero-density lemma
therefore applies.

If a phase coefficient were nonconstant, relatively dense visits of the
orbit to two open phase sets of opposite sign would force positive-density
real zeros. The factor E_T(m)>0 preserves those signs, and the error in
(7) is relative to that factor. This contradicts the zero-density lemma
unless the function is identically zero, in which case the sampled equality
and recurrence of the orbit give the same constant-coefficient conclusion.
Thus every a_lambda is constant on H. At phase zero it is zero, because
C_d(z,0)=0. Inverting the nonzero denominator expansion and using analytic-
density uniqueness shows C_d(z,theta)=0. Induction over D gives C=0 on H.

No endpoint asymptotic power series, complex reciprocal of E_T, complex
moving phase, or quadratic exponential interpolation is used. This is why
the least-class homogeneity of Section 3 was required.

Equation (6) now makes R(m) Gaussian-small. R has the finite-type and
fixed-line vertical subexponential growth required by the reviewed integer
uniqueness lemma. Therefore

    P(z)E_R(z)B_q(z,0)=E_T(z)A_q(z,0)                  (8)

on the right half-plane, and then on their common meromorphic continuation
domain. This completes the exact analytic reduction.

## 7. Accumulating zeros force finite persistence

If I were infinite, the inherited equal-family theorem would give distinct
off-pole zeros z_j of P approaching -1/2 or -3/2. Every finite multiplier in
(8) has a finite-order meromorphic germ there. In a sufficiently small
punctured neighborhood, its isolated poles other than the possible central
pole are absent. Equation (8) makes E_T(z_j)A_q(z_j,0)=0.

A meromorphic function with a finite-order pole at the limiting point
cannot have an accumulating sequence of zeros there unless it is
identically zero: multiply by a sufficient power of z-z_* and apply the
identity theorem. But E_T(z)A_q(z,0) is not identically zero. For example
its value at z=0 is a positive sum of the surviving least-class weights,
because every normalized finite strict or endpoint factor is one at zero.
This contradiction proves I finite.

The result does not classify a whole-source scalar gauge as a finite
private-cell quotient. It bypasses that stronger classification using the
actual bounded-core reference-comb continuation. It still assumes the
actual shared-tuple scalar identity (1); a finite-data observation bridge
and the final local exclusion of arbitrarily small extra physical cells
remain distinct original-master obligations.

## 8. Suppliers and verification boundaries

* [Bounded anchor and actual reference factorization](../continuation-1900z/ANCHOR-AND-MEETING-INVARIANT.md), inherited structural/observation supplier.
* [Strict mixed physical formula and Gamma/Laplace continuation](MIXED-COMB-FIXED-PHASE-LAPLACE.md), hand proof under separate review.
* [Single-zero-arm mixed endpoints](MIXED-COMB-SINGLE-ZERO-ARM-ENDPOINT.md), hand proof under separate review.
* [Both-zero-arm exact moment identity](BOTH-ZERO-MIXED-ENDPOINT-SOL-AUDIT.md), independent all-arity hand derivation.
* [Both-zero-arm Mellin continuation](BOTH-ZERO-MIXED-MELLIN-CONTINUATION.md), hand proof under separate review.
* [Private exact phase removal and resource extension](../../chronology/continuation-2110z/UNIFORM-LAPLACE-PHASE-REMOVAL.md), with its separate independent audit.
* [Finite quadratic/linear mixture audit](../../chronology/continuation-2110z/FINITE-QUADRATIC-LINEAR-MIXTURE-SOL-AUDIT.md), inherited abstract coefficient contract; Section 6 supplies its explicit weighted extension here.
* [Gaussian-small integer uniqueness](../../chronology/continuation-2110z/SUPERSMALL-INTEGER-UNIQUENESS-SOL-AUDIT.md), including the fixed-line finite-type extension used above.

No governing prior result is presented as new mathematics. The new synthesis
is the A-backbone homogeneity argument and its combination with the actual
mixed reference-comb continuations to discharge the law-level bounded-core
finite-persistence implication. Correctness and applicability still require
review of these exact suppliers and their hypotheses; publication alone
would not provide that review. Historical novelty and formal verification
are not claimed. The full G4 master remains in progress.
