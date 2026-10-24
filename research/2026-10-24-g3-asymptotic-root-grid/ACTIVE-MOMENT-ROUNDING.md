# Weighted physical-cell moments and an explicit integer-rounding bound

Stable key: G3-ACTIVE-MOMENT-ROUNDING-01.

24 October2026UTC. Existing G3 owner.
**PROVED BY HAND:** the finite-array rounding inequality and its stated
conditional AG-Pair implication. Author self-review complete; independent
correctness review and Lean formalization unperformed. Cauchy-Schwarz
and elementary rounding are classical ingredients; historical novelty
is not asserted. No scientific/source/coefficient/symbolic/numerical/
solver/QE/model/native/compiler/build job ran.

The ACTUAL COMMUTATOR-TO-MOMENT estimate below is UNPROVED. It is one
optional sufficient test inside the existing AG-Pair attempt, not an
additional original acceptance condition, a second goal, an observed
kernel identity or a completed G3 endpoint.

## 1. Exact finite-array statement

Take ANY finite family a_i>0,0<u_i<=1, including an empty family. Define

    P_j=sum_i u_i*a_i^j,          j=3,4,5,
    Delta=sum_i u_i*a_i^3*(a_i-1)^2=P5-2P4+P3,
    D=sum_i u_i*a_i^3*(1-u_i)^2,
    F=Delta+D>=0.                                      (1)

Let J={i:a_i>1/2 AND u_i>1/2}, and let N_J be its ordinary INTEGER
cardinality. Then

    |P3-N_J|<=4F+30*sqrt(P3*F).                        (2)

In particular, for any real nu,

    dist(nu,Z)<=|nu-P3|+4F+30*sqrt(P3*F).               (3)

There is NO bound on the family size, no lower activity/scale margin,
and no upper bound on a_i. The integer selected by this lemma counts
only J. It is not asserted to count every physical cell or every
equivalent presentation.

## 2. Proof: discard small mass, then round actual active atoms

If a_i<=1/2, then(a_i-1)^2>=1/4, so its mass u_i*a_i^3 is at most
4 times its contribution to Delta. If u_i<=1/2, its mass is at most
4 times its contribution to D. Taking the union of these two classes
gives

    sum_(i notin J) u_i*a_i^3<=4Delta+4D=4F.            (4)

For i in J, a_i>1/2 implies

    (a_i^2+a_i+1)/a_i^3
       =1/a_i+1/a_i^2+1/a_i^3<=14.

Hence, by Cauchy-Schwarz,

    sum_J u_i*|a_i^3-1|
      <=14 sum_J u_i*a_i^3*|a_i-1|
      <=14*sqrt(P3*Delta).                            (5)

Also u_i*a_i^3>1/16 on J. Thus N_J<=16P3 and

    sum_J 1/(u_i*a_i^3)<=16N_J<=256P3.

A second Cauchy-Schwarz estimate gives

    sum_J(1-u_i)
      <=sqrt(D*sum_J 1/(u_i*a_i^3))
      <=16*sqrt(P3*D).                                (6)

Use |u_i*a_i^3-1|<=u_i*|a_i^3-1|+(1-u_i). Equations(4)--(6) yield

    |P3-N_J|
      <=4F+14*sqrt(P3*Delta)+16*sqrt(P3*D)
      <=4F+30*sqrt(P3*F).

This proves(2). The triangle inequality and the integer N_J prove(3).
All zero cases, including F=0 or an empty family, are included without
division. No asymptotic argument or executed array test is used.

## 3. Literal source specialization; no new observation

For an ACTUAL strict equal-arm private independent word K, let h_i>0
be its actual cell arm exposures and g_i its original parent0 coins.
Retain native gamma_i=1-g_i, fresh CURRENT-root choices and opaque old
trees. Ordinary gaps stay in the original word.

For the existing reference S(t) define its actual bigon exposure

    h_B(t)=-log(t/(2-t))>0.

Set, as INTERNAL mathematical quantities of the actual presentation,

    a_i=h_i/h_B(t),       u_i=4g_i(1-g_i) in(0,1].      (7)

Then(1)--(3) hold for EVERY finite physical word, whether or not it
commutes with S(t), with no count, coin or relative-scale promise.

The coin part has an exact existing-source interpretation. In the
retained general source variables, with first-arm probability g,
equal arm durations h give

    z=(2g-1)*h,
    third=g(1-g)*(1-2g)*z^3
          =-g(1-g)*(2g-1)^4*h^3<=0.

Therefore

    D=-4/h_B(t)^3 * sum_i third_i.                    (8)

This is direct substitution into the OLD source variable definition,
not a newly computed matrix coefficient or a new drift identity.
P3,P4,P5 are WEIGHTED PHYSICAL CELL-SCALE moments. They are NOT assumed
to equal finite kernel entries, no-merger log coefficients, moments in
the root-count index, or independently observable route probabilities.

The criterion introduces no new logarithmic calendar/rate equation in
the original input. Exposures are used only to state a mathematical
sufficient bound for actual sources. No exposed COMMON bit is refreshed;
the natural modes and every row retain ONE physical tuple.

## 4. A precise optional source estimate sufficient for AG-Pair

Reuse the completed all-core/pair-calibrated reference and put

    c=2^(-1/m),     nu=log(c)/(4log(t)).

Suppose one can prove that SOME fixed m,M,B,T, with B>=1 an integer,
has the following property for EVERY original fitting strict equal-arm
word K of arbitrary finite length/coins/scales:

    K_C=E(c), b2I(K)=c^(3/4),
    [K_I,S(t)]=0 on the COMPLETE forest cap M,
    c<t^4<1, nu>=T

IMPLY the two SOURCE estimates

    |P3-nu|<=B*nu^(-1/2),
    F<=B*nu^(-2),                                   (9)

where(7) is calculated on that actual presentation.

**The implication(9) is UNPROVED.** It is stronger/more specific than
the AG-Pair conclusion and is not made a necessary condition for original
G3 success. If it fails, AG-Pair itself may remain true by another
mechanism. No theorem here substitutes commutation for(9).

Nevertheless the consequence is exact and quantitative. For
nu>=max(T,2,B), we have P3<=2nu. Equations(3),(9) give

    dist(nu,Z)
      <=B*nu^(-1/2)+4B*nu^(-2)
                         +30*sqrt(2B)*nu^(-1/2)
      <=[5B+30*sqrt(2B)]*nu^(-1/2).                  (10)

Thus(9) would prove AG-Pair with k=2 and any integer
A>=5B+30sqrt(2B), after the stated fixed threshold change. The already
completed [robust arithmetic](https://github.com/Sodelin/Research-Commons/blob/4697d8e3ec032a2669dd121b35667865eb325a9c/research/2026-10-24-g3-asymptotic-root-grid/PROOF.md)
and [original all-core source map](https://github.com/Sodelin/Research-Commons/blob/26898807efa9d09b632922a2cb47e500ff1df42f/research/2026-10-24-g3-all-core-commutation-reduction/PROOF.md),
with its completed pair-calibrated successor, would then give the
original impossibility consequence. They are not derived again.

The intended reverse witnesses are admitted at this precise boundary:
for K=S(t)^N and t=c^(1/(4N)), every actual bigon has a_i=u_i=1.
Thus P3=P4=P5=N=nu and F=0. This is a hand substitution into the OLD
physical integer powers, not a new tuple/source run. Ordinary bookends
remain strictly positive.

This makes(9) a concrete positive-defect question tied to actual cell
parameters, rather than an assertion about all positive matrices.
Its uniform source acquisition remains the substantive missing step.

## 5. Exact prior comparison and exclusions preserved

The current/archive weighted-rounding, near-unit, active-coin, moment/
integer and variance aliases were searched before this derivation.
This is a bounded prior comparison, not historical priority or absence.

The completed synthetic
[G3-SEMISIMPLE-ENDPOINT-NOGO-01](../2026-10-23-g3-semisimple-endpoint-nogo/PROOF.md)
is NOT used as a physical supplier here. The relevant locally retained
synthetic proof is G3-SEMISIMPLE-PROJECTIVE-ENDPOINT-UNDECIDABILITY.md,
20451B/SHA25632720efb91abb80cfce99b785826426e2d0cf0fc35acbd25ba5f6ae9df831541;
selected paragraphs in its Sections2--5 were reread. It forces parameter equality in a DIFFERENT
synthetic absorption alphabet. No synthetic actuator, affine variance
row or hidden repeated-box readout is imported into(7)--(9).

The complete existing R7 fair weak source proof and nonlinear source
jump-trace note were read, with selected R6 Sections1--5 through(18). They supply the actual
source variables, returning storage and organized-block estimates at
their stated completed HAND scopes. R7 needs fair coins and an ORDINARY
endpoint; R6 needs its physical sign/calibration/block/coin promises.
They do NOT prove(9). The source endpoint under commutation has the
already computed NONZERO storage boundary; it has not been set to zero.

The complete OLD G4KingmanHankelObstruction source was also read:
Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6,
research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/
c19f1ccd28fdf75180ee15ad2fc093c542f86554ebe4c09cb23fe384ef2567ae.lean.
It proves arbitrary shifted Hankel nonsingularity of q^binom(n,2)
in the ROOT-COUNT index. It neither excludes nor supplies(2), which
uses moments of PHYSICAL CELL scales. This is source inspection only;
no new Lean elaboration/object evidence is claimed.

The completed paired-diagonal synthesis, global/joint additive-log
admissions, actual all-core maps, arithmetic reduction and uniform matrix/
source lower bounds remain proved. No old source coefficient, one-cell
guard, generic positive-factorization or count-consumer project is reopened.

## 6. Original endpoint and evidence boundary

Completed here: the elementary weighted integer-rounding inequality for
all finite arrays/actual physical presentations, and the conditional
implication(9)=>AG-Pair. This is supporting mathematics inside the existing
route, not a new full attack or new source-coefficient discovery.

Still UNPROVED: acquisition of(9) from the complete source equations,
AG-Pair by any method, and original total G3 YES/terminating-NO or its
source-complete impossibility. No new mandatory supplier/acceptance
requirement is added. In particular the lemma is not a bound on all
equivalent presentation lengths.

No local Git, new chat/subagent/peer turn, scientific/source/solver/QE/
model/native/compiler/Lean/Cargo/Lake/CI action, writer bypass or held/
USED/UNKNOWN replay. Existing owners, original legal menus/source fields,
one identity and encryption-before-runtime-persistence remain unchanged.
