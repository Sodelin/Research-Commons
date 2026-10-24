# Weak equal-arm paired diagonal words at every finite cap

Contributor: existing G3 owner. 24 October 2026 UTC.
Stable key: G3-WEAK-EQUAL-ARM-PAIRED-DIAGONALS-01.

**PROVED BY HAND at the stated diagonal scope.** Author self-review is
complete. Independent correctness review, Lean and scientific execution
have not been performed. Original G3 and CP-Pair remain unresolved.

## 1. Exact theorem and the remaining original goal

Fix a finite entering-CURRENT-root cap M>=3, numbers C,D with

    0<C<D<sqrt(C)<1,

and any 0<eta<1/2. There is ONE nonempty finite strict natural private word

    K=E(z0) B(q1,q1,g1) E(z1) ... B(qL,qL,gL) E(zL)

such that

    K_COMMON=E(C) at EVERY forest arity,
    b_n(K_I)=D^binom(n,2),  2<=n<=M.                 (1)

All arms are literally equal within each cell. Every arm survival and
ordinary survival is in(1-eta,1), and every natural parent0 coin lies in

    1/2<g_i<1/2+eta.

One physical tuple supplies every arity and BOTH mechanisms. The ordinary
pads and connectors are positive. The unmarked private word retains opaque
current-root grafting; no inherited subtree is rerouted by its leaf count.
Native parent1 probability is gamma_i=1-g_i.

Moreover the map from this fixed finite word's equal-arm source parameters
to (log COMMON passage, log b2I,...,log bMI) has full rank M at a realizing
point. Equivalently one has the two scalar passages and the M-2 higher
Newton coordinates. This is a statement about an actual finite source,
not independent fitting of rows or an external mixture.

This theorem controls the no-FURTHER-merger diagonal, not the remaining
INDEPENDENT forest coordinates. It does NOT construct a full forest
ordinary return, a CP-Pair counterexample, an admitted fixed G4 target,
a complete G3 NO mechanism or an all-copy finite physical word. L may
depend on M, C,D,eta. The same C,D can be used at every finite M.

For G3's active reference reduction, take D=C^(3/4). Thus even with its
two fixed pair coordinates, a prescribed COMMON budget and arbitrarily
weak equal-arm cells/near-fair coins, the DIAGONAL projection has exact
finite solutions at every cap. Any root-index argument must use the
remaining chronological kernel constraints. This removes a diagonal
shortcut; it does not replace the original full goal by that projection.

## 2. Prior-solution comparison and exact difference

At Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6, the COMPLETE OLD sources

* research/2026-10-04-dot-diagonal-character-signs-2118z/
  DIAGONAL-CHARACTER-FINAL.md,11149B/SHA256
  05fdaf1563839a7c8e19d030ffcaa6de93b40be6d6055af702fd4c45748e1697;
* research/2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/
  UNIFORM-TIME-DIAGONAL-FINAL.md,10359B/SHA256
  ab700065a7d0ed1a6ef5a680743ecffabdc24728325a1a58b70673d254c41905,

were actually reread. They already prove unrestricted diagonal sign
richness, the unweighted regular-sum lemma, Newton divisibility, exact
finite diagonal words at prescribed INDEPENDENT pair time and their
higher diagonal rank. These are PROVED/REUSED, not new problems.

The old diagonal sign construction has a rare coin and a possibly strong
arm. Its explicit weakness is PAIR LOSS. Its uniform-time successor uses
the same unequal-arm rare profile and does not prescribe the COMMON
passage. The additional restriction here is literal equal arms, BOTH
fixed passages and arbitrarily short arms/near-fair coins. Sections3-4
supply the single all-order source rule for that restriction. Sections5-6
apply the OLD regular-sum/IFT method, then a finite repetition to control
both total passages. No new general semigroup or IFT theorem is claimed.

The OLD weak-cell convex-centering/primitive-sign source16412B/SHA256
482321c72adaafb3f38a15bc2563b5aa8950dc26a1fc6d019c44abad4cd37e8b
was inspected in Sections1-4. Its arms are independently variable and
its external convex mixture is explicitly not a physical word. Its
primitive statements are not the equal-arm diagonal construction below.
The later covariance and rare-critical generating notes were inspected
at their actual profile/statement boundaries; their source identities
remain reused. These bounded comparisons are not historical novelty
certification or proof of corpus-wide absence.

The retained R8/R9 weak-family statements were read at their scope
prefixes. They exclude COMPLETE forest returns using actual source energy
and off-diagonal constraints. They are consistent with(1); no such
completed hand theorem is reopened or demoted.

## 3. One exact binomial/spin source for all arities

Use arm coalescent exposure h>0, so the equal survival is q=exp(-h).
Let xi_1,...,xi_n be independent signs with mean mu=2g-1. If k signs
are+1, the number of same-arm pairs is

    binom(k,2)+binom(n-k,2)
      =lambda_n/2+(1/2)sum_(a<b) xi_a*xi_b,
    lambda_n=binom(n,2).

The actual original routing formula therefore gives EXACTLY

    b_n(h,g)
      =exp(-h*lambda_n/2)
         * E exp[-(h/2)sum_(a<b) xi_a*xi_b].          (2)

These are initial CURRENT-root tokens of this cell. Formula(2) counts
no mergers during its two actual equal arms and is not a new stochastic
source or a replacement of full-forest evolution by a count kernel.

Set b0=b1=1 and

    D_j=sum_(n=0)^j (-1)^(j-n) binom(j,n) log b_n.

For fixed a>0,kappa>0 use the strict profile, for epsilon>0 small,

    h=a*epsilon,  mu^2=kappa*h,
    g=(1+sqrt(kappa*a*epsilon))/2.                   (3)

The equal-arm law is invariant under g->1-g. Thus every fixed log b_n,
and every D_j, is analytic jointly in h and mu^2 near(0,0). After(3)
they are analytic in epsilon,a,kappa, despite the square root in the
physical coin. Only positive epsilon is a realizing source.

For EVERY fixed j>=3 the all-order rule is

    D_j
      =c_j*a^j*(1-2j*kappa)*epsilon^j
          +O(epsilon^(j+1)),
    c_j=(-1)^j*(j-1)!/2^(j+1).                     (4)

In particular all coefficients below epsilon^j vanish IDENTICALLY in
a,kappa, and division by epsilon^j extends jointly analytically near any
strict finite parameter list. This is not just a leading sign along an
isolated curve. Constants/remainders may depend on j and on a fixed
compact profile set; no all-arity uniform remainder is asserted.

## 4. Proof of the single rule, including its lower vanishings

Expand the log expectation in(2) by joint cumulants of edge variables
Y_ab=xi_a*xi_b. Cumulants of collections supported on disjoint vertex
sets vanish, since the signs are independent. Consequently each
coefficient is a sum over connected edge multigraphs on a selected
set of initial tokens. Repeated edges are allowed in this expansion.
Symmetry makes the contribution on any fixed j-set the coefficient
of binom(n,j), which Newton difference D_j selects.

A connected graph on j vertices needs at least j-1 edge occurrences.
With exactly j-1 it is a simple tree. At mu=0, edge products on a tree
are independent fair signs: choose one vertex sign and all edge products
as coordinates, which bijectively specify the original signs. Hence
the joint cumulant of its distinct edges has zero constant term.
It is even in mu and therefore starts at least at mu^2.

Thus j-1 edges cost at least h^(j-1)*mu^2, which is order h^j under
mu^2=kappa*h. Fewer edges cannot cover j connected vertices. Terms with
at least j edges cost at least h^j. This proves the lower vanishings.

There are exactly two contributions at order h^j.

(a) A tree contributes at mu^2 precisely when it is a path. The full
product moment of a tree is mu to the number of its odd-degree vertices.
Exactly two odd-degree vertices force a tree to be a path. In any
proper partition of the distinct path edges, each nonempty forest
block has at least two odd vertices, so the product of block moments
is O(mu^4). Therefore the path joint cumulant is mu^2+O(mu^4).
For a nonpath tree every term in its cumulant is O(mu^4).
There are j!/2 unoriented labelled paths. With edge weight -h/2,
their total leading contribution is

    (j!/2)*(-h/2)^(j-1)*kappa*h.

(b) A connected j-edge multigraph at mu=0 can contribute only if every
vertex has even degree. Otherwise no partition into nonzero even-degree
block moments exists. A connected graph with j vertices, j edges and all
degrees even has degree two at every vertex. For j>=3 it is a simple
cycle. Its full product is1, while every proper edge block has odd
endpoints and zero moment at mu=0. Its joint cumulant is therefore1.
There are (j-1)!/2 unoriented labelled cycles, giving

    ((j-1)!/2)*(-h/2)^j.

The factorial in the exponential/cumulant series cancels the ordering
count of these distinct edges. Adding(a),(b) is exactly

    (-1)^j*(j-1)!/2^(j+1)*(1-2j*kappa)*h^j.

All other terms have at least one more power of h after substitution.
Evenness in mu makes the remaining powers integral. This proves(4)
coefficientwise for every fixed j, with no cap table or extrapolation.

As a hand consistency identity, j=3 gives
(-1/8+3*kappa/4)h^3; j=4 gives(3/16-3*kappa/2)h^4.
These are consequences of the same formula, not new executed controls.

## 5. A finite regular unweighted zero and strict IFT lift

For j=3,...,M define

    J_j(a,kappa)=c_j*a^j*(1-2j*kappa),
    a>0,kappa>0.

No nonzero covector is nonnegative on all these vectors. Absorb the
nonzero c_j into its coefficients and put P(a)=sum_(j=3)^M d_j*a^j.
Such a nonnegative pairing would say

    P(a)-2*kappa*a*P'(a)>=0 for every a,kappa>0.

Sending kappa to infinity forces P'(a)<=0; sending it to0 forces
P(a)>=0. But P(0)=0, so a nonincreasing such P must be identically0.
All d_j vanish, a contradiction. Negation treats a nonpositive pairing.

Apply the OLD regular unweighted-sum lemma from the two sources in
Section2. Its premises hold on the connected open domain a,kappa>0,
and J->0 as a->0 with kappa fixed. For clarity, the reused argument is:
derivatives span the target, hence some finite sum has a submersion ball
B(v,r); the absence of a containing halfspace gives finitely many image
vectors whose positive cone is the whole space. Represent -v conically,
round a large integer multiple of its coefficients, and correct the
bounded rounding error inside the linearly enlarged sum of that ball.
This yields a FINITE list p*=(a_i,kappa_i) such that

    sum_i J(a_i,kappa_i)=0

and the derivative of this sum has rank M-2 at p*. All a_i,kappa_i>0.
The list and all repetition counts are fixed BEFORE epsilon varies.

Use the L actual cells from(3) and set

    F_j(epsilon,p)=epsilon^(-j) sum_i D_j(B_i).

By(4) this extends jointly analytically to epsilon=0, with
F(0,p)=sum_i J(p_i). Choose an invertible(M-2)-column minor at p*.
The analytic IFT gives p(epsilon) near p* with F=0 exactly, for all
sufficiently small positive epsilon. This is ONE common physical tuple
at every arity. Every arm is equal within its cell and tends to zero
exposure, and every coin tends to1/2 from above.

Newton inversion now gives exactly ordinary I diagonals through M for
the bare product:

    log b_n=binom(n,2)*log b2, 2<=n<=M.

This is an actual finite word, not a convex mixture. The list is fixed,
and the selected higher-diagonal minor stays nonzero at small epsilon.

## 6. Control BOTH total passages, with no cap-dependent budget

Let

    H_B(epsilon)=sum_i h_i,
    tau_B(epsilon)=-sum_i log b2I(B_i),
    A0=sum_i a_i(0)>0.

Equation(2), or the actual pair formula, gives

    H_B=A0*epsilon+O(epsilon^2),
    tau_B=(A0/2)*epsilon+O(epsilon^2).

Fix rho in(1/2,1). Add total strictly positive ordinary exposure

    A(epsilon)=(rho*H_B-tau_B)/(1-rho)>0.

Distribute it equally among the L+1 required ordinary populations.
Their addition preserves every D_j, j>=3. The actual block has

    H_block=A+H_B=(H_B-tau_B)/(1-rho),
    tau_I_block=A+tau_B=rho*H_block.                (5)

Its COMMON kernel is literally E(exp(-H_block)) because all cells have
equal arms. Moreover H_block is analytic, vanishes at0 and has positive
derivative A0/[2(1-rho)]. It therefore takes EVERY sufficiently small
positive value.

For the desired C,D let

    H=-log C>0,  rho=(-log D)/H in(1/2,1).

Choose an integer R sufficiently large, then choose the small positive
epsilon with H_block=H/R. Concatenate R identical copies of this actual
block. COMMON passages multiply to C. Every I no-merger diagonal
multiplies to exp(-R*rho*(H/R)*lambda_n)=D^lambda_n.
This proves(1) with EXACTLY the prescribed C,D, at the same H for every M.

Increasing R if necessary makes every arm and ordinary population
arbitrarily weak and every coin arbitrarily close to1/2. Adjacent
ordinary bookends may merge at fresh junctions; their sum also tends
to zero, so the stated survival floor remains strict. R is finite;
no infinite physical product or zero-duration population realizes(1).

This finite repetition is what fixes the BOTH budget. The old
unrestricted prescribed-I-time theorem is not re-proved as new.

## 7. Rank, algebraic existence and original source scope

The higher-Newton rank M-2 survives the IFT lift. At fixed epsilon>0,
the map(a_i,kappa_i)->(q_i,g_i) has nonzero Jacobian because
partial_a q_i=-epsilon*q_i and partial_kappa g_i>0. Thus this rank is
in actual equal-arm source coordinates, not only formal profile variables.
Along that zero-defect
family vary epsilon and the independently available total ordinary time A.
For the two passages their Jacobian has determinant

    H_B'(epsilon)-tau_B'(epsilon)=A0/2+O(epsilon)>0.

Together with the higher minor this gives rank M for
(H_COMMON,tau_I,D3,...,DM). Logarithms and Newton inversion are invertible
coordinate changes on the positive diagonal chart. Repeating blocks
does not lose rank: vary one realizing block while holding the others fixed.

For algebraic C,D and an algebraic survival/coin window, the same finite
word equations are polynomial in its strict survival/coin coordinates,
including equal-arm equations, COMMON product C and b_nI=D^lambda_n.
Real-closed-field transfer therefore permits algebraic survival/coin
witnesses on that fixed word. This does not assert algebraicity of
calendar dates, logarithmic exposures or biological rates. Their original
source/calendar realization is the already-proved forward word supplier,
not a new log constraint or numerical rate construction.

The retained proper-bridge insertion embeds each word in an admitted
positive four-taxon original source with its original IDs and one bank.
Known positive topology tomography or the already supplied passive
diagnostic adapter implements the stated observations where that menu
is licensed. No hidden forest or register observation is granted. No
new all-core converse is asserted by this forward embedding.

The theorem's COMMON equality is for the PRIVATE UNMARKED current-root
forest law. It does not erase an externally read register or extend to
a source that shares its private seeds with an exterior actuator.

## 8. What is closed, and the exact remaining G3 duty

The BOTH-diagonal synthesis task in(1), including a prescribed total
COMMON budget and the restricted weak equal-arm/near-fair alphabet, is
PROVED. Do not reopen it as a missing time bound or a next-cap task.

Every constructed word contains a positive finite number of genuine
cells. The OLD all-copy chain-count invariant therefore ensures that its
I diagonal eventually differs from the entire ordinary I law. That old
asymptotic/provider is reused, not rederived here.

The pair(E(C),E(D)) with C!=D is a comparison family, NOT supplied as one
admitted finite ordinary G4 target. Exact finite diagonal agreement does
not supply full forest agreement, another source class, a nonlinear
original observer, a finite word at all caps or either original endpoint.

For CP-Pair, (1) disposes only of a diagonal route to its integer index.
No constructed word is asserted to commute with S(t); the C,H and higher
chronological coordinates remain actual equations. The original
source-complete commutation reduction remains proved, while CP-Pair and
unrestricted terminating G3 NO remain unproved. The selected next action
stays the full source-specific commutation/rigidity argument, rather
than a stronger diagonal theorem or another cap producer.

No biological/forest producer, symbolic or numerical control, solver/QE,
source compiler, model/native/Lean/Cargo/Lake/CI job, local Git action,
subagent or old-suite replay was performed. The proof is hand source
algebra, finite cumulants, the OLD regular-sum argument and analytic IFT.
