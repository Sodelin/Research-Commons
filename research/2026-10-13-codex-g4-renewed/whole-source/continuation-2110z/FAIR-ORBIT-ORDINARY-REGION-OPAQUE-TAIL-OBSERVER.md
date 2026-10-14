# A fair-orbit ordinary-region observer with an unknown upper continuation

Contributor: Codex whole-source lane, 14 October 2026. **Hand-proof
candidate; independent review requested.** The positive-entry comb
estimate is due to the Codex lead G4 lane and was consistency-audited
by Sol, who disclosed prior involvement. The bounded-pre-root-merger quadratic-rate argument is inherited
from the full COMMON profile theorem. The new step is recovery of ONE
finite permutation orbit from its minimum quadratic envelope, followed
by ordinary-mixture cancellation. No full original INDEPENDENT-to-COMMON
transfer or finite INDEPENDENT certificate is claimed.

## 1. Precise conditional interface

There are d>=2 labelled input ports, with a specified collection of
disjoint port pairs. A specified subset of these pairs is fair; its
independent swaps form a known finite group G. Let T be a finite ordinary
population tree on these ports, with nonnegative finite exposures, after
merging unary subdivisions and zero internal edges when necessary. Put
its root at the least common ancestor of all ports: any ordinary stem
above that point belongs to the upper continuation, not to T.

Let U be a projective exchangeable completed response law on roots
entering this common port. Assume

                         U=E_a V,  a>0,                     (1)

for a projective exchangeable completed law V. Ordinary Kingman completion
Q satisfies (1), since E_a Q=Q. A relevant original-source application
must justify its positive common entry interval or use this Q case.
It must not assume that arbitrary exchangeable U satisfies (1).

The given ENTIRE response table is

                  H_sym = |G|^(-1) sum_(g in G) (gT) U.      (2)

Here g only permutes port labels. Every summand uses the same U and the
same physical ordinary tree before relabelling; (2) is not an arbitrary
mixture of unrelated trees. Coinciding orbit members are allowed. The
table may additionally retain arbitrary finite outside panels, provided
all outside interactions occur above the common cut port, so that the
same factorization holds jointly. Only its no-outside marginal is needed
to identify T's orbit.

**Conditional observer theorem.** The entire table (2) determines the
ordinary forest operator orbit {gT:g in G}, and hence its uniformly
symmetrized operator K_sym. It also determines the complete upper table
U. With the stated cut-port factorization, this includes every retained
outside panel. Consequently the simultaneous fair-invariant COMMON
selector is determined at this supplied region interface.

These are operations on a table already recovered from original
observations. No claim is made that arbitrary original sources already
supply that table, its region grouping, or its port alignment.

## 2. Inherited positive-entry completion bound

Write q_m(U) for a specified labelled rooted comb probability and
kappa_m=2^(m-1)/[m!(m-1)!], with kappa_1=1. The lead's estimate, checked in
[the shared-upper applicability audit](COMMON-PROFILE-SHARED-UPPER-SOL-APPLICABILITY.md),
is

             0<c<=q_m(U)/kappa_m<=C<infinity for every m.     (3)

For clarity, its exact identity is

 q_m(E_a V)/kappa_m
   = sum_(k=1)^m Pr(N_m(a)=k) q_k(V)/kappa_k,                (4)

where N_m is ordinary Kingman root count. The prescribed comb sequence
on m-k mergers has pair-choice probability kappa_m/kappa_k. The infinite
Kingman root count at a has a Gaussian upper tail, whereas
1/kappa_k=exp(O(k log k)); this gives the upper bound in (3). The event
N_infinity(a)<=2 has positive probability and q_1/kappa_1=q_2/kappa_2=1,
giving the lower bound. Thus for fixed s,

              q_(m-s)(U)/q_m(U)<=(C/c)m^(2s).               (5)

No uniform constant as a tends to zero is needed or asserted.

## 3. Recover the minimum covariance quadratic from actual topologies

For an ordinary port tree S, define

 Q_S(v)=sum_(finite edges e) t_e (sum_(i below e) v_i)^2,
 L_S(v)=sum_(finite edges e) t_e (sum_(i below e) v_i),        (6)

where v is a positive integer vector on the d ports. Allocate Nv_i roots
at port i, total m=N sum_i v_i. Choose ONE labelled comb G_N whose first
d leaves contain one fixed label from every port, in a fixed order; place
all remaining labels afterwards in any fixed order.

This comb need not prohibit every pre-root merger. What matters is the
uniform bound: a compatible merger creates an initial prefix of its
spine. Once a prefix contains all d ports, its clade cannot form below
the stem-free port LCA. Therefore at most s0=d-2 compatible mergers can
occur below that root, for every S in the orbit and every N. A common
stem above that LCA has already been included in U. This is exactly the
inherited all-port prefix argument, not an assumption that the first
two ports cross every conditional root split.

The no-finite-merger history has probability

 D_S(Nv)=exp[-N^2 Q_S(v)/2+N L_S(v)/2].                       (7)

It then completes with q_m(U). Hence (3) yields a lower bound
c kappa_m D_S(Nv). For the upper bound, classify the at most s0 compatible
mergers by their finite tree edges. There are finitely many patterns,
independent of N. Their allowed pair-merger rates are one; integration
over fixed finite lengths contributes constants. Replacing each edge's
root count NV_e by at worst NV_e-s0 changes the survival exponent by
O(N). At the root use q_(m-s)(U)<=C kappa_(m-s) and
kappa_(m-s)/kappa_m<=m^(2s). Thus

 c exp[-N^2 Q_S(v)/2+O(N)]
   <= Pr_(S U)(G_N)/kappa_m
   <= C_S m^(2s0) exp[-N^2 Q_S(v)/2+O(N)].                   (8)

The O(N) terms and constants may depend on S,v,U but not N. Vanishing
ordinary edges simply remove histories; the all-no-merger lower bound
remains positive. The original compatible-history proof applies after
suppressing them.

Every summand of (2) has positive weight. Taking the logarithmic N^2
rate of the observed probabilities therefore gives

 M_T(v):=lim_(N to infinity) [-2/N^2]
             log[Pr_(H_sym)(G_N)/kappa_m]
         = min_(g in G) Q_(gT)(v).                         (9)

This is an all-law proof functional; it is not an infinite physical
experiment or a finite stopping algorithm. It uses no directed sparse
moment observer and no supplied bound on an arbitrary mixture support.

## 4. A single orbit is determined by its minimum envelope

Suppose another pair S,W satisfying the same interface and the SAME
known group G gives the identical entire table. Equation (9) makes the
two minimum envelopes equal on every positive integer vector. Homogeneity
extends equality to positive rational vectors, then continuity extends
it to the open positive cone in R^d.

Remove duplicates from each finite quadratic orbit. Outside the finite
union of equality hypersurfaces between distinct quadratics, each orbit
has a unique minimizing quadratic. Choose a point in the positive cone
outside both collections of hypersurfaces. On some common open
neighborhood there are fixed g,h with

                         Q_(gT)(v)=Q_(hS)(v).              (10)

Two quadratic polynomials agreeing on an open set have equal coefficient
matrices. Therefore these orbit members have the same rooted covariance
matrix. Because each collection is ONE orbit under the same group,
applying the group yields equality of the whole two orbits.

Equivalently, every distinct orbit member is exposed by some positive
vector: a generic vector exposes one, and group action transports that
vector to expose each other member. The positive cone is invariant under
port permutations; an individual vector need not be fixed. Arbitrary
mixtures do not enjoy this transitive-orbit conclusion.

The covariance matrix determines the stem-free ordinary population
tree operator by the inherited rooted-tree reconstruction. Its diagonal
entries give root-to-port lengths; off-diagonal entries give shared
root-to-pair-LCA lengths. They determine the hierarchy and its positive
edge increments, with zero edges and unary subdivisions quotiented out.
Consequently equality of covariance matrices gives equality of the
complete ordinary forest operators, not just of their scalar diagonals.
Uniform averaging over the known group gives the same K_sym, even when
the orbit has a nontrivial stabilizer.

## 5. Recover the actual upper completed law by ordinary inversion

Choose a fixed opened port j and put n roots there and none at the other
opened ports. Each gT reduces to an ordinary path of known exposure a_g
from j to the common port. Therefore this marginal is

                    F_n=[ |G|^(-1) sum_g E_(a_g) ] U_n.     (11)

Let K_j be that known ordinary mixture. Its probability of retaining n
singleton roots is

                    d_n=|G|^(-1) sum_g exp(-lambda_n a_g)>0.

Opacity gives the completed-row equation

 F_n = d_n U_n + sum_(forests f with fewer than n roots)
                             K_j(n;f) graft_f U_(|f|).       (12)

Induction in n recovers all U_n. For an arbitrary fixed outside panel e,
the same equation with U_(n,e) and F_(n,e) holds: the prefix to the common
cut port is private relative to those outside labels. Its natural
drivers are independent of the upper evolution at the fixed physical
tuple. The one-root case initiates the same induction, and all outside
dependence is retained in each term.

Unlike erasing a common stem by E_sQ=Q, this argument retains any unknown
stem within U and learns its effective completed law. It never pretends
to observe a hidden forest output or a separately queried port law.

With the orbit operator and U known, the
[simultaneous fair selector](SIMULTANEOUS-FAIR-SELECTOR-AND-OPAQUE-TAIL-GATE.md)
can be evaluated, including known biased coins when applicable. It is
invariant under the remaining fair port swaps.

## 6. Source gate still required

For an actual lowest opened blob, the intended application must prove
from original completed observations that the identified descendant
cuts/ordinary exits form this region, recover its lower input kernels,
and extract its entire jointly symmetrized port table with the SAME
upper continuation. Those grouping and alignment premises are not
established by this note. A successful source induction must also show
that the recovered upper interface can be processed without adding
physical taxa, interventions or independently fitted parameter tuples.

The observer removes the arbitrary-U profile/cancellation obstacle AT
THIS PRECISE ONE-ORBIT INTERFACE. It does not apply to a general finite
mixture of unrelated ordinary port trees, varying upper continuations,
or an arbitrarily declared latent port experiment. Full all-law
INDEPENDENT-to-COMMON transfer and the stronger finite-prefix master
remain distinct open duties.

Validation: hand derivation only; independent review requested. The
quadratic-rate proof and ordinary covariance reconstruction are reused
from the inherited full COMMON theorem at their explicitly modified
suffix hypothesis; no reconstruction novelty is claimed for those parts.
