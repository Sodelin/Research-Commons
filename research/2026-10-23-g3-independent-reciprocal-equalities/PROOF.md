# Independent reciprocal exponents at fixed algebraic bases

Stable source key: G3-ARITH-INDEP-RECIP-EQ-01.

23 October 2026. Existing G3 owner. Status: PROVED BY HAND, not Lean
formalized. Independent review has not been performed; no solver, source
producer, numerical check, native build or new experiment was run.
This is a supporting arithmetic result, not original G3 closure or a new
full G3 attack. No historical novelty claim is made for its classical inputs.

## 1. Prior-solution comparison and precise increment

Original G3 still requires total exact recognition on every original finite
algebraic joint input, one actual strict source/ID map/physical bank on YES,
and termination excluding every unknown finite source on NO. Its original
COMMON/I/BOTH, menu, chronology and register contract is unchanged.

The following actual statements/proofs were compared before selecting this
extension. Commons below is8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6.

- The accepted predecessor is
  `handoffs/2026-10-16-codex-g3-unreviewed-source-copy-001/INPUT-RADICAL-BOUND-AND-FULL-SOURCE-TEST-03.md`,
  25098B/SHA25697987236e5c6f5429d2f597ff1ebd5b34dac7078ff56515122483524a5ad968e,
  Gitblob09d171c9d252f7120cd8dc5f97b25f48c7fd3de7, with later scoped
  `research/2026-10-16-dot-g3-radical-review-0055z/REVIEW.md`,
  SHA179b0a86bdbc37816f971cf5fe072c0258071e47a5c205ae85c0852897468af4.
  Its common-denominator reciprocal-power obstruction, identity alternative
  and source counter-test are OLD/REUSE. Sections3--4 were reread for the
  exact exponent quantifier; the complete proof/review had already been read.
- The subsequent COMPLETE20193B source
  `handoffs/2026-10-16-codex-g3-primitive-multiplicity-increment-005/ONE-TYPE-BOUNDEDNESS-AND-PRIMITIVE-MULTIPLICITIES-07.md`,
  SHA5c5cd7e670d670d528d0a8414ec39748e37db467e84c4d1b18f25b20056f9916,
  Gitblob67aaf47b31c221fd4749f8f547abb57fb96d61c3, was read. It supplies
  hand boundedness without an effective exceptional cutoff, and a fixed
  rational full source input with arbitrarily large independently chosen
  multiplicities whose physical types RETUNE. It expressly preserves the
  distinction between every presentation and one witness. Those completed
  hand arguments are reused, not reopened for missing Lean/review.
- The saturated positive S-unit coordinate construction in
  `G3-REPEATED-BLOCK-ALGEBRAIC-COUNT.md` is reused. Its earlier NEW attribution
  is corrected by `G3-RECIPROCAL-PRIOR-ATTRIBUTION-CORRECTION-20261023.md`.
  Saturation and classical radical independence are not new here.
- The COMPLETE6915B old `RATIONAL-REPETITION-COUNT-SCREEN.md` under
  `research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-impossibility/nonlinear-counter-lifts/`,
  SHAa21c138332f51f5db48d58374d5745a83b4e896bf585da161729c90761322bd9,
  excludes a literal fixed rational Jordan-counter readout. No such readout
  or hardness simulation is assumed below.

The increment is an explicit terminating EQUALITY decision with independently
varying denominator integers and FIXED algebraic bases. It does not bound all
solutions. The retuned-head counterexample has moving bases and does not
contradict this statement. This bounded source comparison does not establish
historical priority or absence of the result from all literature.

## 2. Decision problem

Given finitely many positive effectively real-algebraic numbers beta_{sti},
effectively real-algebraic coefficients c_{st}, and positive integer lower
bounds nu_i, define, for independently chosen integers n_i>=nu_i,

    F_s(n) = sum_t c_{st} * product_{i=1}^k beta_{sti}^{1/n_i}.

Every root is the unique POSITIVE root. The same vector n serves every F_s.
Given a finite Boolean formula made from F_s(n)=0 and F_s(n)!=0, decide
whether any such n exists and return one vector when it does.

THEOREM. This problem has a total effective algorithm. In particular it
covers finite systems of polynomial equalities/disequalities in positive
algebraic reciprocal roots with separately varying denominator counts.
It does not assert a decision for arbitrary polynomial SIGN inequalities.

The proof consists of a finite radical-ratio partition and the following
elementary unit-fraction decision procedure.

## 3. Rational-linear constraints on unit fractions

LEMMA. Feasibility of a finite Boolean combination of rational affine
linear equalities and disequalities in u_i=1/n_i, n_i>=nu_i, is decidable,
with an integer witness on YES.

Expand the Boolean formula into finitely many conjunctions. Consider one
conjunction A u=b together with L_j(u)!=d_j. Use induction on the number m
of unassigned variables; after a choice, substitute its rational reciprocal
everywhere. With no variables, test rational constants exactly.

If some remaining equality has nonzero right-hand side, choose one,

    sum_i a_i/n_i=b,   b!=0.

If all a_i=0 the branch is impossible. Otherwise any solution satisfies

    |b| <= sum_i |a_i|/n_i.

Hence, for at least one i with a_i!=0,

    n_i <= floor(m*|a_i|/|b|).

Enumerate every such index and every integer in its finite permitted range,
substitute, and recurse. Every possible solution enters some branch. The
number of unassigned variables strictly decreases, so this part terminates.

It remains to handle a branch whose equalities are all HOMOGENEOUS, A u=0.
Solve the rational-linear feasibility problem

    A v=0,  v_i>0,  L_j(v)!=0 for every j with d_j=0.

This is a finite sign split of rational linear systems. A nonempty one has
a rational point v, obtainable effectively; rational points are dense in
its rational affine hull and the inequalities are strict. If no such v
exists, there is no unit-fraction solution either.

Write the selected positive v_i=a_i/b_i in lowest terms. Choose a positive
integer T divisible by every a_i, sufficiently large that

    T >= nu_i*v_i  for every i,
    |L_j(v)|/T < |d_j|  whenever d_j!=0.

There are finitely many rational bounds, so this choice is effective.
Then u=v/T has n_i=T*b_i/a_i in the required positive integer range.
Homogeneous equalities/disequalities are retained by positive scaling, and
the other disequalities hold by the strict displayed bound. This constructs
a solution. The construction also permits every remaining n_i to exceed any
additional supplied common lower bound. No limiting n_i=infinity is used.

Both directions and termination have now been proved for the conjunction;
the finite disjunction proves the lemma. Coefficient signs and cancellations
are allowed: the finite branching estimate used absolute values, not an
incorrect termwise positivity assumption.

## 4. Effective saturated algebraic coordinates

Take a real number field K containing every beta and coefficient, with its
specified real embedding. Let Gamma be the subgroup generated by all beta.
The positive saturation

    Gamma_sat = {g in K, g>0 : g^h in Gamma for some integer h>=1}

is effectively finitely generated and torsion-free. This is the OLD
S-unit/lattice construction: let S be the finite set of prime ideals
supporting the beta. Every saturation element is a positive S-unit. In a
basis of that group, take the rational span of the integer coordinate
columns of the beta and intersect it with the ambient integer lattice.
Smith normal form supplies a primitive lattice basis. Its positive S-units
g_1,...,g_r form a basis of Gamma_sat, with computable integer coordinates
for every beta. No unproved GRH/unit-group output or logarithmic zero test
is part of this input.

For clarity, effectiveness of the positive S-unit basis can be acquired by
the standard finite-index construction already given in the reused source.
The known rank permits enumeration until a full-rank logarithmic/valuation
tuple is certified by a NONZERO determinant enclosure. Reduction into its
parallelepiped bounds S-valuations and all Archimedean absolute values.
After multiplying by a fixed rational integer, a computable finite
integral-basis box contains all quotient representatives. Enumerating those
supplies generators for the full group. Exact algebraic product relations,
their known kernel rank, lattice saturation and Smith normal form extract
a basis. Positivity at the chosen embedding removes the only real torsion,
-1. This repeats the established acquisition argument, not a new algorithm
implementation or claimed backend execution.

For q in Q^r, the unique positive value g^q lies in K if and only if q is
integral. The forward direction follows because some power of g^q lies in
Gamma, so membership in K puts it in Gamma_sat; uniqueness of coordinates
in its free basis then gives q in Z^r. The reverse direction is immediate.
Uniqueness for rational coordinates follows by clearing denominators and
using multiplicative independence of the basis.

## 5. A finite radical-ratio partition

Take the union of the radical monomials in ALL F_s, assigning coefficient0
when one is absent from an F_s; combine duplicates if desired. Index this
finite set by t. Put u_i=1/n_i. In the saturated basis each monomial is

    M_t(u) = g^{v_t(u)},   v_t(u)=sum_i a_{ti}*u_i in Q^r,

where all coordinate vectors a_{ti} are known integers. Constants can be
included using the zero vector. Rank r=0 gives M_t=1 and is decided directly
by algebraic coefficient arithmetic.

For each coordinate h choose an integer bound

    B_h >= max_{t,t'} sum_i |a_{ti,h}-a_{t'i,h}|.

Because 0<u_i<=1, every integral vector v_t(u)-v_{t'}(u) is in the FIXED
finite box product_h[-B_h,B_h]. Thus every possible pair of K-proportional
monomials has one of finitely many rational-linear descriptions

    v_t(u)-v_{t'}(u)=z,  z in that box.

Enumerate partitions of the monomial index set into proposed proportionality
classes. In each class choose a representative t0 and enumerate the possible
integral differences z_t=v_t-v_t0, setting z_t0=0. Impose these equalities.
For indices in different classes, exclude EVERY integral vector in the box
as their difference. Each exclusion is a finite disjunction of rational
linear disequalities. Inconsistent choices are harmless and are rejected
by the unit-fraction lemma. Every actual n induces one enumerated choice.

In a fixed choice, the contribution of class C to F_s is

    M_t0(u) * A_{s,C},
    A_{s,C}=sum_{t in C} c_{st}*g^{z_t} in K,

where an absent coefficient is zero. Every A_{s,C} is an EXACT algebraic
constant, independent of the remaining integers.

Representatives of different classes are linearly independent over K.
Each has some positive integer power in K, and their pair ratios are
outside K by the constraints. Apply Carr--O'Sullivan, Theorem1.1 for REAL
field extensions, with the elementary one-element case included. Therefore

    F_s(n)=0 iff A_{s,C}=0 for EVERY class C.

This uses the classical pairwise-to-joint radical independence theorem,
not a new transcendence result. Its statement and Section2 proof were read
at https://arxiv.org/html/math/0703522v2 . No complex root choices or
root-of-unity substitutions are permitted.

Evaluate the requested Boolean formula using these decidable algebraic
class sums. Discard choices where it is false. For every remaining choice,
apply Section3 to its rational-linear constraints on the SAME u vector.
There are only finitely many choices, and each test terminates. A successful
one returns integers n_i and the corresponding exact algebraic roots.
If none succeeds, all integer vectors are excluded. This proves the theorem.

## 6. Consequences and exact G3 boundary

The procedure supplies a total one-witness bound for THIS root-equality
problem: on YES return the maximum count in its returned vector, on NO
return0. It does not bound every solution. For example,

    (2^(1/n_1))^2 = 2^(1/n_2)

has all n_1=2*n_2, with arbitrarily large solutions; the method can return
(2,1). This is a hand example, not a computational check.

The mechanism removes a common-denominator requirement when all algebraic
bases are supplied and the requested constraints are equalities/disequalities.
It does NOT decide:

- polynomial SIGN inequalities in the reciprocal roots;
- arbitrary real exponents;
- physical heads or hidden per-slot base vectors that vary with n;
- unknown original-source reconstruction, menus or the complete joint fibre;
- the several-log Phi=0 predicate on the original cone-promised inputs.

The16October successor's independent primitive multiplicities have types
retuning on one fixed complete source input. Those unknown type outputs
cannot be replaced by individually supplied fixed algebraic bases. Even a
necessary root equality is not sufficient physical source admission. Any
use as an original YES/NO engine must prove the exact source equivalence
and retain natural strictness, IDs, chronology, registers and one bank.
No such full-source supplier is acquired here.

Original G3 remains ACTIVE and unresolved. The next missing implication is
source-complete acquisition of the required fixed-base/equality description,
or a genuinely different all-input bound/NO mechanism; this theorem is not
that acquisition under a different name. There is no new cap/rank ladder,
source experiment, review obligation on completed work, owner transfer,
worker/chat, local Git action or held-job replay.

## 7. Source and evidence record

The companion SOURCE-STATUS.json preserves the separate mathematical, review,
formal and implementation axes. It is a source-status record for this one
claim, not a second master registry. Author completion is PROVED (not Lean
formalized); independent review and implementation were not performed.

Immutable prior sources actually compared:

- [Accepted common-denominator predecessor](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/handoffs/2026-10-16-codex-g3-unreviewed-source-copy-001/INPUT-RADICAL-BOUND-AND-FULL-SOURCE-TEST-03.md) and its [scoped hand review](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-16-dot-g3-radical-review-0055z/REVIEW.md).
- [Later retuned-type/primitive-multiplicity successor](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/handoffs/2026-10-16-codex-g3-primitive-multiplicity-increment-005/ONE-TYPE-BOUNDEDNESS-AND-PRIMITIVE-MULTIPLICITIES-07.md).
- [Classical real radical independence, Carr--O'Sullivan Theorem1.1](https://arxiv.org/html/math/0703522v2). The classical theorem supplies radical independence; it is not claimed as a new result.

The exact increment is the finite class partition plus the terminating
unit-fraction recursion for independently chosen denominators. Historical
priority of that combination has not been established. No mathematical
experiment, implementation, compiler, QE instance or new model job was run.
