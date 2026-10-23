# A regular source bank has bounded algebraic degree independently of word length

23 October 2026. Existing G3 owner. Stable key G3-REGULAR-FIELD-DEGREE-01.
**PROVED (not Lean formalized).** Author-complete hand proof; independent
correctness review and implementation are unperformed. No source producer,
symbolic experiment, QE instance, compiler, Lean or native job was run.
The argument is classical rational specialization, constant-rank/implicit-
function theory and affine Bézout, applied to the actual source compiler.
No historical novelty claim is made.

This is a regular-branch supplier for the ORIGINAL joint source grammar,
including I/BOTH and protected finite source relations. It is not a full
G3 attack or a count/height bound. The singular-word extension is not
asserted. A concrete nongenealogical counterexample below explains why
that extension cannot follow just from bounded polynomial degree.

## 1. Prior comparison and the exact remaining degree question

The retained source/path equivalence is
[REDUCTION.md](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md),
10579B/SHA256
7b789a77b6e15fd8ab7e2c5050021f2d162ddb897285eb34fbabe900ca1f1c24.
Its COMPLETE body was reread. It supplies a finite input-dependent
protected core catalogue, a polynomial joint compiler, independent fresh
append tuples and two-way reconstruction of every finite legal path.
Fixed-length algebraization is already proved; no count bound follows.

Closest regular-witness predecessor, at Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6:
[ATTEMPT-2-ALTERNATIVE-PRESENTATIONS.md](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/ATTEMPT-2-ALTERNATIVE-PRESENTATIONS.md),
17890B/SHA256
37c7cf1641de6a6f3cadefc6a9eda8adc51d4d55ee74e85ff8a2919db736f51f.
Its COMPLETE body was read. Section2 retains a regular alternative from
the old interior-absorption proof and then uses fixed-graph RCF to obtain
an algebraic tuple. It does not give a field-degree bound uniform in the
number of fresh cells. Its source-interiority and universal-alternative
questions remain different statements and are not reopened here.

The later actual full-source successor is attempt5's
[COMPLETE-INTEGER-WITNESS-ATTEMPT.md](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/attempt-5/COMPLETE-INTEGER-WITNESS-ATTEMPT.md),
15188B/SHA256
b4e5e80fb810048ffa819fc330775813e2df5b0e906b647c6b85cd05f1b97d7a,
and its actual complete root review
[ROOT-FOURTH-ROUND-ALGEBRAIC-NORMAL-AND-WEAK-CELL-REVIEW.md](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-08-codex-g3-g4-full-shot-1253z/integration/ROOT-FOURTH-ROUND-ALGEBRAIC-NORMAL-AND-WEAK-CELL-REVIEW.md),
9784B/SHA256
b8eb8951dced216681148e3bf4d329b6649b06a68c2d4279fa54cd0a3bc8c4de.
Both COMPLETE bodies were read. Their one-presentation algebraic selection
is accepted at its conditional legal-chart scope. Their varying-normal and
whole-fibre disclaimers remain binding. They provide no general bound on
degrees/heights of arbitrary critical-source alphabets.

The newly completed one-type toric count decision and the independent
reciprocal equality theorem are different suppliers. Neither is used to
obtain the degree statement here. The recent Habegger import check found
that a height bound alone did not supply a source-wide degree/count bound.
The present statement supplies a degree bound ONLY on a regular branch;
it does not repair that import on singular or unknown source fibres.

All retained local audit/continuation archives were searched for the
field-degree/regular-witness/rational-specialization aliases before this
derivation. The exact matching predecessor and later successor above were
read. This is not an exhaustive absence or historical-priority claim.

## 2. A polynomial specialization lemma

Let K be an effective real number field with its chosen embedding in R.
Write a parameter vector as (theta,u), where theta has s coordinates and
u has arbitrarily many free coordinates. The static legal chart is, locally,

    h_1(theta)=...=h_g(theta)=0,
    rank(dh)=g,                                           (1)

together with strict open conditions. Its defining equations are over K.
The u coordinates have only open domain conditions; any protected equality
has already been placed in theta or built into the parameterization.

Let F(theta,u) in R^d be a polynomial map over K. Suppose every h_i and
every coordinate of F has degree at most M in EACH individual raw parameter.
The number of u coordinates may be arbitrarily large. The TOTAL degree of
F may therefore be large; it is not assumed bounded by M.

Suppose a real legal point z0 satisfies

    F(z0)=y in K^d,

and F, restricted to the chart(1), has LOCALLY CONSTANT rank r at z0.
This is the regularity hypothesis. It is automatic at a full-row-rank
point r=d. It is not implied by merely evaluating the rank at one point.

**Lemma.** There is an arbitrarily close legal point z* with F(z*)=y,
the same local rank, and

    [K(z*):K] <= (R*M)^R,   R=g+r,                       (2)

when R>0. For R=0 the degree bound is1. Moreover all but at most r of
the FREE u coordinates can be chosen rational. Every coordinate of z*
belongs to the SAME real algebraic extension, not separate row fields.

Proof. The full Jacobian consisting of dh followed by dF has rank g+r
at z0. Select r output coordinates F_J such that

    H=(h_1,...,h_g,F_J-y_J)

has Jacobian rank R. Choose a nonsingular R-by-R parameter minor.
The g independent h pivots may be chosen among theta, since h depends
only on theta. Extend these by r parameter columns for the output rows.
Thus at most r chosen columns are u coordinates.

Call the selected coordinates v and all the others w. The implicit-
function theorem gives an open neighborhood of w0 on which H(v,w)=0
has a real solution v=v(w) close to v0, with the chosen determinant still
nonzero. The chart and every strict source inequality remain valid after
shrinking the neighborhood. Choose ALL w coordinates rational in that
neighborhood. Rational density is used in the free PROJECTION coordinates,
not as a false claim that a constrained algebraic fibre has rational points.

These solutions match every output, not only the r selected ones. To see
this, use locally constant rank: on a sufficiently small chart neighborhood
the image of F is an r-dimensional smooth manifold, and projection to
the selected r output coordinates is a local coordinate chart on it.
Consequently F_J=y_J forces the entire vector F=y there. This also follows
directly from the constant-rank normal form and the inverse-function theorem
on the selected output projection. Rank and the source open conditions
persist on a sufficiently small chosen neighborhood.

After w is fixed rationally, H is a square polynomial system over K in R
unknowns. Each equation has TOTAL degree at most R*M: it contains only R
remaining variables, each with individual degree at most M. The real
solution just constructed is nonsingular, hence an isolated COMPLEX zero
of this square system. The classical affine Bézout bound gives at most
(R*M)^R isolated zeros over an algebraic closure, counted with multiplicity.
The isolated point is algebraic over K, and all its distinct K-conjugates
are isolated zeros of the same system. Characteristic zero is separable,
so the degree of the field generated by its ENTIRE coordinate tuple is
at most that number. This proves(2). Adjoining the rational w adds nothing.
The selected-columns observation proves the claim about at most r free
coordinates. If R=0, the map is locally constant on an open chart and a
nearby rational point works. QED.

The affine isolated-zero bound used here is the classical theorem, for
example TheoremI.2 in Pinaki Mondal's author-hosted
[How many zeroes?](https://pinakimondal.org/wp-content/uploads/2021/12/p1_to_16.pdf).
The actual statement and its algebraically closed setting were inspected;
no claim of reviewing the whole book or a new intersection theorem is made.

## 3. Why the actual source compiler has a uniform individual-degree budget

Fix ONE original finite input and one protected template c from the
accepted source-complete catalogue. Let K include every algebraic input
constant and observation value. Its finite static tuple contains the
protected original parameter sites, all equality-relation endpoints,
initial ordinary slots and any fixed original register/control parameters.

For a finite path w of N legal fresh appends, expand the existing SAME-
source joint polynomial compiler. Write the result F_(c,w)(theta,u_1,...,u_N).
The path's word order, slot choices and original IDs are fixed for this
polynomial map. The same fresh block u_j supplies every paired/configuration
component that uses its one physical cell.

There is a computable individual-degree bound M_c INDEPENDENT of N:

1. Each actual fresh append kernel is a fixed finite polynomial matrix in
   its own survival/inheritance tuple. Include all paired/register components
   and any finitely repeated original program uses when taking its degree
   bound delta_c. No matrix entry is an independently chosen control.
2. Each slot word is a product of these matrices. One fresh tuple occurs
   only in its own factor, or in the fixed finite joint block representing
   its licensed uses. Hence any coordinate of a full slot kernel has
   individual degree at most delta_c in that tuple, regardless of the
   number or order of other fresh factors.
3. The fixed polynomial original response map F_c(theta,(K_s)) has a
   finite degree D_c. Substitution therefore multiplies the individual
   fresh-parameter bound by at most D_c. The static parameters occur in
   this fixed map and initialization, not afresh as a newly synchronized
   coefficient at every unmarked cell.
4. Take M_c to cover D_c*delta_c and the finite static-chart equations.
   Fixed algebraic chart auxiliaries can be included in theta; their number
   and degrees depend on the fixed static domain, not on N.

The untied-fresh-position clause is essential and is already part of the
original source grammar. A new constraint making ONE unknown parameter
repeat at unboundedly many fresh positions could create powers of degree N;
that is not silently added here. Coin values may happen to coincide in a
source; the proof does not constrain different cells' independent original
draws to be the same bit. All finite explicitly protected ties remain.

The finite static semialgebraic domain can be treated on its standard
effective smooth algebraic/Nash charts, with finite algebraic auxiliary
variables where necessary. This is the fixed legal-stratum treatment used
in the retained append-normal argument. Crucially ONLY that input-controlled
static domain is stratified before adjoining the N fresh open blocks.
Its chart dimensions, equation degrees and finite component choices are
input data for the bound. Stratifying the growing N-variable OUTPUT fibre
instead would not give a uniform g and is NOT used.

## 4. Original-source regular-branch consequence

**Theorem.** On any such fixed input-controlled legal chart, suppose some
actual finite original source-word presentation realizes the entire input
and the joint response map has locally constant rank r at that presentation.
It has another realization on the SAME finite graph/path, preserving every
original label, ID, menu, static relation, register and physical tuple reuse,
whose ENTIRE survival/inheritance bank lies in one real extension L/K with

    [L:K] <= max(1,((g_c+r)*M_c)^(g_c+r)).               (3)

All but at most r fresh scalar parameters can be rational. In particular,
at most r fresh cells need parameters outside K; their other scalar values
can also be chosen rational unless selected by the bounded system. This
is not a statement that the remaining rational cells can be deleted.

Proof. Apply the lemma to F_(c,w). Every equality not in the original target
has been retained in the static chart or actual joint parameterization;
all remaining fresh conditions are open and are preserved by the close
specialization. The whole d-dimensional input vector is kept, including
any polynomial cross-use of slot kernels. The same algebraic point serves
all rows, modes and register conditionals. The original two-way source/path
theorem reconstructs exactly that same legal finite word/graph with the
new tuple. Neither chronology nor the number/order of cells is changed.
Equation(3) is independent of its original N. QED.

For a finite supplied/input-computed static chart catalogue, maximize the
right-hand side over its c and 0<=r<=d. This produces a TOTAL input/chart-
computable field-degree bound for EVERY input having a regular source-word
witness of this kind. No search for N is needed to compute that degree bound.
It is not a promise or an algorithm declaring that such a witness exists.

When applying the statement to an original source before protected
normalization, regularity must be transported through the actual source
parameter map or checked on its normalized word chart. Pointwise equality
of readouts alone is not asserted to preserve differential rank. The safe
statement above is existence of a REGULAR original source-word presentation.

COMMON scalarization is not used in the proof. The source applicability
therefore includes the actual INDEPENDENT and jointly requested BOTH maps
whenever their full polynomial block is the retained compiler. This does
not identify two separate marginal kernels or refresh any carried register.

## 5. What the witness procedure can and cannot do

For a fixed path and selected static chart, one can test the rank conditions
and source equations by the existing finite RCF machinery. Local constant
rank can be expressed by a neighborhood condition with polynomial Jacobian
minors, or supplied by a known constant-rank chart. Rational free-coordinate
tuples can be enumerated; the square polynomial systems and original strict
constraints can then be tested exactly. If a regular witness exists, some
such specialization succeeds. The returned algebraic bank satisfies the
degree bound because of the isolated-zero proof, even though its heights
may be large. No such procedure was implemented or run here.

The field statement concerns the polynomial source coordinates, including
survivals and inheritance probabilities. It does NOT bound logarithms or
assert that population rates reconstructed from logarithmic survivals lie
in L. Original calendar/rate reconstruction retains its existing contract.

The unbounded path enumeration is still just the original YES search.
Giving this search a uniform DEGREE specification neither makes a failed
finite path test NO nor supplies a stopping index. A bounded-degree point
need not have bounded height, and a source may have arbitrarily many
rational cells. Those are separate reasons not to call(3) a word bound.

## 6. Singular extension: a fixed-degree counterexample outside the source model

Bounded individual degrees do not imply a uniform algebraic-degree bound
on arbitrary singular fibres. For every N>=1 use the open cube(0,1)^N and
the single rational polynomial

    P_N(x)=(x_1^2-1/2)^2
                +sum_(i=1)^(N-1)(x_(i+1)^2-x_i)^2.     (4)

Its TOTAL degree is4, and every individual degree is at most4. The fixed
rational target is P_N=0. A sum of real squares vanishes precisely when

    x_1^2=1/2,  x_(i+1)^2=x_i for every i.

Strict positivity picks the UNIQUE bank

    x_i=2^(-1/2^i).

The last coordinate has degree2^N over Q: its reciprocal is a root of
Y^(2^N)-2, irreducible by Eisenstein at2. Earlier coordinates are powers
of x_N, so the whole bank has exactly that degree. These degrees are
unbounded despite one equation, fixed coefficients and degree4.

At the realizing point every derivative of P_N is zero. At nearby points
the rank is generically1, so rank0 is NOT locally constant. The lemma
cannot be applied with r=0. If the zero fibre is itself declared a stratum,
its codimension is N; that reintroduces the growing dimension into R.

This is a generic polynomial counterexample, NOT an embedding in the
genealogical compiler, an original source NO or an undecidability theorem.
It blocks the invalid extension of this proof to all critical words by
bounded polynomial degree alone. It supplies no lower bound for an actual
G3 witness and does not reopen any completed source theorem.

## 7. Exact disposition toward full G3

Complete here: on input-controlled regular original source-word charts,
one joint algebraic field degree and the number of nonrational fresh scalar
parameters can be bounded independently of word length. This makes the
older fixed-graph algebraization statement quantitative at this receiver.
Its proof uses classical tools; the regular alternatives themselves retain
their old authorship and acceptance.

Still unsupplied: existence of a regular alternative for every relevant
realizable fibre; a source-specific critical-word degree theorem; heights
or rational-denominator bounds; effective count/word compression; and
complete NO coverage over every original core and shared bank. The older
attained-boundary and global-normal limitations remain governing. This
supplier neither refutes those limitations nor proves the universal
alternative-presentation assertion.

Even combining(3) with a toric height theorem would require the actual
source-derived algebraic family, its hypotheses, exceptional-fibre control
and a valid factor-count implication. None is assumed. The entire original
G3 goal stays active and unresolved. This is a proved component, not a new
full attack, and missing implementation/review/Lean does not reopen it.
