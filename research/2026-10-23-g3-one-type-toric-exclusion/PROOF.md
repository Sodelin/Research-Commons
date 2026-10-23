# Strict two-atom toric exclusion and total one-type COMMON decision

23 October 2026. Existing G3 owner. Stable key G3-ARITH-ONE-TYPE-TORIC-01.
**PROVED (not Lean formalized).** Complete author hand proof below;
independent correctness review has not been performed. No elimination,
Puiseux computation, source producer, RCF/QE instance, compiler or native
job was executed. Classical tropical elimination and the already accepted
radical bound are reused. Historical priority is unassessed.

This completes the supplied six-coordinate repeated-ONE-type problem,
including its formerly undecided all-identities-zero alternative. It is
not a full G3 attack or an original all-input recognition theorem. Unknown
slot values, changing types, independent multiplicities, original core
coverage and the unrestricted terminating-NO requirement remain separate.

## 1. Prior-solution comparison and the exact difference

The scientific source pin is Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6.

The closest predecessor is
[INPUT-RADICAL-BOUND-AND-FULL-SOURCE-TEST-03.md](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/handoffs/2026-10-16-codex-g3-unreviewed-source-copy-001/INPUT-RADICAL-BOUND-AND-FULL-SOURCE-TEST-03.md),
25098B/SHA256
97987236e5c6f5429d2f597ff1ebd5b34dac7078ff56515122483524a5ad968e.
Its complete body had been read; sections3--5 were reread for this proof.
Its later complete scoped
[review](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-16-dot-g3-radical-review-0055z/REVIEW.md)
is5446B/SHA256
179b0a86bdbc37816f971cf5fe072c0258071e47a5c205ae85c0852897468af4.
That accepted supplier already decides whether a polynomial vanishes
identically on m^s, and bounds n effectively whenever one defining
polynomial does not. It explicitly does not decide strict feasibility
when every defining polynomial vanishes identically. Neither its grouping
test nor its radical/height argument is newly derived here.

The later actual successor is
[ONE-TYPE-BOUNDEDNESS-AND-PRIMITIVE-MULTIPLICITIES-07.md](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/handoffs/2026-10-16-codex-g3-primitive-multiplicity-increment-005/ONE-TYPE-BOUNDEDNESS-AND-PRIMITIVE-MULTIPLICITIES-07.md),
20193B/SHA256
5c5cd7e670d670d528d0a8414ec39748e37db467e84c4d1b18f25b20056f9916.
Its complete body had been read; sections1--5 and its exact effective-cutoff
disclaimer were reread here. Its completed qualitative finiteness proof is
reused, not reopened. It expressly supplies no effective bound on the
identity exception. Its independent-count retuning construction has a short
witness for the same input and is not a counterexample to a one-witness H.

The new implication at this use-site is that the exceptional algebraic
torus cannot contain ANY strictly log-convex vector at these seven moment
indices. Consequently it contains no strict repeated-two-arm data at all.
The old effective nonzero-identity algorithm is therefore exhaustive here.
This is stronger than the two inspected predecessors at this exact scope;
it makes no claim of novelty in tropical or moment theory.

All retained local audit/continuation archives and relevant authored notes
were searched by the literal one-type/toric/tropical/log-convex aliases.
The bounded matching G3 filename inventory at the pin led back to03,07
and the different rational Jordan-repetition screen. That is a bounded
source comparison, not an assertion of absence from the entire literature
or corpus. Main719b8340... through8dd6b492... adds the reader/intake changes
and scope reconciliation, not a new arithmetic proof at this use-site.

## 2. Exact decision problem

Put

    E={0,1,3,6,10,15,21},  Lambda=E minus {0},  m_0=1.

Input consists of six effectively real-algebraic numbers m_lambda. Decide

    exists n>=1, 0<A,p,q<1, for EVERY lambda in Lambda:
        m_lambda=A^lambda*(1-p+p*q^lambda)^n.             (T)

The SAME n,A,p,q serve every coordinate. The normalized coin p weights the
q arm in this formula; a caller must transport its original ordered-parent
convention explicitly. This statement does not change the inherited
compiler convention parent0 probability=1-native gamma.

The inherited source realization of(T) is reused. Positive ordinary
baseline and two positive arm durations remain strict. The six values are
SUPPLIED complete slot coordinates, not six newly licensed observations
of an arbitrary original graph. One declared repeated type is part of
this subproblem; no equality constraint is imposed on otherwise free fresh
slots of the original recognition problem.

Define

    F_lambda(b,p,q)=b^lambda*(1-p+p*q^lambda),

and let V be the complex Zariski closure of this image, intersected with
the output torus (C*)^6. The closure of the strict real cube is the same
algebraic image closure: a polynomial pullback vanishing on that real open
cube is identically zero. Its rational ideal is computed, in principle,
by the OLD elimination prescription. No computation of that ideal is
claimed here.

A function w:E->R is strictly concave if for every i<j<k in E,

    w_j > ((k-j)*w_i+(j-i)*w_k)/(k-i).                  (SC)

The indices themselves are the numbers in E. In particular, three
collinear sampled points violate(SC), even when they are not adjacent.

## 3. Classical tropical imports and the image-closure issue

Work over the algebraically closed Puiseux field

    K=union_(r>=1) C((t^(1/r)))

with v(t)=1 and the minimum convention for valuations. Only rational
valuation vectors are needed. We use two classical facts: rational points
of the tropicalization are valuations of K-points; and coordinate
projection of a tropicalization equals the tropicalization of the Zariski
closure of the projected image. These are Theorem2.3 and equation(1.3)
in Sturmfels--Tevelev,
[Elimination Theory for Tropical Varieties](https://arxiv.org/pdf/0704.3471).
The actual statements, their setup and the graph-of-parametrization
application were read. Their multiplicity theorem and software are not
required or rerun.

Here the graph is the closed subvariety W of the ten-dimensional torus
with coordinates b,p,h,q,(x_lambda) defined by

    p+h=1,
    x_lambda=b^lambda*(h+p*q^lambda), lambda in Lambda. (G)

It is irreducible, being the graph over the nonempty open parameter set
where all the displayed coordinates are nonzero. Its projected image is
dense in V. Tropical projection followed by the K-point fact therefore
implies: EVERY rational w in Trop(V) is the output valuation of some
actual b,p,h,q in K* satisfying(G). Removing a closed parameter boundary
does not silently assume that every point of V has an ordinary finite
parameter preimage. The tropical projection theorem, applied to W, is
the precise closure/lifting supplier used here.

For context, Cueto--Lin's
[Tropical secant graphs of monomial curves](https://arxiv.org/pdf/1005.3364)
describes the corresponding complex secant tropicalization. Its opening
definitions, Theorem1.1 and the root-of-unity intersection description
were inspected. The complex tropicalization is larger than the naive
minimum of two affine lines. We do NOT replace it by that naive set; the
cancellation cases below are essential. No complete rereview of that
paper or new tropical-secant classification is claimed.

Theorem4.2 and its proof in Blekherman--Rincon--Sinn--Vinzant--Yu,
[Moments, sums of squares, and tropicalization](https://doi.org/10.1112/jlms.70311),
were also inspected at their actual scope: they concern moment CONES
with arbitrary positive support measures. They are not a fixed-two-atom
complex-image lifting theorem. Classical moment log-convexity is reused.

## 4. No strictly concave valuation vector in Trop(V)

**Lemma.** There is no rational w in Trop(V) for which w_0=0 and(SC)
holds on E.

Proof. Lift w using section3. Write a=v(b), c=v(q) and h=1-p. Then

    w_lambda=a*lambda+v(h+p*q^lambda),  w_0=0.           (1)

We exhaust every possible valuation and residue of these COMPLEX
parameters. Strict concavity is invariant under subtracting a*lambda.

**Case1: v(p)=B>0.** Then v(h)=0. Except possibly at the single sampled
index satisfying B+c*lambda=0, formula(1) is

    w_lambda=a*lambda+min(0,B+c*lambda).

If c=0 there is no tie. Otherwise discard the at most one tie, since a
complex cancellation there can raise the valuation. At least six of the
seven indices remain on two affine lines. At least three lie on one
line, contradicting(SC). This argument includes lambda=0, where h+p=1
and no tie occurs.

**Case2: v(h)=B>0.** Here v(p)=0. Except possibly at one tie B=c*lambda,

    w_lambda=a*lambda+min(B,c*lambda).

The same six-indices/two-lines argument applies, again including0.

**Case3: v(p)=v(h)=0 and c!=0.** For every positive lambda the same
term dominates: h if c>0, p*q^lambda if c<0. All six positive indices
are collinear, which is impossible under(SC).

**Case4: v(p)=v(h)=c=0.** Let p0,q0 be their leading coefficients.
Here p0 is neither0 nor1. Cancellation at a positive index requires

    q0^lambda=(p0-1)/p0=:z0,   z0!=0,1.                (2)

Every uncancelled index has w_lambda=a*lambda. If q0 is not a root of
unity, at most one positive index satisfies(2). If q0 has order d>1,
the cancelled indices belong to ONE residue class modulo d. No five of
the six positive indices in Lambda lie in a residue class modulo d>1.
Indeed, after deleting respectively1,3,6,10,15,21, the differences from
the smallest remaining index are

    (3,7,12,18), (5,9,14,20), (2,9,14,20),
    (2,5,14,20), (2,5,9,20),  (2,5,9,14).

Each list has gcd1. If d=1 then(2) has no solutions because z0!=1.
Thus in every case at least two positive indices are uncancelled.
Together with0 they give three points on w_lambda=a*lambda, contrary
to(SC). Raised valuations at the cancelled indices cannot repair that
three-point contradiction.

**Case5: v(p)=v(h)=B<0 and c!=0.** In this case h has leading
coefficient opposite to p's. At EVERY positive lambda one term strictly
dominates, giving

    w_lambda=(a+min(0,c))*lambda+B.

All six positive indices are collinear.

**Case6: v(p)=v(h)=B<0, c=0 and q0!=1.** Write

    h+p*q^lambda=1+p*(q^lambda-1).

Whenever q0^lambda!=1 the valuation is B, so w_lambda=a*lambda+B.
There are at least two such positive indices. This is immediate for a
non-root-of-unity q0. For order d>1, index1 is one, and another exists
because gcd(3,6,10,15,21)=1. Take two such indices r<s. Their middle
point relative to0 and s satisfies

    w_r=a*r+B < a*r+B*r/s=(r/s)*w_s,

since B<0. This violates even weak concavity. No assumption about any
cancelled index was used.

**Case7: v(p)=v(h)=B<0, c=0 and q0=1.** If q=1 exactly, every
coordinate is ordinary and affine. Otherwise put delta=q-1 and
u=v(delta)>0. Characteristic zero gives, for every fixed positive lambda,

    q^lambda-1=lambda*delta+terms of valuation at least2u.

If B+u<0, every positive output valuation is a*lambda+B+u.
If B+u>0, every positive output valuation is a*lambda. Either is affine
on all six positive indices. If B+u=0, the leading coefficient is
1+lambda*d, where d is the nonzero leading coefficient of p*delta.
It vanishes at at most one positive index. All other indices, including0,
have valuation a*lambda, so there are at least three collinear points.

The relation p+h=1 allows only: v(p)>0; v(h)>0; both valuations zero;
or equal negative valuations. Hence these cases are exhaustive. Each
contradicts(SC), proving the lemma. QED.

This proof includes poles, coalescing atoms and nonreal root-of-unity
cancellations. Merely tropicalizing the positive parameter formula by
minimum would not have justified the lemma for the algebraic closure.

## 5. Toric exclusion of the identity exception

**Theorem.** If a positive vector m, with m_0=1, has log m strictly
convex on E, then the entire curve m^s is NOT contained in V. Therefore
at least one rational defining polynomial of V has nonzero grouped
evaluation along m^s.

Proof. Define the integer relation lattice

    L={u in Z^6 : m^u=1}.

It is saturated, since all coordinates of m are positive. The Zariski
closure of {m^s:s in R} in the complex torus is the connected subtorus

    T={x in(C*)^6 : x^u=1 for every u in L}.            (3)

For completeness, a Laurent polynomial evaluated on m^s groups by the
values m^alpha. Distinct real exponentials are linearly independent, so
it vanishes identically exactly when the sum of coefficients within every
L-coset is zero. That is precisely the lattice ideal defining(3). This
uses no conjecture about algebraic independence of logarithms.

Assume m^s is contained in V. Then T is contained in V. The rational
linear space

    L_perp={w in R^6 : u dot w=0 for all u in L}

contains -log m, which is strictly concave on E with value0 at0.
Strict concavity is a finite collection of OPEN strict linear conditions.
Rational vectors are dense in this rational linear space. Choose a
rational w in L_perp still satisfying all these inequalities.

The Puiseux point x_lambda=t^w_lambda lies in T by(3), and hence in V.
Its valuation is w. The lemma excludes this strictly concave rational
valuation, a contradiction. Thus the curve is not contained in V.

If every generator of the rational defining ideal vanished identically
on m^s, the whole curve would lie in V. At least one generator therefore
does not. QED.

Note the direction: log m is strictly CONVEX; its negative supplies the
strictly CONCAVE tropical vector. Interchanging these signs would make
the argument false. No logarithm sign/zero oracle enters the algorithm.

## 6. Complete effective algorithm for(T)

Every solution of(T) obeys strict log-convexity. Indeed the function

    g(lambda)=log(1-p+p*q^lambda)

has

    g''(lambda)=(log q)^2*p*(1-p)*q^lambda
                  /(1-p+p*q^lambda)^2 > 0.

Multiplication by n>0 and addition of lambda*log A preserve it.
This is the classical strict two-point moment/Hölder property.

It is exactly decidable on algebraic input without evaluating logarithms.
For every i<j<k in E check

    m_j^(k-i) < m_i^(k-j)*m_k^(j-i).                   (LC)

All exponents are integers. The total decision procedure is:

1. Reject if any supplied m_lambda is outside(0,1), or any(LC) fails.
   These are necessary strict-source conditions, so this is genuine NO
   for(T), not rejection of a closure point merely for being a boundary.
2. Compute the fixed rational elimination ideal of the image F and a
   finite generating set, using the OLD effective construction. For each
   generator P group the finitely many monomials by the exact algebraic
   values beta=m^alpha. This uses exact algebraic arithmetic.
3. Section5 guarantees that at least one generator has a nonempty grouped
   expression

       P(m^s)=sum_(j=1)^J c_j*beta_j^s,

   with distinct positive algebraic beta_j and nonzero rational c_j.
   If J=1, no positive n can solve(T); return NO immediately.
4. Otherwise invoke the ALREADY PROVED03 radical/height bound in the
   effective real field K=Q(m_lambda). Compute N such that for n>N
   every ratio(beta_i/beta_j)^(1/n), i!=j, is outside K. The accepted
   positive-radical independence theorem then gives

       P(m^(1/n))!=0 for every n>N.

   Thus EVERY strict(T) witness has n<=N. No new radical or height
   theory is needed. For rational data the old finite prime-valuation
   bound may be used instead.
5. For n=1,...,N decide the SAME-parameter strict polynomial equations
   of(T) by RCF over the effective algebraic coefficients. If one is
   feasible return n and its ONE joint algebraic A,p,q witness. If none
   is feasible return NO.

Every step terminates. Step3 is guaranteed by the toric exclusion, not by
an unbounded search for a nonzero identity. Defining an arbitrary default
N=0 on the already rejected inputs makes the resulting branch count bound
a total input-computable function. Any additional explicitly supplied
finite polynomial source conditions on this declared repeated template
can be retained in step5; the necessary count bound remains valid.

The equivalence with one-cell roots is exact: b=A^(1/n) is positive, and
conversely A=b^n. One bank serves all six coordinates. Ordinary equal-arm
data can be handled separately if the caller admits q=1: test
m_lambda=m_1^lambda and use a single ordinary representative. That case
is excluded by the strict q<1 predicate(T), rather than incorrectly
claimed to have bounded ALL ordinary presentations.

## 7. What is complete, and what is not supplied

Complete at HAND scope:

- The two-atom complex-image valuation exclusion at the FIXED seven indices.
- No strictly log-convex input lies in the all-identities-zero alternative.
- Total exact YES/NO and an effective count bound for the full declared(T)
  problem on all effectively real-algebraic six-coordinate inputs.

Classical/retained reuse: source realization, image elimination, exact
grouping, positive-radical independence, effective height gaps, fixed-n
RCF, moment log-convexity and tropical projection/valuation realization.
Qualitative one-type boundedness is not counted again as new progress.

No general G3 endpoint follows. In particular:

- Original observed rows constrain F_core(theta,unknown slots)=y; the hidden
  slot vector m is not generally supplied or forced algebraic by the rows.
- A product of changing two-arm types with independent integer counts is
  not the nth power of ONE point in this three-dimensional variety.
- Neither an input-controlled finite template list nor a finite critical
  type/primitive-multiplicity bound is obtained.
- No I/BOTH source equality, new legal observation, arbitrary-core decoder,
  chronological compression or complete all-size NO certificate is added.
- This is not homogeneous-log zero testing, and it does not decide the
  retained rank-five source-faithful purity stress.

The core implication to unrestricted total G3 therefore remains unresolved.
This completed supplier should be reused whenever this EXACT repeated-type
problem arises, without reopening it because Lean, implementation or an
independent review is absent. No execution or peer review job is selected
by this note. Existing owners, source semantics and held/USED/UNKNOWN
actions remain unchanged; no local Git action has been taken.
