# Projective gap bounds and uniform forest spectral projectors

Stable source key: G3-PROJECTIVE-SPECTRAL-01.

23 October 2026. Existing G3 owner, Codex/OpenAI.
PROVED BY HAND (not Lean formalized). Author self-audit complete;
independent correctness review not performed. No scientific source,
numerical/symbolic control, QE, compiler, native build or model run.

This is a supporting structural theorem for the ACTUAL private current-root
operator. It is not a source-word bound, a new full G3 attack, or original
G3 closure. All-input recognition and terminating NO remain unresolved.

## 1. Exact finite projective domain

Fix ANY finite cap m>=1. For r=1,...,m let L_r be a probability law on rooted
unranked binary forests on r distinctly labelled CURRENT ROOT TOKENS.
Require:

1. Exchangeability of those current tokens.
2. Deleting tokens, pruning their branches and suppressing unary vertices
   restricts L_r to the SAME law L_s on every selected s-token subset.
3. Applying L_r to an entering forest with r current roots grafts its old
   opaque trees back onto the tokens. A same-count outcome leaves the
   entire entering forest literally unchanged. No roots vanish or split.

The finite family through m suffices; an unproved all-cap extension is not
a premise. Internal leaf counts inside old opaque trees are NOT token
weights. Population locations, exposed register updates and time/history
decorations with same-count changes are outside this operator contract.

Let K be the resulting stochastic matrix on the COMPLETE finite forest
carrier, graded by current-root count. Its r-th diagonal block is b_r I,
where b_r is L_r's probability of no merger. Write K_(r,s) for the block
from r roots to s roots and use the maximum absolute row-sum norm. An
optional empty-input identity block stays isolated. We allow all boundary
values, including b_r=0 and ties b_r=b_s.

Actual fresh unexposed private COMMON and INDEPENDENT words satisfy this
contract by the retained current-root, restriction and opaque-graft laws.
Their finite-cap endpoint limits also satisfy it: these are closed linear
consistency/grafting and probability constraints. This does not identify
an arbitrary full original Code/register kernel with this smaller operator.

## 2. Prior comparison and the exact increment

The COMPLETE strict-source predecessor at Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6 was read:

research/2026-10-06-dot-g3-critical-arithmetic-census-1148z/route-audit/
PFA-UNDECIDABILITY-APPLICABILITY.md,
6900 B/SHA256
6f6ab647259a71eda3613ef88f9bec7ee0e3fa292644a5f34674368ba61e1585,
Git blob 11047dbea81da3983e238219b741a3e3b0ae7e1a.

It ALREADY proves 1=b_1>...>b_m>0 and square-free source semisimplicity for
a strict word. It expressly does not assert its argument for boundary
cells. Its source representation, scalar grading and strict-word theorem
are reused, not reproved as new.

The later COMPLETE9October finite-fibre decoder proof and actual root-review
receipt, already restored to the current G3 index, were compared:

research/2026-10-09-dot-g3-reviewed-source-coding-1541z/
FINITE-FIBRE-SEMIALGEBRAIC-COUNTER-OBSTRUCTION.md,
11521 B/SHA31276ccc8373b782808078646e15f7bc475cd1c0c022a168f81fe4a02776c83e;
ROOT-FINITE-FIBRE-REVIEW-RECEIPT.md,
848 B/SHAda46c53203f4b2b36ee51d005f3aea97754467b46b2312bf8e6d0e461837f7ca.

That completed fixed-source counter obstruction remains valid. It supplies
neither a uniform bound for arbitrary source spectral projectors at nearly
coincident diagonals nor the boundary-tie argument below.

Also read COMPLETE at the same pin:

- research/2026-10-10-dot-g4-sign-free-inverse-estimate-1116z/
  SIGN-FREE-PROJECTIVE-INVERSE-BOUND.md,8309 B/SHA
  93fd4844b11a77c812535dc9e490137e2a1138542e8634e08f526a18fb1f2601,
  its4702 B INDEPENDENT-NORM-REVIEW.md/SHA
  407b6c1ece6290d297310c422dc05c9af431fa138ff81763111553db755892b3,
  and4013 B independent/INDEPENDENT-SOURCE-REVIEW.md/SHA
  e5c5b64e7e6886e73f45aaab51b216ff98929c064ac479764dcd2b2d4fcd6285.
  The representative-subset and shape-independent chain methods are OLD.
  Their raw inverse estimate with a small-diagonal factor is reused.
- research/2026-10-13-codex-g4-renewed/spectral-bridge/
  FULL-FOREST-GAUSSIAN-BLOCK-BOUND.md,6425 B/SHA
  1aec053b7c547fe5b01989d24fd4558778005619467cd16a48e0c3aec4c47d81.
  Its projector bounds concern the ORDINARY generator with distinct integer
  rates, not every projective coagulation kernel.
- The existing G4 owner's COMPLETE
  MATCHED-DIAGONAL-RELATIVE-INVERSE-BOUND-R1.md was read. Its common-diagonal
  relative inverse norm and the source one-pair identity remain reused;
  they do not assume or prove this arbitrary-kernel projector bound.
- The completed paired cap2 image/lower-count proof and paired cap3 one-cell
  quartic were read at their exact private-interface scope. They do not
  supply an all-arity unequal-arm survival comparison.

Primary context was inspected only at the relevant stated scope:
[Spence, Kamm and Song, Genetics202 (2016), Lemma3 and its proof](https://pmc.ncbi.nlm.nih.gov/articles/PMC4827730/).
That lemma diagonalizes the block-COUNT rate matrix of a Xi-coalescent
assuming distinct total rates. This is established nearby methodology,
not an imported all-forest, boundary-tie or uniform-projector theorem.
The initially attempted author PDF URL returned404 and was not read.
Neither the entire article nor all general-coalescent literature was
reviewed. Classical finite triangular resolvents and interpolation retain
attribution. Historical novelty is unestablished.

The claimed increment is Sections3--6: an exact projective diagonal-gap
majorant and a parameter-independent m! projector bound, INCLUDING ties
and zero diagonal boundary values. Section7 gives its same-tuple private
source use with an observed/internal COMMON pair coordinate. This bounded
retained-source comparison is not an exhaustive prior-absence claim.

## 3. Exact positive decomposition of a diagonal gap

For a realized r-token output forest H, let its output components contain
a_1,...,a_k input tokens. All a_i are positive integers summing to r.
Let e_s(a) be the elementary symmetric polynomial of degree s, zero for k<s.

Choose an s-subset of input tokens uniformly. Its restricted output has
no merger precisely when at most one chosen token belongs to each output
component. Its conditional probability is therefore

    h_s(H)=e_s(a_1,...,a_k)/binom(r,s).

Projectivity gives E h_s(H)=b_s. If H has no merger, h_s(H)=1, and that
event has probability b_r. Thus, for 1<=s<r,

    b_s-b_r = E[1_(H has a merger) h_s(H)].                 (1)

In particular b_1=1>=b_2>=...>=b_m>=0. This is an exact nonnegative
decomposition, with no independence assumption on the selected subsets.

If k>=s, then e_s(a)>=r-s+1. To prove this, merge component sizes until
only s remain: replacing a,b by a+b cannot increase e_s, since the
removed term is a*b*e_(s-2) of the other sizes. At s sizes e_s is their
product, at least r-s+1; repeatedly use a*b>=a+b-1 for integers a,b>=1.
The case s=1 is directly e_1=r.

Consequently, defining

    kappa_(r,s)=binom(r,s)/(r-s+1)
               =r!/[s! (r-s+1)!],

we obtain the ALL-ROOT-COUNT tail and block bounds

    P(s<=number of output roots<r)
       <= kappa_(r,s) (b_s-b_r),

    ||K_(r,s)||_infinity
       <= kappa_(r,s) (b_s-b_r),                 1<=s<r.   (2)

The block bound is valid on the complete opaque-forest matrix: summing
each row over an output-count block is the fresh r-token count law.
No number-of-forest-shapes multiplier is present.

If b_r=b_s, EVERY corresponding off-diagonal transition block vanishes.
This includes zero diagonals. This consequence needs projectivity; scalar
triangularity and stochasticity alone do not imply it.

## 4. Boundary semisimplicity without assuming distinct diagonals

For complex z off the diagonal values, the block triangular inverse has
the finite path formula

    [(zI-K)^(-1)]_(r,s)
      =sum_(r=r_0>...>r_l=s)
          K_(r_0,r_1)...K_(r_(l-1),r_l)
            / product_(q=0)^l (z-b_(r_q)).                 (3)

For r=s the path has length0 and numerator I. This follows by the finite
geometric expansion of the strictly count-decreasing part of zI-K.

A nonzero path product in(3) has STRICTLY increasing diagonal values:

    b_(r_0)<b_(r_1)<...<b_(r_l).

Indeed each nonzero transition block requires a strict gap by(2).
Thus every denominator on a nonzero path has distinct roots. Every
resolvent pole is simple, even if equal diagonal values occur in separate
root-count layers.

A finite matrix whose resolvent has only simple poles is semisimple.
Equivalently, the partial fractions of(3) give

    K=sum_(beta in S) beta P_beta,
    I=sum_(beta in S) P_beta,
    product_(beta in S)(K-beta I)=0,                       (4)

where S is the set of DISTINCT diagonal values and P_beta are the spectral
projectors. These formulas also prove semisimplicity directly. A zero
eigenvalue and the isolated empty-input block cause no Jordan coupling.

This extends the OLD strict-word semisimplicity argument to the entire
finite projective coagulation domain, including actual source closure
operators. It does not assert a common eigenbasis for different K.

## 5. Uniform spectral projector bound

Take a nonzero path r=r_0>...>r_l=s in(3). The residue at beta=b_(r_j) is

    K_(r_0,r_1)...K_(r_(l-1),r_l)
       / product_(q!=j)(beta-b_(r_q)).                    (5)

If the path contains no beta, its residue is0. It cannot contain beta twice.

By(2), its row norm is bounded by the product of the kappa values times

    product_(q=0)^(l-1)(b_(r_(q+1))-b_(r_q))
         / product_(q!=j)|beta-b_(r_q)|.

That last ratio is at most1. For q<j, charge the step gap to
beta-b_(r_q); for q>=j, charge it to b_(r_(q+1))-beta. Every denominator
factor is used once, and each step gap is no larger than its charged
distance. Therefore the residue norm is at most

    product_(q=0)^(l-1) kappa_(r_q,r_(q+1)).               (6)

It remains to sum all decreasing count paths; summing the larger set of
ALL paths is a valid majorant. Put d=r-s>=1 and h_q=r_(q-1)-r_q>=1.
The product in(6) telescopes to

    r!/[s! product_(q=1)^l(h_q+1)!].

For every positive integer h, (h+1)!>=2^h. There are2^(d-1) ordered
compositions of d, so summing over ALL paths from r to s gives at most

    r!/(2s!).                                             (7)

For an r-root input row, add the possible identity diagonal and sum over
s<r. This proves

    sum_H |P_beta(f,H)|
      <=1+(r!/2) sum_(s=1)^(r-1) 1/s! <= r!.              (8)

For r=1 this is1. For r>=2, the last inequality follows from

    sum_(s=1)^(r-1) 1/s! <=2-2/r!.

This elementary bound holds at r=2 and passes from r to r+1 by adding
1/r!; equivalently 1<=2r/(r+1). It also follows by induction from the
factorial series.

We have therefore proved the uniform bound

                    ||P_beta||_infinity <= m!             (9)

for EVERY distinct eigenvalue of EVERY operator in Section1.
No minimum spectral gap, positive parameter margin, source size, common
physical clock or forest-state cardinality occurs.

## 6. Consequences and exact checks by hand

For any scalar function f defined on S, spectral functional calculus gives

    ||f(K)||_infinity
       <=m! sum_(beta in S)|f(beta)|
       <=m*m! max_(beta in S)|f(beta)|.                   (10)

For positive diagonals this yields

    ||K^(-1)||_infinity <=m*m!/b_m,
    ||log K||_infinity <=m*m! (-log b_m).                 (11)

The logarithm is the real principal matrix logarithm. The old projective
inverse theorem is reused; this is an additional uniform spectral proof
and conditioning estimate, not a new physical inverse.

Continuous functions on[0,1] can be uniformly approximated by polynomials.
Equation(10) transfers that approximation uniformly over the entire domain
of Section1. Since polynomial evaluation is continuous in K, f(K) is
continuous through eigenvalue collisions. A supplied effective polynomial
approximation gives the same effective norm estimate without locating a
minimum spectral gap. Logarithms require a positive diagonal lower margin.

Two exact HAND scope checks:

- At cap2, K has rows(1,0) and(1-b,b). Its b-projector has rows(0,0)
  and(-1,1), hence norm2=2!. The uniform bound does not mean orthogonal
  or nonnegative projectors.
- The count matrix with rows(1,0,0),(1-a,a,0),(0,1-a,a), 0<a<1, has
  a nontrivial Jordan block at a. It is triangular and stochastic but
  violates(2), since b_2=b_3=a and its3-to2 entry is1-a>0. It cannot
  be a projective coagulation kernel. No such matrix was called physical.

No matrix script or symbolic package was executed for these checks.
Fractional powers, inverse or logarithm are algebraic/analytic operations;
none is declared a nonnegative kernel or a legal positive source word.
The already completed original-source continuous-power no-lift results
retain their full force.

## 7. Same-tuple COMMON pair control of the complete spectrum

For ONE actual fresh private cell let p=P(parent0), native gamma=1-p,
with arm survivals u,v in[0,1]. Its natural unused-bank COMMON pair
survival is c=p*u+(1-p)*v. Let lambda_r=binom(r,2).

COMMON no-merger probability is

    b_r^C=p*u^lambda_r+(1-p)*v^lambda_r >=c^lambda_r,

by convexity for r>=2. For INDEPENDENT, route each CURRENT token once.
Given routes X_i, put Z_i=u or v for its chosen arm. Its conditional
no-merger probability is the product over unordered token pairs of W_ij,
where W_ij=u or v for a shared arm and1 for distinct arms. Pointwise,

    W_ij >= sqrt(Z_i Z_j).

For r>=3, route independence and convexity with exponent(r-1)/2>=1 give

    b_r^I
      >=[p*u^((r-1)/2)+(1-p)*v^((r-1)/2)]^r
      >=c^lambda_r.                                      (12)

At r=2 use the already retained exact pair identity

    b_2^I-c=p(1-p)(2-u-v)>=0.

The r=1 kernels are identities. Ordinary populations contribute exactly
a^lambda_r in BOTH modes. Diagonals multiply under the actual fresh
source grammar, with one tuple across every row. Hence for ANY finite
strict paired word with natural COMMON pair survival C>0,

    b_r^C >=C^lambda_r,       b_r^I >=C^lambda_r
                       for EVERY1<=r<=m.                 (13)

Equal numerical parameters at different cells do not reuse a bit.
A stored/exposed bank is not newly averaged, and no full-code or
cross-slot interface is inferred without its actual supplier.

Combining(11),(13), each legitimately supplied numerical mode block obeys

    ||log K_mode||_infinity
        <=m*m!*lambda_m*(-log C),

    ||K_mode^(-1)||_infinity
        <=m*m!*C^(-lambda_m).                             (14)

This uses the SAME word's natural COMMON PAIR coordinate, not an assumed
equality of physical arm clocks. It does not add a COMMON observation to
an I-only problem. If C is latent or can approach0 on the original target
fibre, no input-derived positive lower bound has been acquired.

There is also a direct EXACT source-invariant use, rather than only a
conditioning estimate. In a legitimately supplied fresh paired slot state,
retain C and R_r=b_r^I. Ordinary initialization has R_r=C^lambda_r. An
actual append multiplies them by c*a and b_r^I(cell)*a^lambda_r, respectively.
Equation(12) and the old r=2 identity prove that

    C>0,     R_r>=C^lambda_r                            (15)

is a finite polynomial inductive invariant for EVERY1<=r<=m. The SAME
physical append tuple supplies both multipliers. No word length enters.

Use the OLD source/path correspondence and original F_c(theta,K)=p target.
Where the exact fresh-root receiver supplies these slot coordinates, (15)
may be retained alongside all protected parameters in its existing finite
state. If RCF proves the target disjoint from these sound invariants for
EVERY template in the source-complete finite catalogue, that is a genuine
all-original-size NO. This reuses the old invariant verifier/correspondence;
the explicit all-arity same-tuple inequality is the added supplier. No such
RCF instance was run, and no completeness of this invariant family follows.
For an I-only input, C can at most be same-word INTERNAL bookkeeping; it
does not become a supplied COMMON value or clock promise. No exposed bank
or arbitrary coupled register tensor is replaced by this scalar invariant.

## 8. Why the theorem does not bound physical word length

The completed paired cap2 source theorem already gives strict rational
targets C=1/2,Q=1-1/j whose EVERY private word has

    N >=(j-9)/8,                 j>=3,

and has finite strict witnesses. This is OLD/REUSE, not a new lower-bound
derivation. Both cap2 mode matrices nevertheless have the uniform norm2
projector bound above. Thus stable finite-dimensional spectral structure
does not give a cap-only word bound or bounded physical factorization.

More generally, fixed K semisimplicity, the scalar functional calculus and
source membership are different obligations. Noncommuting products need
not share projectors. Parameters may change with an encoded integer.
The old finite-fibre counter theorem and the new independent-root order
undecidability theorem keep their exact distinct scopes.

For original G3 the target is the ORIGINAL joint response fibre, not a
known complete K. Even a known complete projective kernel need not be a
finite physical word. No all-core source converse, arbitrary source-size H,
closed-value logarithmic equality oracle, exact physical factorization or
unrestricted NO completeness is supplied.

The source-level change is precise: a spectral collision/Jordan limit is
not an unresolved obstruction inside the proven private projective domain.
Do not spend another count/arity ladder re-proving strict semisimplicity or
seeking such a Jordan degeneration. The actual source-specific finite
attainment/exclusion gap remains. This theorem is not promoted as a new
full G3 mechanism.

## 9. Evidence and preservation

The positive decomposition, finite resolvent paths, factorial composition
bound and route inequalities above form the complete hand proof. The
counter matrices and the cap2 check are exact HAND calculations only.
No source generator, old suite, symbolic/numerical control, QE, Lean,
native/Cargo/Lake/CI/model job or peer review was run.

Source hashes, publication readback and recipient adoption are separate
from correctness review and formalization. Source publication does not
create a new scientific execution admission. Original owners, protected
IDs/menu/calendar/register/opaque-graft requirements, no local Git,
no new chat/subagent and all held/USED/UNKNOWN actions remain.
