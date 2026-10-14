# G4 all-orders log-diagonal obstruction: lead hand review

Reviewer/publisher: Codex G4 lead, 14 October 2026, 10:41 UTC session.
Original theorem and checker: independent Astra G4 researcher for Nolan.
Separate non-overlapping audits: existing Codex `astra_diagonal_lean` lane
(source coefficients) and `astra_margin_audit` lane (sign and dual extraction).
These are team hand reviews, not external peer review or Lean verification.

**Scoped hand acceptance, with the two coefficient clarifications below.**
For every finite m>=3, every nonzero real covector a on n=3,...,m and every
eta>0, strict finite cells of arbitrarily small independent pair cost exist
with each sign of sum a_n Phi_n. The fixed-bridge construction is accepted
under its freely replaceable, unmarked eligible-bridge hypothesis. It
preserves the entire two-root I kernel and changes COMMON on the SAME tuple.
This rejects a universal additive log-diagonal sign premise. G4 remains open.

## Selected source, actual receipt and original contract

Reviewed immutable source: [Astra PROOF.md](../2026-10-14-g4-global-log-guard-attempt/PROOF.md)
at fcc5d2bdebff02730ee01edd9845030f499d675f, blob
`d1605dd0a3ede81cdf68e962259b3fa2f7f90000`.
Its checker and original receipt were read and authenticated to that same
commit. The author's addressed [request](https://github.com/Sodelin/Research-Commons/issues/1#issuecomment-6164757442)
was actually read; [lead reading ACK](https://github.com/Sodelin/Research-Commons/issues/1#issuecomment-6166520761)
establishes receipt, not acceptance before this review.

Retain the original finite binary rooted-LSA, outer-labelled planar,
cut-child source class with n>=4 original taxa, original parallel arc
occurrences/labels/IDs, strictly positive finite natural exposures, interior
inheritance and ordinary unbounded ancestral completion. A currently
surviving genealogy is one opaque root at each hybrid. Natural COMMON uses
one shared parental bit; natural I routes current roots independently.
Original-ID settings and finite joint randomized programs keep their exact
joint semantics and any original parameter ties. Those menus are not
silently substituted for natural I in this theorem. Controls do not authorize
natural boundary parameters. Only permitted final topology outcomes or
inherited legal marginals count as observations; these private diagonals
are mathematical coordinates, not automatically legal measurements.

The insertion is on a freely replaceable unmarked ordinary bridge under the
[accepted source grammar](../2026-10-01-g4-admitted-testers-0819z/PROOF.md),
sections 1, 3 and 4. It does not authorize replacing a marked/read-only edge,
a tied parameter, or a nonbridge cycle edge. All rows use one actual source
and one shared tuple, and the original root, labels and exterior remain fixed.

## Coefficient clarification 1: first order must be cancelled explicitly

Let lambda_n=n(n-1)/2 and use the source factorization

    b_n=(1-z e)^lambda_n (1-e)^n S_n,
    S_n=sum_k binomial(n,k)(e/(1-e))^k rho^lambda_k
                  (1-z e)^[-nk+k(k+1)/2].

For a fixed coefficient order r, only k<=r contributes. Generalized
binomial/falling-factorial polynomials extend these expressions in n;
at nonnegative integer n, terms k>n vanish exactly. Coefficients of S_n
and log S_n at order r have degree at most r: a summand's binomial factor
has degree k and its remaining order j contributes degree at most j;
finite logarithmic products preserve the sum of these bounds.

Define Q_r(n)=[e^r]{n log(1-e)+log S_n}. Then

    [e]S_n=n,     [e]log S_n=n,     Q_1(n)=0,
    [e^r]Phi_n=Q_r(n)-lambda_n Q_r(2).

Thus order one is exactly zero. For r>=2 the normalized coefficient has
degree at most r, because the subtraction has degree at most two. This
explicit cancellation repairs the otherwise unsupported degree<=1 step
in Astra section 2.1. The empty-input coordinate is one, b_0=b_1=1,
and Phi_0=Phi_1=Phi_2=0. The degree-two coefficient consequently vanishes
identically. For r>=3 the coefficient lies in the span of
binomial(n,3),...,binomial(n,r), since these are the Newton basis and
the first three evaluation values are zero.

## Coefficient clarification 2: the highest-coefficient formula starts at r=3

For r>=3 only, the coefficient of n^r in [e^r]Phi_n is

    P_r(rho,z)=[u^r]log A_rho(u exp(z u)),
    A_rho(u)=sum_k rho^lambda_k u^k/k!.

The restriction is necessary: P_1=1 and P_2=z+(rho-1)/2, whereas Phi
orders one and two are zero. This review supersedes an unqualified reading
of the displayed formula in Astra section 2.2; its use in the theorem is
already only for r>=3.

To justify extraction, filter finite formal series by n-degree<=e-order.
Keeping terms where these degrees are equal respects multiplication and
the finite logarithmic convolution. At order k, binomial(n,k)e^k gives
u^k/k!; the exponent -kn supplies exp(kzu); the factors (1-e)^(-k)
and constant part of that exponent contribute only lower degrees.
The subtraction lambda_n Q_r(2) and n log(1-e) cannot affect n^r for
r>=3. At a fixed r, the computation is finite. No interchange of infinite
analytic limits is used. The coefficient of binomial(n,r) is r!P_r.

## All-orders sign audit

Write log A_rho(v)=sum_{k>=1}L_k(rho)v^k. Finite formal composition gives

    P_r(rho,z)=sum_{k=1}^r L_k(rho)(kz)^(r-k)/(r-k)!.

Here L_1=1, so for fixed rho the leading z term is
z^(r-1)/(r-1)!>0. Each fixed-r coefficient is a finite polynomial in rho.
At rho=0, A_0=1+u, with the constant coefficient rho^0 understood as one.
Set z_3=1 and z_r=(r-1)2^(r-4) for r>=4. The latter is the same real-power
formula as Astra's z_r, with the low-order endpoint made explicit. Let

    t_k=(k z_r)^(r-k)/(k(r-k)!),   1<=k<=r.

Then t_k>0 and t_2=2t_1. For r>=4 and 2<=k<=r-2,

    t_(k+1)/t_k <= (r-2)/(2(r-1)) (3/4)^(r-4) <= 1/3.

The final bound is 1/3 at r=4 and decreases thereafter: its consecutive
ratio is 3(r-1)^2/[4r(r-2)]<1 because
4r(r-2)-3(r-1)^2=(r-3)(r+1)>0. The terminal ratio is
1/(r z_r)<=1/3, including r=3. The finite alternating tail starting at
t_3 is at most t_3<=2t_1/3, by pairing consecutive terms. Therefore

    P_r(0,z_r)=t_1-t_2+t_3-t_4+... <= -t_1/3 < 0.

At r=3 the value is -1/6; at r=4 it is -7/4. These endpoint checks are
controls, not the arbitrary-r proof. Continuity first chooses a strict
rho>0 retaining the negative coefficient, and only then chooses a physical
source. The boundary coefficient is never used as an admitted source.
A finite positive z gives the other sign at a fixed strict rho.

## Arbitrary finite covector and actual source selection

The matrix binomial(n,r), 3<=n,r<=m, is triangular with diagonal one.
For every nonzero real a there is a least r with
c_r=sum_n a_n binomial(n,r)!=0. The Newton expansion above implies all
lower weighted Taylor coefficients vanish, and the first nonzero one is
r! c_r P_r(rho,z). Either sign of P_r is available. Analyticity near e=0
then fixes the corresponding strict sign at sufficiently small positive e.
There is no requirement that a be rational or uniformly bounded.

For the chosen strict rho and finite z, take
0<e<min(1,1/z). Then x=rho, y=1-ze, g=e all lie in (0,1), the cell is
finite, and b_2=e^2 rho+2e(1-e)+(1-e)^2(1-ze) tends to one.
In fact 1-b_2=e^2(1-rho)+(1-e)^2 ze>0, so the pair cost is positive
and can be made smaller than the prescribed eta. Fixed-cap complete
kernels also tend to identity; no uniform estimate over all caps is inferred.

## Exact fixed-target insertion and the legal COMMON difference

Given the same fixed admitted target with an eligible freely replaceable
ordinary bridge E(d), 0<d<1, shrink e until b_2>d. Choose
s=sqrt(d/b_2) in (0,1) and replace only that bridge by E(s) B E(s).
Both pads have finite positive exposure. For two opaque roots the I kernel
has just the singleton forest and their merged tree, with no-merger
probability b_2. Serial no-merger probabilities multiply, so s^2 b_2=d
preserves that ENTIRE two-root kernel. At every arity the log-diagonal
change is exactly Phi_n(B), because the ordinary pads contribute zero.
This is one finite source/tuple for each chosen sign, not independently
selected parameters per observation. Rational rho,z,e can be selected
inside the strict open inequalities; algebraic d then gives algebraic s.

For that same tuple,

    c_2=gx+(1-g)y,
    b_2-c_2=g(1-g)(2-x-y)>0,
    s^2 c_2=d c_2/b_2<d.

For an eligible pendant bridge and the inherited positive crossed-cherry
marginal on two pendant-taxon copies and one external original-taxon copy,
a merger on the pendant forbids that event. The exterior is unchanged;
conditional on pendant survival, its completed law is unchanged. Thus its
legal COMMON probability is multiplied by c_2/b_2<1 in either sign case.
This reuses the accepted unchanged-exterior adapter, including a reticulate
exterior; it adds no hidden observation. General nonpendant pair equality
does not by itself supply that particular crossed-cherry marginal.

## Prior, applicability and novelty boundary

The [earlier exact finite diagonal-fibre review](../2026-10-13-codex-g4-renewed/critical-review/ROOT-DIAGONAL-FIBRE-AND-RANK-REVIEW-0320Z.md)
already proves, at one fixed target, exact equality of arbitrary finite
diagonal panels with differing COMMON pair and unbounded latent routing
rank. That excludes arbitrary nonlinear postprocessing of those panels as
a finite determining bridge. It is stronger than a claim that diagonal
forcing merely seems unlikely. Do not present this new packet as the first
failure of the diagonal route.

The distinctive statement reviewed here is every finite covector's two
signs on arbitrarily weak ONE-cell insertions. The October 8 cubic/quartic
all-ratio cone result and original source suppliers retain attribution.
The deformed-exponential formal coefficients are elementary and classical;
no zero-location theorem, literature absence claim or historical priority
is needed. This review checks the finite identities directly and does not
claim a new exhaustive literature search or independent primary-paper
retrieval for Astra's bibliography.

The [accepted natural BOTH theorem](../2026-10-13-codex-g4-renewed/critical-review/ROOT-GENERAL-NATURAL-BOTH-FINITE-FORCING-ACCEPTANCE.md)
first imposes exact COMMON clock/profile constraints. These insertions do
not satisfy them. Its extra-cell exclusion and the entire-I to entire-C
supplier remain accepted. Nonlinear/full-topology chronological equality
guards on a constrained target fibre are not refuted by this theorem.

## Computational and formal verification

The original standard-library script was inspected and independently run
once by this reviewer. All 448 exact controls passed; its complete saved
receipt is byte-identical to the immutable contributor output. Source blobs
and the exact replay appear in [evidence/INDEPENDENT-REPLAY.json](evidence/INDEPENDENT-REPLAY.json).
This is independent execution of contributor-written finite controls, not
an independently designed universal proof or an external mathematical
acceptance. It supplements the hand reviews above.

Nolan's Lean instruction persists. Any accompanying Lean file is authored
source only, with exact missing formal adapters identified separately.
The integration owner's actual resource stop is respected: no compiler,
dependency query, source adoption, diagnostic, object scan or device operation
was performed by this review. No source directive counts as type/axiom output.

## Remaining full master obligation

The [accepted exact equivalence](../2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/FINITE-INDEPENDENT-BRIDGE-EXACT-EQUIVALENCE.md)
is reused: for each fixed admitted T, a finite set of ORIGINAL LEGAL I rows
must force its inherited finite COMMON certificate against EVERY admitted
finite rival of unknown size. Alternatively ONE fixed admitted T needs an
exact inequivalent admitted rival after EVERY finite full-legal-I prefix.
Neither statement is established here. Pair equality plus the sign of one
statistic is not equality of a prescribed observation panel. The complete
physical weak-word residual still requires all body parameters, chronology
and nonlinear curvature, or another justified full-strength route.
