> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Explicit two-atom relation for the repeated-bigon count bound

23 October 2026 UTC. Existing G3 owner. HAND/self-audited mathematical
supplement; UNREVIEWED and UNCOMPILED. No source, arithmetic, QE, compiler,
model, native or old-suite execution supplies acceptance for this proof.
The original all-input G3 goal remains ACTIVE/OPEN.

This makes one step of [the repeated-block count theorem](G3-REPEATED-BLOCK-ALGEBRAIC-COUNT.md)
explicit. That frozen predecessor is 13443B/SHA256
69ae2c128c73cff02cfed6e9876aa8877dad997c4418c20306afd7c4d4dcfcf1.
The use-site is four multiplicatively independent ALG target coordinates
of an unknown number of identical fresh COMMON bigons. It is not an
all-word size bound or an extension of the observation language.

## Prior and successor comparison

Complete relevant bodies were read, not merely their headings. These four
paths are at immutable Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6:

- `research/2026-10-01-codex-g3-finite-recognition/COMMON-CAP-FOUR.md`,
  15058B/SHA256a0fda6976d285ede96bb0f67b0193405663758d3b0f87b00c5c24611b061aa1f,
  blob85fd78cd5de9300e20c4cfa9b0a43eca5f6fa2e0. Exact two-node compression
  for the THREE nonconstant moments at exponents1,3,6, and its bounded
  original COMMON cap-four recognizer, are OLD/REUSE.
- Its arbitrary-cap successor
  `research/2026-10-01-codex-g3-finite-recognition/ARBITRARY-CAP-BOUNDARY.md`,
  11325B/SHA256e718b8013324eb56a372639dbe0f3408741001209a6ed6e18adc43167073892c,
  blob5de3f810eed5825e1111c63694b22a7a0abe6b45, already detects an exposed
  sparse-moment boundary, uniquely recovers its atom law and bounds binary
  factors by support size minus one. Those algorithms are not reopened.
- `research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/ONE-BERNOULLI-QUALITATIVE-LOCALIZATION.md`,
  7777B/SHA25602fe3641345ed9d7d816947f03019157c672020ce00253d881c084e75c07cb39,
  blobfc44ee5f5375c971ed0c6ed8f37df670bdb6adb5, already uses the four
  moments1,3,6,10 to identify a two-point limit and localize one persistent
  Bernoulli factor. It explicitly supplies no effective all-word rate.
- `research/2026-10-08-codex-g3-g4-coordinated-1000z/g3-singular/PROOF-R2.md`,
  18565B/SHA25601824ddd515ea7d8d26f479eaad745689d9cba564b32f8c93904eeba5ec155f0,
  blobeeb96521e12c0bb8a465e1419a42ccad6a1732d0, supplies low-response-rank
  coupled compression using the OLD strict two-atom realization, with its
  declared whole-fibre COMMON hypotheses. It does not bound a repeated
  cell from multiplicative arithmetic of the four target moments.

The local [six-moment exposed-factorisation proof](G3-COMMON-SIX-MOMENT-EXPOSED-FACTORISATION.md)
is also reused. Its nonnegative polynomial is in the SUPPORT variable and
forces a representing measure onto finitely many roots. The polynomial
below is instead a universal relation in FOUR MOMENT COORDINATES of one
cell. It need not expose the target moment vector, and the final target of
N repeated cells need not itself have two atoms. Confusing these two
polynomials would duplicate the boundary result and invalidate this use.

Classification: explicit integration of classical moment recurrences,
resultants and the preceding radical theorem. The inspected predecessors
do not state the explicit relation/count interface below. This bounded
comparison makes no exhaustive absence or mathematical priority claim.

## One fixed polynomial, with a nonzero certificate

Let a,b be positive real supports and0<=p<=1. Put

    m_j=p*a^j+(1-p)*b^j, m_0=1,
    t=m_1, z=m_3, u=m_6, v=m_10,
    sigma=a+b, pi=a*b.

The ordinary two-atom recurrence is

    m_(j+2)=sigma*m_(j+1)-pi*m_j.

Eliminating m_2 from the j=0,1 equations gives

    z=sigma^2*t-(sigma+t)*pi.

For physical positive data sigma+t>0. In the polynomial ring
Q[sigma,t,z], define

    D=sigma+t, A=sigma^2*t-z,
    B_0=1, B_1=t,
    B_(j+2)=sigma*D*B_(j+1)-A*B_j       if j is even,
    B_(j+2)=sigma*B_(j+1)-A*B_j         if j is odd.

Substitution of pi=A/D in the moment recurrence proves, by induction,

    B_j=D^floor(j/2)*m_j.

In particular B_2=sigma*t^2+z and B_3=z*D. Define

    F_6=B_6-u*D^3,
    F_10=B_10-v*D^5,
    Q(t,z,u,v)=Res_sigma(F_6,F_10).

This is a completely specified rational polynomial: use the ordinary
18-by-18 Sylvester determinant, with degrees6 and12 in sigma. Indeed
B_4 has degree3 and B_5 degree4, each with leading coefficient z-t^3.
Induction in the displayed recurrence gives, for every j>=4,

    deg_sigma B_j=j+floor(j/2)-3,
    leading coefficient=z-t^3.

The other terms in F_6 and F_10 have sigma degrees3 and5, respectively.
Thus their generic degrees are exactly6 and12. Padding a determinant to
unnecessarily larger degrees would not be this definition.

For every positive two-atom moment tuple, its actual sigma is a common
root of F_6 and F_10. Therefore Q(t,z,u,v)=0. This remains necessary for
coincident supports and degenerate weights; no division by a-b or p is
used. Degenerate weights are not admitted as natural source permissions.

To prove Q is NONZERO, specialize the formal coefficient variables to

    (t,z,u,v)=(0,1,0,0).

This is an algebraic coefficient check, not a physical source. The same
recurrence gives

    F_6=sigma^6+3*sigma^3+1,
    F_10=sigma^12+7*sigma^9+15*sigma^6+10*sigma^3+1,
    F_10=(sigma^6+4*sigma^3+2)*F_6-1.

The specialized polynomials retain degrees6 and12 and are monic. At
each root of F_6 the second is -1. Consequently

    Q(0,1,0,0)=(-1)^6=1.

This hand identity proves nonzeroness without expanding the determinant
or running a polynomial-identity search. No assertion that Q alone
characterizes physical two-atom laws is needed or made.

A convenient loose total-degree bound is198. Assign weights1 to sigma,t,
weight3 to z,6 to u and10 to v. B_j is weighted homogeneous of weight
j+floor(j/2); F_6 and F_10 have weights9 and15. Every coefficient of
F_6 has ordinary total degree at most9, and every coefficient of F_10
at most15. Every Sylvester term takes twelve coefficients from F_6 and
six from F_10, so

    deg Q<=12*9+6*15=198.                         (1)

The bound is deliberately loose; constant sharpening is not a new queue.

## Explicit repetition bound

Supply FOUR exact positive real-algebraic numbers

    beta=(beta_1,beta_3,beta_6,beta_10)

which are multiplicatively independent over Z. The natural application
also has each beta_j in(0,1). The question here is whether there are ANY
positive real a,b and interior p, and ANY integer N>=1, with

    [p*a^j+(1-p)*b^j]^N=beta_j, j=1,3,6,10.       (2)

Both supports must be in(0,1) for the physical application.
The bound below remains necessary even before those extra inequalities.

Reuse, without reopening, the unconditional positive S-unit and primitive
lattice construction in the preceding count theorem. It returns positive
algebraic C_1,...,C_4 in one real number field K and an integer4-by-4
matrix E of rank4 such that

    beta_j=product_i C_i^E_(i,j).

The underlying S-unit coordinate lattice of the C_i is primitive. Put

    M=max_(i,j) |E_(i,j)|, H=396*M.               (3)

M>=1. This is a total computable integer from the supplied algebraic
target, including on a NO instance satisfying the rank-four premise.
No successful source search or transcendental zero oracle is assumed.

For a putative witness of count N set x_i=C_i^(1/N), choosing the positive
real roots. Then its one-cell tuple is

    (beta_j^(1/N))_j=(product_i x_i^E_(i,j))_j,

and Q vanishes there. Because E has rank4, distinct exponent vectors
alpha of Q remain distinct under alpha -> E*alpha. Thus the formal
Laurent polynomial

    Q(product_i X_i^E_(i,1),...,product_i X_i^E_(i,4))

is nonzero. By (1), every resulting exponent lies in[-198*M,198*M]
in each coordinate, so each exponent width is at most396*M. Remove a
common Laurent monomial. If N>H, all remaining exponents are in
{0,...,N-1} in every variable. The primitive-lattice radical independence
lemma of the preceding proof, applying Mordell's real-radical theorem,
says that these distinct monomials in x_1,...,x_4 are K-linearly
independent. They cannot give the nonzero Q relation. Contradiction.
Therefore EVERY witness of (2) satisfies

    N<=396*max_(i,j)|E_(i,j)|.                   (4)

The old proof provides the full elementary number-field/S-unit acquisition
and the exact source of the radical theorem. This supplement does not
rely on an uncertified class-group computation or a new PARI execution.
The primary theorem is Mordell, *On the linear independence of algebraic
numbers*, Pacific Journal of Mathematics3(1953), pp625--630:
https://msp.org/pjm/1953/3-3/pjm-v3-n3-p10-s.pdf .

The strict two-atom construction and complete fixed-N polynomial source
feasibility are OLD/REUSE. Enumerating N=1,...,H and those exact fixed-N
formulas gives terminating recognition of this supplied repeated family.
Additional original rows are tested together at the same N and ONE
physical tuple. A failed four-coordinate test rejects this family only.
If the four-coordinate rank premise fails, this supplier returns
OUT-OF-SCOPE, not NO. The more general count theorem is unchanged.

## Literal original-source interface and limits

For k current roots let lambda=binom(k,2). One fresh natural COMMON bigon
with first/parent0 probability p, original native gamma=1-p, arm survivals
x,y and an ordinary survival factor s has diagonal

    s^lambda*(p*x^lambda+(1-p)*y^lambda).

Its four k=2,3,4,5 coordinates are exactly the two-atom moments above,
with supports a=s*x,b=s*y. N repetitions use DISTINCT original private
IDs and independent cell bits; assigning the same numeric p does not
reuse one exposed register. Routing acts on current opaque roots, not
their old leaves. The four algebraic target values must be actually
supplied or licensed-decoded by the original caller. Choosing one latent
kernel from an unconstrained joint-response fibre does not qualify.

If otherwise identical cells have different ordinary connector factors,
their total product A can be absorbed for this DIAGONAL calculation as
supports a=A^(1/N)*x,b=A^(1/N)*y. This neither reorders the full forest
program nor freezes the exterior; fixed-N feasibility must retain its
actual chronology, connectors, parent order, register and all rows.
An unknown additional stochastic head/correction cannot be absorbed as
an ordinary factor and invalidates equation(2) for the whole target.

The COMMON coordinates can bound a supplied BOTH family too, but do not
independently fit its I parameters. A pure I input without a licensed
COMMON diagonal does not meet this supplier. Rank>=5 in an arbitrary
six-coordinate signature does NOT ensure rank4 of this particular
four-coordinate subtuple. The original general theorem remains available
where its actual rank/dimension hypotheses are acquired.

Nonvacuity is OLD arithmetic from the preceding proof, not a new run:
p=x=s=1/2,y=1/3 gives moments

    C_lambda=(3^lambda+2^lambda)/(2^(2*lambda+1)*3^lambda).

At lambda1,3,6,10 the numerator primes introduce, in order,5,7,13 and
a prime divisor of4621 (60073=13*4621). None of the latter primes occurs
earlier. These four rational numbers are multiplicatively independent;
every positive power preserves that property. This does not prove that
the displayed repetition count is a minimum among all source types.

No unbounded synchronization constraint is added to the original input
language. Repeated numeric cells are a restricted mathematical source
family; original arbitrary words may use different parameters at every
fresh position. No count bound for those heterogeneous words, no
whole-fibre choice, no Phi-zero decision, no all-core NO certificate and
no master H(D) follows. Those are the exact remaining original G3 gates.

## Verification boundary

The recurrence, generic degrees, specialized Euclidean identity and
degree/count inequalities were checked by hand in this derivation.
There was no determinant expansion, numerical test, fresh source tuple,
RCF/number-field run, old control replay or proof-assistant pass.
Read/hash custody is separate from mathematical acceptance. The four
inspected predecessor/successor statements are reused at their original
scope; no absent grep match is used as proof of prior absence.
