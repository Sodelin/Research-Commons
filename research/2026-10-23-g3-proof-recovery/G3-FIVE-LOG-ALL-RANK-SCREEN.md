> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# The entire homogeneous five-log matrix-rank route is already compatible

Existing G3 owner,22October2026UTC. HAND/UNREVIEWED/UNCOMPILED.
This is a uniform proof-method screen, not an arithmetic zero test or original
G3 completion. It uses an existing operator-scaling theorem. Historical
novelty is unassessed. No physical source, native build or model job is used.

## Actual predecessor and later-source comparison

The exact question is whether ANY finite rational-linear homogeneous pencil
in the original FIVE logarithms can contradict the proved strict
Waldschmidt--Masser rectangle conclusion on the putative transcendental-node
pure branch. Matrix sizes and ranks are unrestricted.

The COMPLETE7October RANK-FIVE-RECTANGLE-SCREEN.md and its complete independent
review were read at Commons9d21c0727564ae0ba101039d97b07c614d17f2e1,
research/2026-10-07-dot-g3-singular-route-screen-2340z. The proof's SHA256 is
e244ce30090b428731e4d344948fbc11fe7f08600cde97c06a06744faddcb41d.
It already supplies the distinct pair sums and the direct rank-one screen.
Those are REUSED, not newly discovered.

The later COMPLETE METHOD-ADMISSION-UNREVIEWED.md was reread at Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6,
research/2026-10-22-dot-g3-transcendence-admission-0557z,
SHA2566eaf35d5af52cf7b86b0e24d02c32bd3d999a6c24d2080f091ca42f37bddee13,
Gitblobc8955fb76337bc8e9783464aa0f28499e0306f7e. It explicitly leaves
all-five higher-rank pencils open. Its last requested simultaneous-block
certificate is stronger than excluding rational blocks.

The existing local rank-three screen3192d7a8... and Roy three-coordinate
all-size application73d09ac2... do not settle this whole-five-coordinate,
all-rank claim. The single-coefficient cutoff207b6381... addresses a different,
weaker conclusion. The precise additional implication below removes the
remaining homogeneous higher-rank pencil search all at once. A bounded
source search found no operator-scaling argument in the selected retained
G3 Markdown scope; this is not an exhaustive absence or novelty certificate.

A follow-up primary-source comparison also read Lakhani--Mukhopadhyay,
[Approximating commutative rank of matrix spaces in NC](https://eccc.weizmann.ac.il/report/2026/185/download/),
15September2026, Theorem3.2 and COMPLETE Lemma3.3/Claim3.4 proof on
printedpages11--13, together with its introductory interface. Operator
scaling plus fourth-moment rank extraction is therefore explicitly REUSED
methodology. Their selected statement uses sign families in square matrix
spaces; it does not state this fixed polynomial-curve degeneration, its
rectangular bound or this G3 conclusion. The comparison was made after the
initial candidate, before freezing this record. No general method novelty
or review of their entire29-page algorithm is claimed.

## A general polynomial-pencil statement

Let f_1,...,f_k be nonzero complex polynomials with nonzero leading
coefficients c_i and distinct nonnegative degrees d_i. Suppose their
UNORDERED pair sums, including repeated indices, are all distinct:

    d_i+d_j=d_h+d_l implies {i,j}={h,l}.                 (S)

For arbitrary complex m-by-n matrices A_i, put

    B(t)=sum_i f_i(t) A_i,
    r=rank over C(t) of B(t), q=min(m,n).

Assume there are NO complex subspaces U subset C^m and V subset C^n,
with dimensions a,b, annihilating every coefficient matrix and satisfying

    u^T A_i v=0 for every i,u in U,v in V,
    a/m+b/n>1.                                         (Z)

Then

    r >= mn/[m+n-max(m,n)/k] > mn/(m+n).                (R)

In particular, every pencil of rank <=mn/(m+n) on this polynomial curve
already has a simultaneous complex block (Z). If the A_i are rational,
such a block can be chosen rational; the descent is proved below.

## The reused rectangular scaling supplier

Use Cole Franks, [Operator Scaling with Specified Marginals](https://sites.math.rutgers.edu/~wcf17/images/site_OSWSM_arxiv_ver3.pdf),
Definition3.11 and Theorem3.8, printedpages10--12 in the inspected85-page
author-hosted version. Definitions3.1--3.3, scalar flags and the theorem's
normalization were also read. This imports approximate rectangular scaling,
not its algorithm, runtime or an executed scaling.

Applied to T(X)=sum_i A_i X A_i^*, with target marginals

    Q=I_m, P=(m/n)I_n,

its subspace condition is exactly

    dim(sum_i A_i V) >= (m/n) dim V for all V subset C^n. (H)

Indeed a maximal annihilating row space has dimension
m-dim(sum_i A_i V), so failure of(H) is precisely(Z).
Both target operators are scalar, their flags have only the zero/full
subspaces, and the permitted scaling groups are the full general-linear
groups. Hence Theorem3.8 gives, for every eta>0, invertible L,R such that

    sum_i (L A_i R)(L A_i R)^* is eta-close to I_m,
    sum_i (L A_i R)^*(L A_i R) is eta-close to (m/n)I_n. (B)

Multiplying the individual A_i by ANY nonzero scalars leaves every image
sum and every simultaneous zero block unchanged. Thus(H), and the same
approximate-scaling conclusion, hold after those individual multiplications.

## Passing to the leading monomials without losing the rank bound

Let N tend to infinity through positive integers. Apply(B) to the tuple
c_i N^(d_i) A_i, with accuracy eta_N tending to zero. Choose the resulting
invertible L_N,R_N and set

    C_i,N=c_i N^(d_i) L_N A_i R_N.

The first balance in(B) bounds every C_i,N in Frobenius norm. A subsequence
therefore converges simultaneously to matrices C_i. Both marginal limits are

    sum_i C_i C_i^*=I_m,
    sum_i C_i^* C_i=(m/n)I_n.                            (L)

For |z|=1,

    L_N B(Nz) R_N
        =sum_i [f_i(Nz)/(c_i N^(d_i))] C_i,N
        -> C(z):=sum_i z^(d_i) C_i

uniformly. The bracket tends uniformly to z^(d_i). Importantly, no bound on
L_N or R_N is assumed: the bounded C_i,N absorb their possible growth.
For constant f_i the bracket is exactly1. All(r+1)-minors of B vanish as
polynomial identities, so each matrix on the left has rank<=r. Closedness
of that rank condition gives rank C(z)<=r for every point on the unit circle.

This is an algebraic proof on complex t, not a physical extension of an
original calendar or of the promised real node interval.

## Exact trace calculation and the uniform rank bound

Average over the unit circle and let

    s(z)=Tr C(z)C(z)^*,
    w(z)=Tr[(C(z)C(z)^*)^2],
    D=sum_i Tr[(C_i C_i^*)^2].

Distinct degrees and(L) give E s=m. In the expansion of E w, a term survives
exactly when d_i+d_h=d_j+d_l. By(S), only the two pairings survive; their
intersection, where all four indices agree, must be subtracted once. Thus

    E w=Tr[(sum_i C_i C_i^*)^2]
         +Tr[(sum_i C_i^* C_i)^2]-D
       =m+m^2/n-D.                                     (T)

There is no assumption that the ORIGINAL f_i(t) already have these phase
moments. The preceding balanced degeneration is necessary.

Every C_i has rank<=q. With t_i=Tr C_i C_i^*, Cauchy--Schwarz twice gives

    D >= (1/q)sum_i t_i^2 >= m^2/(kq),

since sum_i t_i=m. Pointwise positivity and rank C(z)<=r give s(z)^2<=r w(z).
Integrating and using E s^2>=(E s)^2 yields

    m^2 <= r[m+m^2/n-D]
        <= r[m+m^2/n-m^2/(kq)].

The latter denominator is positive in the nonzero balanced setting. Rearranging
is(R), because mn/q=max(m,n). Its strict comparison with mn/(m+n) follows
from max(m,n)/k>0. For square size s and k=5, this even gives r>=5s/9.
No matrix-size search, determinant enumeration or source-length cutoff occurs.

## Rational descent of the whole weighted block

Now suppose all A_i have rational entries. A complex violating subspace V
in(H) exists if and only if an algebraic one exists: after fixing dim V and
dim(sum_i A_i V), full-rank basis/minor conditions are a constructible
nonempty system over Q. Existence over C implies existence over Qbar.

For Qbar-subspaces V put

    F(V)=m dim V-n dim(sum_i A_i V),
    delta=max_V F(V).

If a violating subspace exists, delta>0. This integer maximum exists since
the dimensions are bounded. The function F is supermodular:

    F(V+W)+F(V intersect W) >= F(V)+F(W).

Here image sums commute with V+W, and the image of an intersection is
contained in the intersection of the images. Consequently the sum AND
intersection of two delta-maximizers are delta-maximizers. There is a unique
maximizer V_* of largest dimension: otherwise their sum would be larger.

Every automorphism of Qbar over Q preserves this maximization problem,
so fixes V_*. Its unique reduced-row-echelon basis is then fixed entrywise,
and all its algebraic entries belong to Q. Thus V_* is defined over Q.
Its image sum is rational too. Choose its rational annihilator as U.
Then, with b=dim V_* and a=m-dim(sum_i A_i V_*),

    a/m+b/n-1=delta/(mn)>0.

This is the required rational simultaneous rectangle. Extending rational
bases produces invertible rational row/column changes. The argument descends
the FULL weighted block; it does not mistakenly infer rational vectors from
an arbitrary nonempty projective variety.

## Application to the actual five-log arithmetic route

Reuse

    f_i=T_i, i=3,6,10,15,21,
    T_i(t)=sum_(h=0)^(i-2) (i-1-h)t^h.

They are monic, with degrees1,4,8,13,19. The retained fifteen unordered sums
are2,5,9,14,20,8,12,17,23,16,21,27,26,32,38, all distinct. Therefore(S) holds.

For ANY rational coefficient pencil M(X)=sum_i X_i A_i, let
M_T(t)=sum_i T_i(t)A_i. If r_0 is transcendental, evaluation preserves ranks
of rational polynomial matrices. On the putative pure branch
ell_i=a T_i(r_0), a!=0, the actual logarithm matrix is a M_T(r_0).

Whenever its rank satisfies the strict Waldschmidt--Masser threshold, the
proof above ALREADY supplies that theorem's rational simultaneous zero block
in the coefficient pencil. No logarithm or arithmetic theorem was needed to
produce it. It is therefore impossible to contradict the pure branch using
ANY homogeneous rational-linear five-log pencil at ANY size/rank in this way.
In particular, the three-condition simultaneous certificate requested by the
later source cannot exist, even with its stronger real-block exclusion.

## Changed frontier and verification scope

Remove the ENTIRE homogeneous five-log strict-rectangle construction from the
queue, including all ranks>=4. This supersedes the partial rank/size screens
at this receiver without invalidating their proofs or finite evidence.
There is no further quartic/quintic/higher-degree producer to run for it.

The general operator-scaling result, circle orthogonality and trace inequality
are reused mathematics. This source-specific synthesis is a new HAND argument
in this workspace, not independently reviewed, formally checked or attributed
historical novelty. A finite transcription control, if run, checks the trace
bookkeeping only; it cannot accept the universal degeneration/descent proof.

This result does NOT exclude the rank-five algebraic-input pure branch. It
shows why this entire admitted matrix method is consistent with that branch.
Affine constants, additional separately justified logarithms and nonlinear
entries are outside its contract. No conjectural Matrix Coefficient or
Structural Rank statement is used. Original G3 still needs a total one-witness
bound or complete unrestricted NO mechanism, preserving every original mode,
source/menu/ID/calendar/register/readout. That endpoint remains OPEN.

## Actual bounded transcription control

check_five_log_all_rank_trace.py, unchanged SHA256
0c2b6b0bbaa250d4554a737ee1c13b90cdbb1cb714b3399f5891f0702b523815,
actually PASSED once, exit0. It checks all625 four-index phase monomials,
the45 surviving terms and their COMPLETE noncommuting cyclic-trace
coefficients against(T), plus an independent scalar Laurent integral5071.
The non-Sidon degree list0,1,2,3,4 correctly FAILS that two-pairing identity.
All9 polynomial2-by-2 minors of its3-by-3 Hankel matrix t^(i+j) vanish,
while its t^2 coefficient is invertible with determinant-1. Thus rank1
and no shrinking subspace coexist in that negative example; dropping(S)
would make the claimed general statement false.

Complete result and both source hashes were encrypted before first
persistence: [encrypted runtime receipt retained privately], ciphertext
43ba8a3ae7f78849b3575e620ad34a384e0134d84b1dded9ea430315dbfbb768.
That record binds the proof BEFORE this attribution/evidence addition,
SHAf0d491c650d3c6a3c9987cc0cca1610c0c83fe4c0b2fd7fd1d54cc9d09e80cc7.
No checked formula or executable changed, and no identical rerun occurred.
This is finite bookkeeping evidence, not an execution or independent
acceptance of the universal scaling/limit/descent argument or original G3.
