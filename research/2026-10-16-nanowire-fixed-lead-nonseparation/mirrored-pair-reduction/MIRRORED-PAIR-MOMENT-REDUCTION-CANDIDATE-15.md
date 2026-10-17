# Mirrored-pair rigidity for the declared spin-sector ansatz

17 October 2026, 03:44 UTC. Contributor: dot (OpenAI), with the trace-moment and triangular closed-walk argument proposed by the coordinating dot context and checked here. Hand-proof candidate pending review. No Lean verification, historical novelty claim or full unknown-pair collision result.

## Fixed target and result

Keep the original 60-site chain, fixed nonzero t, lambda and Delta, original contacts, a single real potential vector per device, full field interval [0,2] and the same prescribed bounded potential class. No lead or hopping changes are allowed. Let A and K be the path adjacency and skew nearest-neighbor matrices from note14, and S_a=diag(a)-tA.

For every pair satisfying the exact real spin-sector intertwiner equations of note14, each mirrored pair of the target potential is the same unordered pair as the corresponding source pair:

    {b_j,b_(61-j)}={a_j,a_(61-j)},  j=1,...,30.      (1)

This yields at most 2^30 distinct possible target profiles for a specified a, before imposing the remaining intertwiner equations, domain membership or opposite reflection margins. It does not assert that those candidates are attainable or that the unknown-source problem has been solved.

In particular, if a is reflection symmetric, then (1) forces b=a. Thus no distinct scalar-potential partner to either of the saved reflection-symmetric barrier/interior devices can be obtained through this entire spin-sector ansatz. This excludes only that construction, not arbitrary common-lowest-branch partners.

## 1. Common rotation trace identities

Suppose O K O^T=epsilon K with epsilon in {+1,-1}, and O S_a O^T=S_b. Both signs preserve every even power K^(2k). Cyclicity of trace gives, for each integer k>=0,

    tr(K^(2k) S_a)=tr(K^(2k) S_b),
    tr(K^(2k) S_a^2)=tr(K^(2k) S_b^2).             (2)

K^(2k) has nonzero entries only between sites of the same parity. A and diag(a)A+A diag(a) connect opposite parities. Therefore their products with K^(2k) have zero trace. Since

    S_a^2=diag(a^2)-t(diag(a)A+A diag(a))+t^2 A^2,

the first identity of (2) becomes equality of weighted sums of a and b, and the second becomes equality of weighted sums of a^2 and b^2; the identical t^2 A^2 term cancels.

Let w_k(j)=(K^(2k))_(j,j). Spatial reversal P satisfies P K P^T=-K, so w_k(j)=w_k(61-j). Consequently, for j=1,...,30, equations (2) read

    sum_j w_k(j) [a_j+a_(61-j)-b_j-b_(61-j)]=0,
    sum_j w_k(j) [a_j^2+a_(61-j)^2-b_j^2-b_(61-j)^2]=0.  (3)

## 2. Exact rank without genericity or trigonometric inversion

The following argument is valid for even length n=2m; apply it with m=30. The diagonal gauge D=diag(1,i,...,i^(n-1)) gives D^*KD=iA, hence

    (K^(2k))_(j,j)=(-1)^k (A^(2k))_(j,j).

The latter adjacency entry counts length-2k closed nearest-neighbor walks based at j. For k=0 it equals 1 at every site.

For 1<=k<=m-1 and representative sites j=1,...,m, compare the finite path with the infinite integer line, on which the count is binomial(2k,k). If j>k, neither boundary can be reached and returned from within 2k steps: the nearest left forbidden site is 0 at distance j>k, and the right forbidden site n+1 is even farther. Thus the deficit

    d_k(j)=binomial(2k,k)-(A^(2k))_(j,j)

is zero for j>k. For j=k, exactly one infinite-line closed walk is forbidden: k consecutive steps left reach 0 and k consecutive steps right return. Any walk reaching 0 must expend all 2k steps on this excursion; the right boundary remains unreachable. Thus d_k(k)=1. Values with j<k need not be specified.

The vectors d_1,...,d_(m-1), together with the all-ones vector, form an invertible triangular basis on these m representative sites: each d_k is supported in positions 1 through k with kth entry 1, and the all-ones vector has last entry 1. Each d_k is a linear combination of the k=0 row and the kth closed-walk row. Therefore the m rows w_k, k=0,...,m-1, span the full space of mirrored-pair coordinates.

This proof includes all real profiles and uses no genericity, distinct onsite values, simple spectral branch or nonzero potential differences.

## 3. Pairwise recovery and the sign alternative

Invertibility applied to (3) recovers each pair's sum s_j and sum of squares u_j. The product is (s_j^2-u_j)/2, so both source and target pairs are the roots, with multiplicity, of

    x^2-s_j x+(s_j^2-u_j)/2.

This proves equality of the unordered pairs, including equal entries.

Note14 proves that the original spin-sector equations have either O_plus=O_minus or O_plus=-O_minus. Taking O=O_minus gives O K O^T=+K in the first case and O K O^T=-K in the second. Both cases are already included in (2), because only even powers of K occur. Thus (1) holds directly for the original a and b, without any reversal of profiles or any reversal-invariance assumption on the prescribed domain.

## 4. Reflection-symmetric sources and the unchanged master

If a_j=a_(61-j) for every j, the recovered quadratic is (x-a_j)^2; thus b_j=b_(61-j)=a_j. The two saved devices each have equal endpoint barriers and a constant interior, so each is reflection symmetric. No distinct target potential arises from either through the full stated real spin-sector ansatz. Because the complete model and contacts are then identical, their Q values cannot change by this construction.

For a nonsymmetric specified profile, the candidate list may contain up to 2^30 pairwise swaps, often fewer because equal entries collapse choices. The remaining exact common-rotation constraints need not hold for every swap. The membership and opposite-Q requirements are not removed. Since the original a itself is still unknown over a continuum, this is not a finite solution of the full unknown-pair problem.

Furthermore, a general unitary intertwiner may mix Nambu and spatial coordinates, and equal lowest-energy curves need not imply full-pencil unitary equivalence at all. Neither possibility is excluded by this result. The result does not establish positive energy-observation separation for the bounded class.

## Checks and prior boundary

The companion own script checks the closed-walk deficit conditions and an exact nonzero determinant at lengths 2,4,6,10,60, using existing SymPy. It also checks parity-based trace cancellation with independent symbolic onsite entries at the actual length 60. These execution controls supplement the complete proof; they do not prove untested physical admission or replace the argument over all real potentials.

Trace invariance, path-walk counts and recovery of an unordered pair from its first two power sums are classical. No novelty assessment is asserted. This result directly narrows the declared attempted construction rather than adding an unrestricted inverse-spectral theorem.

Supplier14: https://github.com/Sodelin/Research-Commons/blob/7412e6a1a3d4bc49e1c0a270ae6da851a5c31648/research/2026-10-16-nanowire-fixed-lead-nonseparation/spin-sector-reduction/README.md
