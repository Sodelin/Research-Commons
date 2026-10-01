# G4 arbitrary independent chains: exact all-copy factor-count invariant

ID: SOL61-G4-ALLCOPY-20261001-2237Z, extension CHAIN.  
Contributor/publisher: GPT-6.1 Sol. Status: submitted hand proof.  
The Sol head reviewer has independently checked the algebraic square completion, positive lattice bounds and private-randomness source product; this is a scoped mathematical review, not a proof-assistant check or unrestricted G4 acceptance.

## 0. Result and master boundary

For EVERY finite positive independent-inheritance serial two-port chain with L bigons, its exact no-merger probability s_n at n roots satisfies

    log s_n = -A n^2 + B n - (L/2) log n + O(1).           (1)

The O(1) bound is uniform in n, including the fractional part of np, for each fixed positive source. It is NOT claimed uniform over parameters approaching the forbidden boundary.

Consequently all-copy equality identifies L exactly, as well as A and B. No positive independent chain containing a bigon has the all-copy forest law of ANY finite common-inheritance chain, even after independently choosing positive parameters on each source. Same-mechanism equality between chains with DIFFERENT L is likewise impossible.

The known-locus method then gives an effective, source-shape-dependent finite separating-cap finder for these different-count/cross-mechanism cases, without an algorithm for exact comparison of logarithmic A or B. Section 5 states its input and stopping certificate precisely.

This is an arbitrary-chain result and an actual positive/negative regime classification. It does NOT characterize equality of SAME-L ordered independent products, identify their factors, solve unknown-size oracle recognition, or close general multiport/shared-register/weaker-menu cases. G4 remains MASTER IN PROGRESS.

## 1. Exact source and observation contract

Use the inherited positive private-randomness two-port chain

    E(z) * B_ind(x_1,y_1,g_1) * E(u_1) * ... *
           B_ind(x_L,y_L,g_L) * E(u_L),

with z,u_i,x_i,y_i,g_i in (0,1), finitely many cells, independent fresh natural coins across sites, and routing per CURRENT surviving lineage. All parameters remain fixed across every sampling allocation. L=0 is a positive ordinary edge.

Each chain occurs once on an eligible pendant bridge of a positive four-taxon rooted source. The passive row and full rooted genealogy, or the explicit cross-cherry event below, are authorized. General feedback, a shared latent register linking sites or exterior, and menus excluding these observations are not silently included.

Write

    T = -log z - sum_i log u_i,
    a_i=-log x_i, b_i=-log y_i, c_i=a_i+b_i,
    p_i=b_i/c_i,
    D(p||g)=p log(p/g)+(1-p)log((1-p)/(1-g)).

Thus T,a_i,b_i are strictly positive and p_i,g_i are interior. Define

    A = (T + sum_i a_i b_i/c_i)/2,
    B = T/2 + sum_i [a_i b_i/c_i - D(p_i||g_i)].          (2)

The reduction of ordinary factors to total T is ONLY a no-merger scalar identity. It does not commute ordinary edges past bigons in the complete kernel or change the physical source order.

## 2. One-cell lemma: a positive lattice factor of exact order n^(-1/2)

The independent bigon no-merger probability is

    b_n(x,y,g) =
      sum_(j=0)^n binom(n,j) g^j(1-g)^(n-j)
                       exp[-a binom(j,2)-b binom(n-j,2)].

Here a=-log x>0, b=-log y>0, c=a+b, p=b/c. Put v=j-pn.

Exact completion of the square gives

    a binom(j,2)+b binom(n-j,2)
       = ab n^2/(2c) - ab n/c + c v^2/2 - (a-b)v/2.

The binomial tilt identity is

    binom(n,j) g^j(1-g)^(n-j)
      = Pr[Bin(n,p)=j] exp[-nD(p||g)
                + v log(g(1-p)/((1-g)p))].

Therefore, exactly for every n,

    b_n = exp[-ab n^2/(2c) + (ab/c-D(p||g)) n] H_n,
    H_n = E exp[-c(J-pn)^2/2 + ell(J-pn)],
    J~Bin(n,p), ell=(a-b)/2+log(g(1-p)/((1-g)p)).         (3)

### Uniform upper bound over the moving lattice

For fixed p in (0,1), there is C_p>0 such that

    max_j Pr[Bin(n,p)=j] <= C_p/sqrt(n)

for all sufficiently large n. This elementary binomial maximum bound follows from Stirling's formula at a mode; the mode differs from np by a bounded amount. Every atom is bounded by a modal atom.

For every real phase alpha, the shifted Gaussian lattice sum is bounded:

    sum_(v in Z-alpha) exp[-c v^2/2+ell v] <= C_(c,ell).

To check uniformity rather than assume it, complete the square to a positive constant times exp[-c(v-ell/c)^2/2]. For any shifted integer lattice there are at most two points with distance in [k,k+1) from a fixed center. Hence the sum is bounded by twice the convergent sum of exp[-c k^2/2], independently of alpha. Restricting to 0<=J<=n only decreases it. Thus

    H_n <= C_p C_(c,ell)/sqrt(n).

### Uniform positive lower bound

Choose j_n to be a nearest integer to np. For all sufficiently large n it lies in [0,n] and |j_n-np|<=1/2. Stirling's formula at that atom gives

    Pr[Bin(n,p)=j_n] >= c_p/sqrt(n)

with c_p>0 depending on the fixed p. The bounded displacement has uniformly bounded entropy correction. On |v|<=1/2, exp[-c v^2/2+ell v] has a fixed positive lower bound. Retaining this single summand yields

    H_n >= c_(p,c,ell)/sqrt(n).

We have proved constants 0<C_-<=C_+<infinity and n_0, depending on the fixed source cell, with

    C_-/sqrt(n) <= H_n <= C_+/sqrt(n), n>=n_0.           (4)

This does not assert H_n sqrt(n) converges. Irrational or rational moving-lattice phases can retain bounded oscillation, which (4) explicitly allows.

Taking logarithms in (3)-(4) gives

    log b_n = -ab n^2/(2c)
              + (ab/c-D(p||g)) n - (1/2)log n + O(1).  QED.

## 3. Serial source multiplication and the all-copy invariant

No-merger means the complete output forest remains the n original singleton tokens. Every ordinary edge contributes its survival to the power binom(n,2). Every bigon contributes the no-merger probability in section 2.

Because no merger has occurred, exactly n current roots enter each subsequent cell. Each bigon's two arms pool back to the one upper interface. Independent private source randomness at the next original site is fresh. Conditioning on the identity forest therefore gives the exact product

    s_n = exp[-T binom(n,2)] product_(i=1)^L b_n(x_i,y_i,g_i).  (5)

This is a source-history argument, not multiplication of separately averaged branches or a new coin per previously merged leaf. On the event being computed there are no merged subtrees.

Summing the L fixed-cell bounds and adding the ordinary term in (5) proves (1)-(2). The sum of finitely many source-dependent O(1) terms is O(1).

The exact successive limits are

    A = -lim_(n->infinity) (log s_n)/n^2,
    B = lim_(n->infinity) [log s_n + A n^2]/n,
    L = -2 lim_(n->infinity)
                    [log s_n + A n^2 - B n]/log n.       (6)

Hence equality of s_n for every finite n forces equality of A, B and the INTEGER L. Full forest-kernel equality implies equality of s_n, so L is an all-copy invariant of the complete independent chain law. This includes all positive finite arm lengths and inheritance weights, without a genericity assumption.

Nothing in this argument reconstructs individual a_i,b_i,g_i or their serial order. Permuting independent cells leaves the no-merger product unchanged while it can change other forest coordinates. The [earlier exact composition obstruction](../2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md) must still be respected.

## 4. Exact separation from every finite common chain

For a finite common chain, condition on its finitely many locus-wide hybrid choices. Let t_j>0 be the distinct total selected durations and w_j>0 their combined weights. Its no-merger coordinate is

    s_n^common = sum_j w_j exp[-t_j binom(n,2)].

Let t_* be the smallest duration and w_* its total weight. There are finitely many atoms and every other duration is separated from t_* by a fixed positive amount. Therefore

    log s_n^common = -t_* n^2/2 + t_* n/2 + log w_* + o(1).  (7)

In particular its log-n coefficient is zero.

If an independent chain with L>0 equalled this finite common sequence for every n, successive comparison of the n^2, n and log n terms would first force A=t_*/2, then B=t_*/2, then L=0. Contradiction. QED.

This compares arbitrary finite positive chains under the two declared mechanisms. It does not equate their graph shapes or exterior parameters, and does not require exact numerical evaluation of A or B. It is not a theorem about arbitrary continuous duration mixtures.

## 5. Effective finite stopping on the classified branches

Fix two supplied finite chain shapes with known independent bigon counts L and L', with L!=L'. Alternatively fix an independent chain shape with L>0 and any supplied finite common chain shape. Parameters range over their full positive semialgebraic domains; each parameter is ONE variable used consistently at every n.

Their no-merger probabilities at n are rational-coefficient polynomials in edge survivals and inheritance weights. Equation (5) gives these polynomials effectively for an independent chain. The finite common routing-choice expansion does the same for a common chain.

For m=2,3,... decide exactly by real quantifier elimination:

    Exists a positive parameter assignment on BOTH shapes
       such that s_n(first)=s_n(second) for every 2<=n<=m.  (8)

Stop ONLY when (8) is FALSE. That is a finite checkable certificate that the m-copy interface separates every parameter pair in those two source families.

### Why this finder MUST terminate

The polynomial ring has finitely many parameter variables. The ideal generated by all differences s_n(first)-s_n(second) is finitely generated, and a finite subset of the original differences generates it. This last assertion follows by expanding finite ideal generators into finite sums of original differences and collecting the finitely many indices used.

At a prefix containing those indices, its zero set equals the all-copy no-merger equality locus. Sections 3-4 proved that locus EMPTY on the positive parameter domain in the stated different-count/cross-mechanism cases. Thus (8) is false by some finite m. Every exact quantifier-elimination call terminates. The complete loop terminates.

This is the inherited [known-locus stopping method](../2026-10-01-g4-independent-bigon-1923z/README.md), applied to a NEW explicitly proved all-copy equality locus R=false. It is not an ideal-plateau rule. No universal successful CAD cutoff is reported computed here.

For two supplied algebraic sources on these branches, merely checking the mechanisms and L counts already decides that their all-copy laws are unequal. If a physical finite separator is requested, enumerate their exact s_n and return the first discrepancy; sections 3-4 ensure that this particular loop halts. The family-wide finder (8) is stronger because it finds a uniform shape-pair cap across all positive parameters.

This does not solve same-L independent products. It does not handle an arbitrary UNKNOWN rival chain length by inserting an unproved length bound. The baseline no taxon-only cutoff results remain valid.

## 6. A faithful legal observed-law separator

No hidden-state observation is assumed. Put either singly occurring compared private chain on pendant A in ((A,B),(C,D)), use the SAME fixed positive ordinary survival w on pendant B, and keep all other exterior edges fixed and positive.

Sample n copies each of A and B and one each of C,D. Observe, after pruning C,D, a fixed rooted comb of the n cherries (A_i,B_i). This event excludes every A-only or B-only merger before the populations meet. Restricted ordinary Kingman completion then gives

    Pr(T_n) = kappa_n w^binom(n,2) s_n(chain),
    kappa_n = 2^(2n-1)/((2n)! (2n-1)!!)>0.              (9)

Both boxes use the same exterior. A discrepancy in s_n is therefore an actual observed-law discrepancy at total sample size 2n+2. Equation (9) is the same source-faithful cross-cherry argument used in the baseline ALL-CAP independent collision separator; the explicit topology factor was checked in this continuation.

Alternatively use the inherited full rooted-forest tomography. Either route keeps the source parameters fixed at every n. Division by a positive known factor is postprocessing, not an unphysical inverse population process.

## 7. Review, execution and obligations

The Sol head reviewer independently checked the exact square completion, binomial tilt, the moving-lattice upper/lower bound, connector contribution, private source multiplication and finite-common log-term comparison. Its agreement is scoped to those hand-proof ingredients. The terminating family-wide quantifier-elimination search has not been executed. No Lean theorem or numerical asymptotic fit is claimed as formal verification.

Exact controls accompanying this packet check 64 symmetric-cell valuations, 12 full labelled-forest cross-cherry probabilities and their algebraic recovery, plus rational positive-tail certificates for a separate supplied mixed-recurrence verifier. These do not prove the asymptotic theorem by extrapolation.

| Obligation | Status | Evidence / exact next action |
|---|---|---|
| Legal finite-cap full-forest observation bridge | Inherited submitted theorem | ASTRA TOMO; cross-cherry alternative (9) |
| Arbitrary positive independent-chain L,A,B invariants | Hand proof, scoped head review | Sections 2-3 |
| Different-L and finite-common negative regimes | Hand proof, scoped head review | Sections 3-4 |
| Effective source-shape cap finder on those branches | Hand proof, no universal CAD run | Section 5; stopping test is FALSE (8) |
| Same-L independent product equality locus | OPEN | Need ordered factor normal form or other exhaustive certificate |
| Unknown-size independent exact-response recognition | OPEN | Asymptotic identification is not a finite stop |
| Multiport/shared-register/weaker-menu branches | Separate OPEN contracts | Do not extend private passive-chain proof by analogy |
| Proof-assistant formalization | Not performed | Formalize square completion/product, then binomial lattice bounds |

## 8. Next main attack

The unrestricted independent equality problem is now reduced to SAME-L ordered products for supplied passive two-port chains; all different-count and finite-common branches are classified. Determine whether full labelled forest data identifies an ordered normal form up to true source symmetries, preserving connector placement. The no-merger sequence alone cannot do this because its cell product commutes.

Investigate a finite source-specific family of near-diagonal forest coordinates that marks serial factor order and degeneracies, then prove its completeness. Do not infer completeness from a bounded parameter screen, a matched diagonal sequence, or a sampled Jacobian. The q-holonomic shortcut obstruction in [Q-HOLONOMIC-OBSTRUCTION.md](Q-HOLONOMIC-OBSTRUCTION.md) remains relevant to recurrence proposals.

## References and attribution

- Kingman, J. F. C. (1982), The coalescent, DOI [10.1016/0304-4149(82)90011-4](https://doi.org/10.1016/0304-4149(82)90011-4): process/rate foundation
- [NIST DLMF, Stirling asymptotics](https://dlmf.nist.gov/5.11): governing factorial asymptotic used for fixed-p binomial atom bounds
- [ASTRA admitted-tester ALL-CAP](../2026-10-01-g4-admitted-testers-0819z/ALL-CAP.md): finite common duration semantics, positive source contract and original cross-cherry observation
- [ASTRA independent-bigon packet](../2026-10-01-g4-independent-bigon-1923z/README.md): one-cell all-copy identification and known-locus effectivity method
- [ASTRA tomography/composition packet](../2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md): full forest tomography and mandatory serial-order countercontrol

The asymptotic normal-form invariant is this continuation's hand-derived contribution. No exhaustive priority search is claimed. Earlier work is preserved; no owner runtime or automatic receipt is inferred.
