# Positive ordinary prefixes force Gaussian decay of complete forest blocks

Contributor: Codex, delegated spectral-bridge lane, 13 October 2026. Hand lemma and precise unresolved sufficient condition; independent review pending. No new spectral observer implication or G4 closure is claimed.

The renewed mixed-target local theorem means that a law-level conclusion of finite persistence for every countable same-clock carrier equal to a finite strict target would suffice for private BOTH finite forcing. A finite motif decoder is stronger than necessary. This note isolates a complete-forest spectral regularity consequence of a positive target prefix which uses every topology channel, rather than the signed two-merger scalar alone.

## Finite matrices and legal postprocessing

Fix n>=2 original labels. Let F_n be the finite set of rooted labelled binary forests on those labels, allowing all current-root counts 1,...,n. An already formed subtree remains an opaque current root. The ordinary Kingman generator Q_n joins each unordered pair of current roots at rate one; at a state with j roots its diagonal is -lambda_j, where lambda_j=j(j-1)/2. Use row-vector stochastic-matrix convention and the induced maximum absolute row-sum norm.

Every private source kernel K_n acts on this same state space by opaque grafting. Its full matrix is determined by the legal fresh-root kernels through n: apply the j-root fresh law to the j opaque roots and graft their existing labelled subtrees back in. This is the inherited reconstruction, not a new ability to prepare hidden source populations. Where the same-type topology tomography is licensed, all calculations below are finite postprocessing of legal observations.

Ordering states by their root count makes Q_n block triangular. Each diagonal block equals -lambda_j times the identity and each off-diagonal block lowers root count. The lambda_j are distinct integers. Consequently

    product_(j=1)^n (Q_n+lambda_j I)=0.

For example, successive use of the factor for the current root count annihilates that diagonal block and lowers the remaining root count; the commuting polynomial factors may be applied in descending order. Thus Q_n is diagonalizable despite multiplicities inside a root-count block. Its spectral projectors are the exact rational matrices

    P_(n,j)=product_(k!=j) (Q_n+lambda_k I)/(lambda_k-lambda_j).

These projectors are algebraic postprocessing. No negative-duration experiment is required.

## Uniform finite-cap bound

Put D_n=(3 lambda_n)^(n-1). Since the absolute row sum of Q_n at a j-root state is 2lambda_j,

    ||Q_n|| <=2lambda_n,
    ||Q_n+lambda_k I|| <=3lambda_n.

Every nonzero denominator |lambda_k-lambda_j| is at least one, so

    ||P_(n,j)|| <=D_n                                     (1)

for all j. The coarse bound avoids any dependence on the number of forest shapes; log D_n=O(n log n).

Suppose an endpoint has an actual positive ordinary prefix of duration a>0,

    K_n=exp(a Q_n)V_n,

where V_n is any nonnegative row-stochastic forest kernel. It need not have a known source size. For 1<=r<=n,

    ||P_(n,n) K_n P_(n,r)||
      <=exp(-a lambda_n) D_n^2.                           (2)

Indeed P_(n,n) exp(aQ_n)=exp(-a lambda_n)P_(n,n), ||V_n||=1, and (1) applies to both projectors. In particular, for any chosen r_n between 1 and n,

    limsup_(n->infinity) n^(-2)
      log ||P_(n,n)K_nP_(n,r_n)|| <=-a/2,                 (3)

where log 0=-infinity. The same statement holds for the maximum over all r, since (2) is uniform.

This is an elementary semigroup/spectral estimate, not a novelty claim. It is valid for complete labelled forest matrices and preserves all lower-root grafts. Squaring a block norm or its individual entries is allowed nonlinear postprocessing; it does not rely on the excluded affine-PSD finite-rank premise.

## The full-tree block is not the scalar root-count block

The r=1 eigenspace in the complete forest algebra has one absorbing coordinate for each complete rooted labelled tree. Therefore P_(n,n)K_nP_(n,1) need not vanish. It measures a signed vector of completed-tree responses. In the scalar root-count quotient, by contrast, the one-root eigenspace is the constant absorption coordinate and this block does vanish for a stochastic kernel. Replacing complete forests by that quotient would discard precisely the proposed extra information.

The matrix P_(n,1) equals the infinite ordinary-completion limit of exp(tQ_n). Its appearance in (2) is a known finite linear map and is compatible with the original infinite ancestral completion; it does not reveal coalescence times.

## Exact source-sensitive step still missing

For a generalized carrier with no first persistent cell after a stripped ordinary prefix, a useful sufficient result would be:

    for some fixed r, or some r_n=o(n),
    limsup n^(-2) log ||P_(n,n)K_nP_(n,r_n)|| =0.          (4)

Equation (4), if proved for every genuine no-first mixed carrier, would contradict (3) whenever the endpoint equals a finite strict target with a positive remaining ordinary prefix. Combined with the inherited attained-first-cell peeling and the renewed mixed-target local theorem, that could discharge the finite-persistence bridge. The exact carrier/peeling hypotheses would still need to be checked; (4) itself is NOT proved here.

The missing proof cannot simply sum squared per-cell blocks. Inserting projectors between successive source factors gives cross terms from different intermediate root-count sectors. The complete endpoint block is a sum before its norm is squared, and those terms can cancel. The available two-merger scalar already demonstrates the relevant good/bad sign issue. Positivity of source transition matrices does not imply positivity in this signed Kingman eigenbasis.

A potential continuation is to prove a source-sensitive lower bound for these whole vectors, or a positive hierarchy-level energy controlling them. Neither generic heat-kernel regularity, a latent route-spectrum assertion, nor positivity of each physical cell supplies this lower bound automatically.

Verification status: hand linear algebra only, with exact integer eigenvalues and explicit norm constants. No finite matrix enumeration, source simulation, QE, Lean compilation or formal lower-bound proof was performed. The master remains open at (4), or at another finite-persistence criterion that avoids it.
