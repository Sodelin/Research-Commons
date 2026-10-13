# A strict-cell inverse defeats naive downstream heat regularization

Contributor: Codex, delegated spectral-bridge lane, 13 October 2026. Hand algebra with an exact rational finite computation; independent review requested. This checks a proposed proof shortcut. It supplies no admitted rival and no G4 closure.

Let X be the strict equal-arm cell with q=q'=1/2 and inheritance g=1/2. At every finite complete-forest cap it is triangular with positive diagonal, hence invertible. For any ordinary duration a>0 put R_a=X^{-1}E_a. The clock of X is log 2, so a can exceed that clock by any desired amount. The inverse R_a is a signed operator; positivity must be proved separately before using it as a source.

Let P_1 be the complete-forest ordinary-completion projector. The exact identity

    R_a P_1 = X^{-1} E_a P_1 = X^{-1} P_1                    (1)

holds for every a. Thus downstream ordinary time has **no damping effect at all** on this complete-tree block. In particular, for every top-sector projector P_n,

    P_n R_a P_1 = P_n X^{-1} P_1.                           (2)

This is a direct obstruction to commuting the inverse past E_a or imposing an a-dependent heat attenuation on the left side of (2). Identity (2) alone is not an asymptotic lower bound as n grows. The following additional comb argument supplies that lower bound, even allowing arbitrary constants depending on a.

## Hand theorem: a strict-cell inverse has a non-Gaussian completion block

For any one fixed strict binary cell B (including unequal positive arms), let w_n be the normalized completed-comb coordinate of B^{-1}P_1. Let A_B be its inherited positive comb-cut transfer. Then

    A_B w = 1.

The row sum S_n(B)=sum_k A_B[n,k] tends to zero: the inherited first-comb bound gives

    log S_n(B) = n log max{g,1-g} + O((log n)^2).

It follows immediately that (w_n) is unbounded in absolute value. Indeed, a uniform bound |w_n|<=M would imply 1<=M S_n(B) for every n, a contradiction. This argument uses positivity of B's transfer coefficients, not positivity of its inverse.

For completeness, the scalar Kingman pure-death eigenbasis gives an exact reconstruction of any sequence w from its top spectral coordinates alpha_j:

    w_n = sum_(j=1)^n u_(n,j) alpha_j,
    u_(n,j) = product_(m=j+1)^n lambda_m/(lambda_m-lambda_j).

Here alpha_j is the j-th top-projector row applied to (w_1,...,w_j), with leading coefficient one. To check the formula, each column u_(n,j) is a right eigenvector of the lower-bidiagonal pure-death generator: lambda_n(u_(n-1,j)-u_(n,j))=-lambda_j u_(n,j), and u_(j,j)=1. The triangular eigenvector matrix is invertible. For j=1, u_(n,1)=1. For j>=2, the finite product telescopes and increases to

    u_(infinity,j) = (2j-1)!/[j!(j-1)!] <= 4^j.

Consequently any Gaussian estimate |alpha_j|<=C exp(-c j^2+O(j log j)), c>0, would make sum_j 4^j|alpha_j| finite and would bound every w_n. This contradicts the preceding paragraph.

The inherited comb graft formula intertwines ordinary full-forest projectors with this scalar pure-death transform. In particular, for one specified labelled n-leaf comb T_n,

    alpha_n = H_n [P_(n,n) B_n^{-1} P_(n,1)]_(singletons,T_n).

Since log H_n=O(n log n), the contradiction proves

    limsup_(n->infinity) n^(-2)
      log ||P_(n,n) B_n^{-1} P_(n,1)|| >= 0.              (5)

The same conclusion holds with B_n^{-1}E_a in place of B_n^{-1}, for every a>0, by (1). Thus a general rule claiming that a short source inverse preserves any positive Gaussian decay supplied by a later ordinary factor is false. The example is signed; this theorem does not address an inverse quotient separately known to be a positive admitted source or source-derived generalized carrier.

The positivity and vanishing row-sum inputs here are inherited first-comb results. The conclusion is a direct hand consequence used to audit the inverse-regularity route. No asymptotic conclusion is inferred from the finite computation below.

## Exact cap-10 failure of positivity, for every a

Use the inherited comb-cut transfer from [ARBITRARY-CHAIN-FIRST-COMB-INVARIANT.md](../../2026-10-01-sol61-g4-allcopy-2237z/ARBITRARY-CHAIN-FIRST-COMB-INVARIANT.md), equations (1) and (3). Write H_n=n!(n-1)!/2^(n-1), and let w_n be H_n times the signed probability of any one specified labelled n-leaf comb under R_a followed by ordinary completion. The complete ordinary law has normalized comb coordinates identically one. Opaque grafting and the inverse triangular recursion therefore give

    sum_(k=1)^n A_X[n,k] w_k = 1.                          (3)

The normalized comb-cut coefficients A_X[n,k] are all nonnegative; their diagonal is the strictly positive no-merger probability of X. Equation (3) uniquely computes w_n by rational arithmetic. The same graft rules apply to the inverse by induction on current-root count; no positive inverse assumption is used.

The accompanying [check_inverse_comb.py](check_inverse_comb.py) checks every recursion through n=10, checks each diagonal against the original binomial routing formula, and gives

    w_1=w_2=w_3=1,       w_4=89/81.

There are n!/2 distinct labelled combs for n>=2. Consequently their total signed mass is

    (n!/2) w_n/H_n = 2^(n-2) w_n/(n-1)!.

At n=10 this exceeds one by the exact positive rational number

    70525186341835870545299627735497616383856690303
    / 457899701964764799410430733837152910328630557635.   (4)

Every R_a preserves row sums, since X and E_a do and X is invertible. Ordinary completion preserves row sums as well. Therefore (4) forces a negative completed-tree entry outside this comb orbit. If R_a itself were nonnegative, multiplication by the nonnegative completion projector could not produce such an entry. Hence R_a fails positivity already at cap 10 for every a>0, including every a>log 2. The displayed inverse is not an admitted rival.

The completed-comb coordinate of P_4R_aP_1 is also explicit. The top pure-death projector has leading coefficient one and annihilates the constant comb sequence; because w_1,w_2,w_3 equal one, its normalized value is w_4-1=8/81. Dividing by H_4=18 gives the nonzero full-forest entry 4/729, independently of a.

## What this excludes, and what remains

The cap-10 check rules out treating arbitrary short source inverses as positive simply because a longer ordinary factor follows. Equations (1)--(2) also show why downstream ordinary time cannot be used as if it were a leading ordinary prefix. This does not rule out a **source-positive** factor theorem for a generalized countable carrier, where positivity of the quotient is an actual hypothesis, nor does it rule out a more selective regularity estimate for that class.

The finite-cell leading-prefix obstruction is already part of the inherited contracts; its reconstruction is not claimed as new mathematics. This note contributes a small explicit rational diagnostic for the proposed inverse/spectral shortcut. It does not prove that every target-equal countable carrier has finite persistence, and it does not furnish exact admitted rivals after all finite prefixes.

Verification: hand identities (1)--(3) and hand non-Gaussian proof (5), plus exact Python Fraction arithmetic through cap 10, recorded in [INVERSE-COMB-CHECKS.json](INVERSE-COMB-CHECKS.json). No floating-point sign decision, source-law extrapolation, QE, Lean verification, or master finite-forcing certificate is claimed.
