# Enhanced residue/retained-factor criterion for exact common-source attainment

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 01:34 UTC.
Status: the global criterion and EVERY-normal-form annihilator strengthening passed the current head's independent hand challenge; the single rational rank witness was executed locally and the head's independent replay matched all four printed scalar fields. The immutable public receipt is coordinated separately. It strengthens the differential-annihilator characterization by a new square-node pair. It does not decide arbitrary input-only membership or bound total retained multiplicity.

## Contract and statement

Fix a finite cap M, d=M-1 and the Kingman exponents lambda_l. Use the accepted finite-log actual-closure normal form

    h=a lambda+kappa 1+sum_i H(p_i,q_i)+sum_(j=1)^s w_j R(r_j),

with s>=1 distinct interior r_j, positive w_j, strict retained pairs and a,kappa>=0. The retained list may be countable and summable; only a finite subset will vary. Let alpha,beta indicate the active positive a,kappa and let rho be the smallest residual node. The actual source retains its strict positive baseline and Bernoulli contract; this normal form may have endpoints.

Form the following response-column family:

    lambda if alpha=1; 1 if beta=1;
    R(r_j), w_j R'(r_j) for every residual node;
    H_p(p_i,q_i), H_q(p_i,q_i) for every retained pair;
    D(rho^2), D'(rho^2)/2,

where D(q)=1-q^lambda, H_p=(1-q^lambda)/(1-p+p q^lambda) and H_q=-p lambda q^(lambda-1)/(1-p+p q^lambda), coordinatewise.

If these columns span R^d, then h is in the INTERIOR of the actual finite strict source image. It is enough that one finite retained subset gives full row rank. Every additional fixed closure term can be retained in the proof.

Consequently EVERY nonattained closure point, in EVERY normal form with s>=1, admits a nonzero covector c annihilating ALL columns above. In addition to the earlier retained critical equations and original-node double roots, its sparse polynomial F_c(x)=sum c_l(1-x^lambda_l) has an EXTRA double root at rho^2. This is a global necessary condition; c is a differential annihilator, not a claimed global linear separator.

## Exact desingularization with existing strict factors

Choose a finite subset of retained pairs whose columns, together with the other finite columns, give full row rank. Allow order-t^3 corrections to those probabilities and ratios, all residual weights/nodes and active a,kappa. Inactive endpoint coefficients remain exactly zero. Add a first strict factor with odds t at rho and a second with odds t^2(1/2+t u) at rho^2+t xi. Subtract t(1-rho) from the residual weight at rho.

The corrected normal-form log signature minus the target is analytically divisible by t^3. The t D(rho) terms cancel against the removed residue weight; the second factor cancels the first factor's -t^2 D(rho^2)/2 term. Varying a residual node by t^3 changes the order-t weight correction only at order t^4. Retained strict-pair corrections contribute their ordinary analytic derivatives at order t^3. Thus the t=0 equation is

    J y+D(rho^3)/3=0,

with precisely the listed response columns. The second-node column is D'(rho^2)/2 because the second odds have leading coefficient1/2; rho^2 is an independent node variable, so no extra2rho enters this column.

If J has full row rank, choose a nonsingular d-column pivot. Set other correction variables to zero and solve the pivot variables at t=0. The analytic IFT supplies a finite analytic solution near t=0. For sufficiently small positive t, all originally strict retained probabilities/ratios stay strict, all active coefficients and residual weights stay positive, all residue nodes remain distinct and interior, and the two added factors have strict odds/nodes. Inactive a/kappa endpoints stay fixed. The entire corrected normal form is EXACTLY h.

At such t, vary the genuine normal-form physical parameters in the selected block. The second-factor odds derivative tends to D(rho^2), and its node derivative divided by its positive odds tends to D'(rho^2). The remaining columns tend to their original retained/residue/active-coefficient values. Nonzero column scaling is harmless. Full row rank therefore persists at sufficiently small positive t. These are two-sided variations inside the admitted normal-form domains, with every unselected summable tail fixed. Submersion puts h in int(C); the independently accepted int(C)=int(S) then gives actual finite strict-source interior. This is an exact existence theorem, not a Poisson approximation or an extracted source factor list.

If the full response family does not span R^d, its linear span is a proper finite-dimensional subspace and has a common nonzero annihilator. Since any full span would already have a finite basis, this conclusion also applies to countably many retained factors. R/R' imply original-node double roots. D/D' imply the new square-node double root. Active drift gives a double root at1; active killing removes the constant coefficient. The retained derivatives give the same cleared polynomial critical equations as SINGULAR-NORMAL-FORMS.md. This proves the stated necessary condition.

## Cap-seven reduction and computable supplied-data test

At M=7, with positive drift, zero killing and one residue r, the residue/active/new-square block has five independent columns

    lambda, R(r), R'(r), D(r^2), D'(r^2).

In the six-dimensional observation space its left nullspace is one-dimensional. Its normal F is exactly the sparse paired normal with double roots at1,r,r^2 from SMALL-LOSS-POISSON-NONATTAINMENT.md. Therefore a single retained factor for which either c.H_p or c.H_q is nonzero makes the enhanced block full row rank and places the entire point in int(S_7). A nonattained normal form of this type must have EVERY retained pair in that fixed normal's strict algebraic critical locus.

For supplied algebraic residual nodes and retained pairs, this response-rank criterion is decidable by exact algebraic arithmetic: all entries are rational functions at integer exponents; positive weights can be removed as nonzero column scales. It recognizes a source-faithful YES regime from its supplied normal-form data. It does not infer such data from an arbitrary observation tuple, turn a rank-deficient case into NO, or fix the unknown integer-multiplicity search.

An exact supplied-factor witness was checked with r=p=q=1/2. Using the prior rational F1 covector,

    c.H_p=264206472849574962397628/1724150400203654123597325>0;
    det[lambda,R,R',D(r^2),D'(r^2),H_p]
      =-1194657982825502877092734367331/170838271759546762430365101121863680.

Thus ANY a,w>0 signature a lambda+w R(1/2)+H(1/2,1/2) is in int(S_7) under this theorem. In particular, multiplying the previously rejected algebraic Poisson coordinates by(1+2^(-lambda))/2 gives an exact algebraic attained-interior tuple. The original NO point is not translated into another NO point by this source factor. No actual finite factor list is extracted from the IFT/interior existence argument.

At a general cap the same criterion restricts the remaining covectors to the nullspace of the active/residue/new-square block, then intersects their retained-factor critical conditions. The matched-cap theorem is the special case where that finite block already has full row rank without any retained factor. The new condition exposes how additional actual factors can regularize a previously nonattained Poisson point; it is not a new cap census.

## Verification and next action

The analytic/source transfer is a hand proof reusing the accepted uniform t^3 construction and actual-semigroup interior theorem. enhanced_retained_rank_check.py executed the single exact rational six-column rank witness above in Python fractions arithmetic, preserving its matrix, source normal hash and projections in enhanced-retained-rank-check.json. The finite check verifies rank, not the analytic/source theorem. No new solver, numerical fit or factor scan has been executed for this criterion. The head independently challenged and accepted the two-sided domains, order-t^3 retained corrections, fixed summable tail, rank persistence and common-annihilator implication. Its independent replay matched the CLI's four printed scalar fields; that CLI summary is distinct from the full matrix/result file. The immutable receipt is coordinated separately; no complete Lean theorem is implied.

The exact master gap remains input-only recognition: obtain an input-dependent finite search bound or a complete finite boundary certificate for all rank-deficient singular normal forms. The no-cap-only-factor-ceiling theorem remains in force.
