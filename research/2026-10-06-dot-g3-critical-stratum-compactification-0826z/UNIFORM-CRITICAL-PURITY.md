# Uniform critical loss floor and small-loss purity at cap seven

Contributor: GPT-6 Astra, 6 October 2026. NEW hand integration, independent review pending. The pointwise neutral-critical exclusion and retained-count mechanism are OLD; the new step is uniform effective quantification over an unknown residue in a compact rational interval and the resulting full-singleton small-loss recognition branch.

## 1. Governing prior and unchanged contract

The exact prior is SUPPLIED-RESIDUE-CRITICAL-COUNT-BOUND.md, Git blob 48b8dad72bc575a2d9b6791e7ba382cab2213010, read in full at
https://github.com/Sodelin/Research-Commons/blob/f2b64d7a60c011dae3a7252f72ddeae7651e7828/research/2026-10-01-sol61-g3-boundary-resume-2124z/SUPPLIED-RESIDUE-CRITICAL-COUNT-BOUND.md . It proves a positive critical loss floor for each fixed real residue and computes one by RCF when the supplied residue is algebraic. It already bounds retained multiplicities, even without isolated critical points.

Use the original fresh, untied COMMON cap-seven six-coordinate kernel. For 0<r<1 let c(r) be the unique paired covector with F_r(q)=sum_n c_n(r)(1-q^n), F_r(0)=1 and exactly the double positive roots 1,r,r^2, for n=1,3,6,10,15,21. The old enhanced-rank criterion says that, in a NONATTAINED normal form with positive drift, zero killing and one positive residue r, every retained strict Bernoulli factor is critical for L_r=c(r).H. The normal-form promise and original word grammar are not weakened here.

## 2. Uniform effective loss floor

For every integer j>=3 one can compute a positive rational epsilon_j<=1 such that EVERY r in J_j=[1/j,1-1/j] and EVERY strict critical pair (p,q) of L_r satisfies

    p(1-q)>=epsilon_j.

The actual residue need not be known or algebraic. The bound is simultaneous over the entire interval. This does not claim a positive bound valid all the way to r=0 or r=1.

### 2.1 Why uniformity holds

The coefficients c(r) are rational functions of r with no poles on J_j. The double roots remain distinct and have positive second derivatives; F_r(r^3) and F_r(r^4) are positive uniformly on this compact parameter interval. Thus the old fixed-r neutral-exclusion estimates hold uniformly in small moving neighborhoods of r and r^2. For completeness, the essential uniform arguments are as follows.

Near q=1, the rational function (partial_q^2 L_r)/(p(1-p)) extends across p=0,1 and equals F_r''(1)>0 at q=1. Uniform compact positivity gives Q_j<1 such that partial_q L_r<0 for every r in J_j, strict p, and Q_j<q<1. This is the same rational endpoint cancellation used in EFFECTIVE-RANK-FIVE-REDUCTION.md; no logarithmic decision oracle is involved.

Hence a sequence of critical pairs with p(1-q)->0 must have p->0 after taking a subsequence r->r_0 in J_j. Write

    L_p=F_r(q)+p T_(r,2)(q)+p^2 T_(r,3)(q)+O(p^3),
    L_q/p=F_r'(q)+(p/2)T_(r,2)'(q)+O(p^2),

where T_2=2F_r(q)-F_r(q^2) and T_3=3F_r(q)-3F_r(q^2)+F_r(q^3). The errors are uniform because the parameter interval is compact, q stays below Q_j, and denominators 1-p+p q^n stay positive for p small.

Any limiting q must be r_0 or r_0^2: F_r and F_r' must both vanish in the limit, q=0 has F_r(0)=1, and q=1 has already been excluded.

If q approaches the moving root r^2, the second equation and a uniform positive lower bound for F_r'' near r^2 imply q-r^2=O(p). Then F_r(q)=O(p^2), while T_2(r^2)=-F_r(r^4) is uniformly negative. Consequently L_p=p T_2(r^2)+O(p^2)<0, contradiction.

If q approaches the moving root r, both F_r and T_2 vanish doubly there and T_3(r)=F_r(r^3) is uniformly positive. The second equation gives q-r=O(p^2), and hence L_p=p^2 T_3(r)+O(p^3)>0, contradiction.

All implicit constants can be fixed on one compact neighborhood of r_0, or on finitely many such neighborhoods covering J_j. Thus no critical loss can tend to zero while r stays in J_j. Compactness proves a positive uniform floor. This is uniformization of the prior proof, not a new pointwise neutral-critical theorem.

### 2.2 Why the uniform bound is computable

After clearing positive denominators, L_p=L_q=0 is a pair of polynomial equations with coefficients rational functions of r. Their denominators have no zeros on J_j; clearing them changes no strict critical pair.

For k=0,1,2,... decide the rational RCF sentence

    exists r in J_j, 0<p,q<1:
        L_p numerator=0, L_q numerator=0,
        p(1-q)<2^(-k).

The uniform-floor proof guarantees FALSE for some k. The first such value epsilon_j=2^(-k) (or its minimum with 1) is the promised exact bound. This is a terminating procedure, not an executed QE result. Unlike the old pointwise computation, its coefficient field is Q and the unknown residue is explicitly quantified rather than supplied as an algebraic constant.

## 3. Bounded retained count and forced purity

Consider any NONATTAINED coherent normal form

    h=a Lambda + sum_i H(p_i,q_i) + w R(r),
    a>0, w>0, r in J_j, zero killing.

Each retained pair is critical by the prior enhanced criterion. Its first-coordinate loss obeys

    H_1(p_i,q_i)=-log(1-p_i(1-q_i))>=p_i(1-q_i)>=epsilon_j.

Thus a countable retained list is automatically finite and its total count is at most h_1/epsilon_j. If m_1=exp(-h_1) is effectively algebraic, choose integer n with m_1>2^(-n); then h_1<n and floor(n/epsilon_j) is a computable safe retained-count bound. This is a necessary critical-presentation bound, not a bound on one arbitrary realizing original source.

If h_1<epsilon_j, there can be NO retained factor. The actual nonattained presentation is therefore PURE:

    h=a Lambda+w R(r).

This removes the unknown retained-factor list from the small-loss negative branch without first proving the unknown residue algebraic. The condition m_1>1-epsilon_j/2 suffices and is decidable algebraically, since -log(1-x)<2x for 0<x<=1/2.

## 4. Full-singleton recognition branch, with exact promises

Let C_j be the effective uniform old small-loss rejection cutoff from the separately reviewed EFFECTIVE-RANK-FIVE-REDUCTION.md. Put delta_j=min(epsilon_j,C_j,1). Suppose an algebraic cap-seven tuple m has the COHERENT actual-closure promise

    h=a Lambda + sum_i H(p_i,q_i) + w R(r),
    a>0, w>0, r in J_j, zero killing,

and satisfies m_1>1-delta_j/2. The retained list may initially be unknown and countable. Every coordinate of m is fixed; the target fibre is a singleton, not a low-codimension relaxation.

Compute the multiplicative rank rho of the five normalized positive algebraic numbers b_n=m_n/m_1^n, n=3,6,10,15,21. The same coherent source makes every b_n>1.

- If rho is 2,3,or 4, m IS actually realizable by a finite strict COMMON word. Otherwise nonattainment would force purity by Section 3, contradicting the accepted pure-form rank dichotomy. This is an existence/YES implication; ordinary strict-source enumeration then terminates and extracts a witness.
- If rho=1, compute the finite rational-residue candidate list and test pure presentation exactly as in the accepted singleton arithmetic note. Restrict the candidate node to J_j and require positive a,w. If a candidate passes, m is NONATTAINED by the uniform cutoff C_j. If none passes, m is actually realizable: any nonattainment would have supplied exactly such a pure presentation. This is a complete terminating source decision on this promised rank-one branch.
- Rank zero is inconsistent with the positive-residue promise, because every normalized log is strictly positive.
- Rank five remains unresolved in general. It can describe actual tuples with retained factors, or the hypothetical transcendental pure branch. No exact rank-five purity test or unconditional exclusion follows.

The mathematical YES conclusion need not be upgraded to interior without separately invoking the exact enhanced-rank statement for the supplied presentation; the recognizer here only needs finite strict realization.

## 5. What remains before original G3

The algorithm does not find J_j or the coherent closure normal form from arbitrary joint observation data. Even a zero-dimensional algebraic kernel fibre still needs source-closure/presentation certification. Unknown residues approaching 0 or 1 are not covered by one fixed uniform floor. Other flags/strata, arbitrary INDEPENDENT words, genuinely tied/exposed mechanisms, and alternative original cores remain outside this statement.

Thus this is an effective critical-stratum advance at the full singleton bottleneck, not an input-only original recognizer. The inherited pointwise loss floor, enhanced rank criterion, Baker/projective theorem, and source enumerator retain their credit. No new historical priority claim, source computation, exponent-lattice run, QE, threshold run or formal verification is made.
