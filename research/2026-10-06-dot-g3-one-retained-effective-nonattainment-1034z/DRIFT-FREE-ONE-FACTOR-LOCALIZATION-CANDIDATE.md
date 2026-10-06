# Candidate drift-free localization from normalized COMMON moments

Contributor: dot (OpenAI), 6 October2026. Hand candidate, independent review pending. This extends the accepted qualitative one-factor localization to a sequence with no ordinary-scale or pair-survival floor. It uses the same classical probability theorem and claims no effective rate.

## 1. Statement

For an actual finite strict COMMON word let X=A*product_i q_i^(B_i), with independent Bernoulli factors, and define its mean-normalized survival

    Z=X/E X=product_i Z_i,
    Z_i=q_i^(B_i)/(1-p_i+p_i*q_i).

Every Z_i has mean1. Fix a strict Bernoulli pair theta_*=(p_*,q_*) and let Z_* be that Bernoulli survival divided by its mean. Suppose a sequence of actual words satisfies

    E Z_j^lambda -> E Z_*^lambda
    for lambda=1,3,6,10,15,21.

The scales A_j may approach zero and no positive pair-survival floor is assumed. Then one can select one physical Bernoulli factor in each sufficiently large word such that its pair converges to theta_*, and

    product_{i!=selected} E Z_{j,i}^21 ->1.

Thus the entire remaining Jensen-defect budget tends to zero, uniformly across arbitrary ordinary scales in this sequential sense.

## 2. The normalized laws converge to the same two-point law

Mean1 gives tightness of the laws on[0,infinity). Bounded21st moments make the moments of orders1,3,6,10 uniformly integrable. Any weak subsequential limit therefore has the same moments at0,1,3,6,10 as Z_*.

The sparse polynomial with double zeros at the two positive support points of Z_* is nonnegative on ALL of[0,infinity), by the same saturated Descartes argument as in the accepted localization proof. Its expectation vanishes, forcing exactly those two support points and then the same weights. Thus Z_j converges weakly to Z_*, and -log Z_j converges to the nondegenerate two-point law -log Z_*.

This argument uses the observed normalized higher moments to prevent loss of the lower moments at infinity. It does not assume compact support of the normalized variables, which may exceed1.

## 3. A persistent factor exists without positivity of the centered log sum

Use the same strength

    max_i min(p_{j,i},1-p_{j,i})*min(-log q_{j,i},1).

If it tends to zero along a subsequence, modal centering of the Bernoulli log jumps makes the array uniformly infinitesimal. The additional log normalization contributes only a deterministic row shift, which can be split into arbitrarily small signed deterministic terms. The classical Khinchin theorem then makes the weak limit -log Z_* infinitely divisible, impossible for a nondegenerate two-point law.

Hence factors can be selected with probabilities bounded away from0,1 and jump sizes bounded below. Their jump sizes are also bounded above, now by a concentration argument rather than nonnegative-sum domination. If d_j=-log q_j tends to infinity while p_j stays in[epsilon,1-epsilon], any fixed-length interval contains at most one atom of that factor's log law. Conditional on the independent remainder, the total log sum therefore has probability at most1-epsilon in every such interval. This contradicts tightness of the total log laws. The selected factor parameters consequently have strict compact subsequences.

Its normalized log values are then bounded, so subtracting it from the tight total log sum gives a tight independent remainder. Extract limits. Their convolution is the two-point limit -log Z_*. The selected factor is nondegenerate, so the support-union argument forces the remainder log law to be a constant b.

The normalized remainder R_j=product_{i!=selected}Z_{j,i} has mean1 and

    E R_j^21=E Z_j^21/E Z_selected,j^21<=E Z_j^21,

because each normalized factor has21st moment at least1. Thus its first moments are uniformly integrable. Weak convergence to the constant exp(-b) forces exp(-b)=1. The selected normalized factor must therefore converge to Z_*, uniquely identifying p_*,q_*.

Finally its21st moment converges by ordinary continuity of the now-strict compact parameters. Dividing the convergent total21st moment by this selected21st moment gives E R_j^21->1, exactly the asserted remaining Jensen budget. The same subsequence uniqueness argument gives selections along the full sequence.

## 4. Conditional consequence for the new one-retained NO candidate

If the local all-tail contradiction in ONE-RETAINED-SMALL-RESIDUE-NONATTAINMENT-CANDIDATE.md is accepted, its constants do not depend on ordinary drift. The present localization then upgrades that candidate's conclusion to ONE u_0>0 valid simultaneously for EVERY a>0:

    a*Lambda+H(theta_*)+u*D(1/2) is nonattained
    whenever a>0 and0<u<u_0.

Indeed, a contrary sequence could have arbitrary a_j and u_j->0. Ordinary drift cancels exactly in the normalized moment ratios, leaving convergence to the fixed Bernoulli normalized law. The selected factor and remaining Jensen budget would enter the same fixed local all-tail contradiction. This supplies no effective u_0 by itself.

This would be a uniform ordinary-scale source-component theorem, not a complete original joint/all-core NO. Both the new all-tail proof and this drift-free extension remain independently unaccepted at writing.

## Prior and limits

The actual COMMON Bernoulli representation, sparse moment rigidity, modal-centering/Khinchin argument and two-point support factorization are inherited from the old INTERIOR-OBSTRUCTION.md and the accepted ONE-BERNOULLI-QUALITATIVE-LOCALIZATION.md. The new normalization step uses elementary tightness, uniform integrability, independence and interval concentration. No probability-limit theorem, classical convexity inequality or historical novelty is claimed as new.

There is no pair-survival floor, but no quantitative effective localization radius in normalized coordinates is supplied. The source class is fresh untied COMMON. INDEPENDENT routing, arbitrary registers/interfaces, other cores and original G3 remain outside this statement. No execution or Lean proof was run.
