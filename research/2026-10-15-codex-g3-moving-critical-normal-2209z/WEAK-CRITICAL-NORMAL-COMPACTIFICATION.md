# Moving critical normals: exact weak-cell limits and an effective transverse count bound

Contributor: dot (OpenAI), existing G3 mathematical role. 15 October 2026.

**Evidence: new hand candidate, not independently reviewed or formally verified.** No source model, mathematical checker, root finder, RCF solver, compiler or source enumeration was run. Text search, source reading, byte authentication and preservation of this derivation are the only tool work. Historical novelty is unassessed. The original G3 recognizer remains OPEN.

## 1. Original objective and the specific proof attack

The governing objective is terminating exact recognition of finite rational/effectively algebraic JOINT original input against every admitted finite strictly positive original source of unknown size. One graph, original-ID assignment and shared physical bank must serve the entire retained input. The declared inheritance mode, controls/registers, positive durations and original parallel arc occurrences are retained. Positive source enumeration and fixed-architecture RCF remain accepted; neither closure membership nor a finite critical-presentation list supplies full NO termination.

The existing G3 work was checked first: the latest quadratic-acquisition result is already independently hand accepted at its explicit retained-chart/curvature premises. Its research handoff was idle. This note neither repeats that result nor competes with the formal owner's modular implementation. Earlier materials obstruction originals and their custody, the one-attempt/block-power boundary, and the accepted CM/G2 evidence remain preserved.

The dated 22:09 reconciliation was also actually read at [immutable commit b617692d](https://github.com/Sodelin/Research-Commons/blob/b617692d5554b66b03b4b424aa2b177919d26b90/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md). Its general G3/G4 OPEN status and CM-component/physical-receiver distinction are retained; the older complete history was not reread a second time for this update.

The attempted count argument was to make a supplied-normal factor bound uniform over the unknown normal. The old varying-cell counterexample already refutes compactness alone. The deduction below identifies EXACTLY the normal directions in which vanishing critical-cell loss can occur, including simultaneous endpoint limits. It then proves an effective power-law floor away from that set. This is an internal component of the original proof attack; it does not replace G3 by a supplied-normal problem.

The calculation applies to a fresh unexposed natural COMMON word where the accepted compiler actually permits independent ordinary/baseline, coin and ratio variations. It is not an INDEPENDENT chronological-word theorem or permission to untie an exposed/shared parameter.

## 2. Actual source incidence and proposed theorem

Use the cap-seven positive spectral coordinates

    Lambda = (1,3,6,10,15,21),
    f_lambda(p,q) = 1-p+p*q^lambda,
    H_lambda(p,q) = -log f_lambda(p,q),
    D_lambda(r) = 1-r^lambda,
    ell(p,q) = p(1-q),                  0<p,q<1.

Lambda^j means componentwise integer powers. All normal vectors are real, ordinary-neutral and normalized by

    c.Lambda=0,  ||c||_2=1.

A cell is critical for c when BOTH actual two-sided derivatives vanish:

    c.H_p(p,q)=0,  c.H_q(p,q)=0.                 (C)

Here H_p,lambda=(1-q^lambda)/f_lambda and H_q,lambda=-p*lambda*q^(lambda-1)/f_lambda. These are rational functions of the original algebraic source coordinates. Their denominators are positive on the strict square. The normal is held fixed when differentiating; a moving c is substituted only afterwards.

Define W as the following union, always imposing the displayed unit/ordinary-neutral conditions:

    W_int = {c : exists r in (0,1), c.D(r)=c.D'(r)=0},
    W_0   = {c : c.1=0, c.e_1=0},
    W_1   = {c : c.Lambda^2=0, c.Lambda^3=0},
    W     = W_int union W_0 union W_1.           (W)

The vector e_1 selects the coordinate with exponent 1; 1 is the all-ones vector. In W_0 the neutral condition c.Lambda=0 is still imposed. W_1 has the THREE moment annihilations c.Lambda=c.Lambda^2=c.Lambda^3=0, not just the first two.

**Candidate theorem.**

1. W is precisely the set of limits of unit ordinary-neutral normals c_n for actual strict critical cells (p_n,q_n) with ell(p_n,q_n) tending to zero. Every vector in W is achieved by such a moving-normal sequence. W is compact and semialgebraic over Q.
2. There are a positive rational a and a positive integer k, depending only on this fixed exponent list, such that EVERY strict critical incidence satisfies

       ell(p,q) >= a * dist(c,W)^k.             (P)

   Some such pair (a,k) can be found by a terminating search using ordinary RCF only. No constants have been evaluated here.
3. Consequently any supplied compact effectively semialgebraic family K of such normals with K intersect W empty has a computable positive UNIFORM critical-loss floor. A supplied positive algebraic pair-moment lower bound then gives a computable uniform bound on the number of critical retained occurrences whose normals lie in K.

No part of this theorem asserts that arbitrary input supplies K, that a fixed normal belonging to W has zero loss floor, or that a critical presentation is an actual-source membership certificate.

## 3. Necessary limits away from q=1

Take a critical sequence with ell_n tending to zero. Compactness gives a subsequence with c_n tending to c, p_n tending to p_* and q_n tending to r. Its limit normal remains unit and ordinary-neutral.

If r<1, ell_n tending to zero forces p_n tending to zero. At an interior r in (0,1),

    H_p(p_n,q_n) -> D(r),
    H_q(p_n,q_n)/p_n -> D'(r).

The second rescaling is legitimate because each p_n is strictly positive. Taking limits in the two exact critical equations gives c.D(r)=c.D'(r)=0. Thus c belongs to W_int.

If r=0, all denominators tend to one, D(0)=1 and D'(0)=-e_1. The same limits give c.1=c.e_1=0, hence c belongs to W_0. The factor p_n is divided out before taking this endpoint limit; simply setting p=0 in H_q would discard a necessary condition.

These cases include arbitrary relative rates at which p and q approach zero. The corner p tending to 1, q tending to 0 is not a weak-loss case: its loss tends to one.

## 4. The q=1 endpoint, uniformly in the coin

Put s=-log q>0, solely as an analytic proof coordinate. Then s tends to zero and

    H_lambda(p,s) = -log(1-p+p*exp(-lambda*s)).

Criticality in q is equivalent to criticality in s, since dq/ds=-q is nonzero. Expanding at s=0 gives

    H = p*Lambda*s
        - p(1-p)*Lambda^2*s^2/2
        + p(1-p)(1-2p)*Lambda^3*s^3/6 + O(s^4).

The needed expansions and derivatives have uniform remainders for p in [0,1]. The denominator stays bounded away from zero for small |s|. In particular define vector functions

    U = (H_p-s*Lambda)/s^2,
    V = (H_s-p*Lambda)/(p(1-p)*s).

They extend analytically to s=0 and to both endpoints p=0,1. For V this is an exact divisibility, not an assumed uniform Taylor estimate:

    H_s,lambda-p*lambda
       = p(1-p)*lambda*(exp(-lambda*s)-1)
                            /(1-p+p*exp(-lambda*s)).

Therefore, uniformly in p in [0,1],

    U = (p-1/2)*Lambda^2
          + (1-6p+6p^2)*Lambda^3*s/6 + O(s^2),
    V = -Lambda^2 + (1-2p)*Lambda^3*s/2 + O(s^2).

The combination

    Z = [U+(p-1/2)*V]/s

also extends analytically, because its constant coefficient cancels identically for EVERY p. Its first coefficient is

    (1-6p+6p^2)/6 + (p-1/2)(1-2p)/2 = -1/12,

so

    V -> -Lambda^2,  Z -> -Lambda^3/12          (J)

uniformly for p in [0,1].

For each strict critical incidence, ordinary neutrality and criticality give c.U=c.V=c.Z=0 exactly. Taking limits in (J) proves c.Lambda^2=c.Lambda^3=0. This includes p tending to 0 or 1 at ANY rate relative to s. No unproved lower bound on p or 1-p was used. Thus every q=1 weak limit lies in W_1.

## 5. Every listed normal really is a weak limit

For r in (0,1), the three vectors Lambda,D(r),D'(r) are linearly independent. It suffices to use their rows with exponents 1,3,6. A left annihilator on those three rows would produce

    F(x)=sum_(lambda=1,3,6) b_lambda*(1-x^lambda)

with double zeros at 1 and r. A nonzero polynomial with at most four nonzero monomials has at most three positive roots counting multiplicity, by Descartes' rule; these four zeros are impossible. Identical zero forces all three b_lambda zero. This is the inherited sparse-root argument, not a new root theorem.

Fix c in W_int with node r. Let p_n tend to zero through strict values and hold q_n=r. The row spaces

    span{Lambda,H_p(p_n,r),H_q(p_n,r)/p_n}

converge, with rank three, to span{Lambda,D(r),D'(r)}. Project c orthogonally onto their annihilators and normalize. The resulting c_n tend to c and satisfy the exact critical equations. Their cells have loss p_n(1-r) tending to zero.

For c in W_0 take any strict p_n,q_n tending to zero. The corresponding rescaled row spaces converge with rank three to span{Lambda,1,e_1}; these three vectors are independent. The same projection/normalization supplies the required critical sequence.

For c in W_1 hold p=1/2 and let q tend to one through strict values. For small s>0, span{Lambda,H_p,H_s} equals span{Lambda,V,Z}: the changes of rows used above are invertible at every strict p,s. By (J), this space tends to span{Lambda,Lambda^2,Lambda^3}, whose rank is three by the ordinary Vandermonde argument. Project and normalize again.

There is no failure when a limit normal is already on several listed strata. Projection converges to the unit c, so its norm is nonzero for all sufficiently late terms. The projection is a proof construction, not a source inverse or an added biological control. When the fixed data in one construction are algebraic and p_n,q_n are algebraic, projection and normalization give algebraic normals as well.

These constructions concern one physical COMMON cell with a free ordinary scale; the accepted eligible-bridge realization supplies strict arm survivals and connectors. Nothing sets an actual arm duration to zero. The q=0 or q=1 values are LIMITS only.

## 6. Compactness, thinness and a purely algebraic rate certificate

Let C be the strict critical incidence defined by (C), ordinary neutrality, unit norm and 0<p,q<1. Clear the positive f_lambda denominators. C is semialgebraic over Q and lies in the compact product of the unit sphere with [0,1]^2. Its closure E is compact semialgebraic and can be defined effectively in RCF. The preceding necessary and sufficient limits identify

    W = projection_c { (c,p,q) in E : p(1-q)=0 }.

This proves compactness of the explicit union (W), including its r endpoints, without assuming that projection of an open-r stratum is closed.

For each interior r, its three independent linear constraints leave a three-dimensional normal subspace, hence a two-dimensional unit sphere. Allowing r adds at most one dimension. The endpoint strata are two-dimensional unit spheres as well. Thus dim W is at most three, whereas the full unit ordinary-neutral normal sphere has dimension four. This codimension statement is NOT a finite input-normal acquisition theorem.

On E the continuous semialgebraic functions ell=p(1-q) and d=dist(c,W) satisfy {ell=0} subset {d=0}. The classical compact semialgebraic power inequality gives some positive constant a and positive integer k with ell>=a*d^k. Decrease a to a positive rational. Equivalently one can use one-variable semialgebraic Puiseux bounds for the minimum loss at normal distance at least delta. This is classical real algebraic geometry, not new transcendence theory.

It is important that this existence statement is EFFECTIVE here without an analytic feasibility oracle. Enumerate positive integers k and dyadic rationals a>0. For each pair use RCF to check the finite sentence

    for all strict critical c,p,q and 0<=delta<=2:
       [for all w in W, ||c-w||_2^2 >= delta^2]
          implies p(1-q) >= a*delta^k.          (R)

Every unit c and every w in W have distance at most two; W is nonempty. By compactness its distance is attained. Thus (R) is exactly the desired power bound on the strict incidence. All functions in (R) are polynomial after the recorded denominator clearing and the explicit existential definition of W_int. The semialgebraic power inequality proves that this RCF search eventually finds a pair. No (a,k), QE run or numerical bound is claimed to have been computed in this note.

This rate proof does NOT require the accepted fixed-normal Puiseux theorem as a premise. That older theorem additionally bounds critical loss for a fixed normal IN W. There is no contradiction: membership in W describes what can happen when the normal MOVES, not a zero loss floor for the same fixed c.

## 7. Conditional retained-count consequence

Supply a compact effectively semialgebraic family K of unit ordinary-neutral normals with K intersect W empty. Emptiness and compactness are actual hypotheses, not an inference from normalized coefficients. RCF first checks the separation and finds rational delta>0 below dist(K,W), or directly searches a positive uniform floor on the incidence over K. The theorem proves termination of that search. Let 0<epsilon<1 be a returned rational floor.

Suppose a coherent word or closure presentation has n actual retained critical factors, each assigned a normal in K, and its pair coordinate obeys m_1>=rho>0. Other ordinary/head/residue factors must have pair survival at most one, as in the original normalized source. Then

    rho <= m_1 <= product_i(1-ell_i) <= (1-epsilon)^n.

Choose an integer N with (1-epsilon)^(N+1)<rho. Exact algebraic arithmetic finds one by enumeration, and n<=N. No fractional occurrences or separately fitted rows appear.

For a single common normal, the power law also gives a quantitative NECESSARY escape condition. If m_1>=rho and n>0, then

    n*a*dist(c,W)^k <= -log rho.

One can replace -log rho by any computably chosen rational upper bound; no logarithmic equality test is needed. Consequently unbounded retained counts at a fixed positive pair floor require normals to approach W at the stated power rate. An arbitrary actual source need not have such a critical presentation, so this is not a lower/upper complexity bound on every G3 witness.

## 8. Exact consequence for the full termination attempt

The proposed globally uniform normal floor is still FALSE. What is now supplied is its exact weak-normal failure set and an effective transverse rate. The older rare-admissible rational weak family converges to a paired normal with double roots r and r^2; its limiting normal lies in W_int, exactly as this theorem requires. Pointwise positive floors cannot be compactified across W by continuity.

The attempted complete algorithm would need to extract, from the original finite algebraic JOINT input, a coherent all-rival cover whose relevant normals are bounded away from W, or separately decide every contact/near-contact branch. This derivation does not establish that premise. The locus W itself has lower dimension, but a normal can lie outside W arbitrarily close to it; a dimension count does not bound that distance. No algebraic degree/height bound for an unknown normal was inferred from the input.

Even a retained-count bound for one supplied normal-form family is not yet a bound on one actual realizing source. Finite residue/exponential equations, other presentation flags, alternative cores, hidden shared parameter fibres, and INDEPENDENT prefix/suffix chronology retain their exact earlier obligations. A surviving critical presentation is not a NO certificate, and its absence is not by itself a YES or NO decision. This note therefore proves neither termination nor undecidability and supplies no new negative original input.

The next precise proof gate is now quantitative: can the original input impose an effective positive distance from W on every surviving critical branch, or can its W-contact branches be covered by a complete sound exact exclusion/attainment procedure? Any claimed answer must preserve the same original source and shared bank across ALL supplied rows. Effective closure approximation and a positive margin on a different family cannot discharge this gate.

## 9. Prior reuse, exact files and verification stage

The following local bodies were read/authenticated; the listed SHA256 values select the source bodies, not a new acceptance of every historical statement.

| Provider | SHA256 |
| --- | --- |
| Original EXACT-CRITERION.md, 2026-09-30-g3-exact-source | 3528692b34948807ad942be5ceaf02cea40a78dcdc7e5c7a963557cf224f4330 |
| MASTER-STATEMENTS.md, 2026-10-05-dot-original-g-master-priority-1913z | e3b949a1bbb86aeff07de0f127243da560d3a0844247d3b8ce92110827473432 |
| ACTUAL-WEAK-CRITICAL-CELLS.md, Oct8 full-shot/attempt-5 | 8f66d5f81a00c58cb1c6352fd84857015bf949cc4cb0f98b8a65a4bb20b2feb9 |
| UNIT-CRITICAL-PUISEUX.md, Oct10 1029z | c94a4d25f50b49c071cbd92a675dfe1b22edb5e8a13ccc28b5409bd3f9ed0332 |
| Its INDEPENDENT-OBSTRUCTION-REVIEW.md | 70c792cc6876f41cfc92b5ebe998d949190208ea9825d63d2013342a8eb10d53 |
| LOCAL-NORMAL-BANK-OBSTRUCTION.md, Oct10 1043z | bbae35d72811ab0b925ff8b3244cf532fcd07ee22eccf4dd7c97067b9990bff6 |
| NO-FIXED-SEMIALGEBRAIC-RATIONAL-CLASSIFIER.md, Oct6 1422z | 3c89bb2d02f7166c8b9c8dc85c872ed348c95900ba8dc11404c7286f5879a0a6 |
| Its INDEPENDENT-RATIONAL-CLASSIFIER-REVIEW.md | 85d7fbb2bd01211c599da559f087b00c21a616492d25b492c7282233042d23ab |

The old fixed-normal floor, varying rational weak controls, all-core calibrated count obstruction and fixed-RCF-classifier impossibility retain their attribution. An initially attempted nonsemialgebraicity argument in this turn was retired after finding the stronger accepted rational-input prior; it is not presented as new work. The proposed delta is the COMPLETE moving weak-normal incidence including the uniform q=1 three-jet endpoint, its converse constructions, and the effective transverse power/count estimate.

Descartes' rule, projection onto a varying full-rank subspace, Taylor expansion, compact semialgebraic power bounds and RCF decision are classical. No broad novelty or general decision theorem is claimed. Independent hand/source review is requested before treating this candidate as an accepted provider. There is no Lean, runtime, source-model simulation or empirical evidence associated with this note.
