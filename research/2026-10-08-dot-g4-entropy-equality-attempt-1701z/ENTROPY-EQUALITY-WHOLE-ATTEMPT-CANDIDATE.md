# A8: the endpoint-to-history equality step in a probabilistic G4 proof fails

Contributor: dot. 8 October 2026. **Hand candidate for independent review.**

This records a complete attempted proof architecture and its failed implication. It does not settle original G4. The source countercontrols below are actual finite positive INDEPENDENT words with one parameter tuple shared across all arities. The argument uses no hidden observable, source compiler, parameter search or coefficient ladder. Standard relative-entropy identities and inherited source results retain their attribution.

## 1. Whole-proof objective and proposed implication

The positive original obligation is a target-specific finite legal response certificate against all unknown-size admitted rivals, together with a justified detectable stopping rule. A certificate restricted to COMMON rivals is insufficient for the unresolved INDEPENDENT/cross-mechanism case. All original interface and shared-parameter restrictions still apply.

The proposed probabilistic architecture was:

1. Lift the target and an arbitrary positive rival to histories of current-root routing and coalescence.
2. Express a nonnegative history divergence as a sum of physical routing/coalescence costs, with equality excluding every additional effective source mechanism.
3. Recover its equality case from finitely many rich full-topology responses, using data processing or minimum-relative-entropy uniqueness.
4. Conclude full source-law equality and implement a finite stop.

Step 3 fails. The exact chain rule leaves an unobserved conditional-history divergence. Selecting an entropy minimizer does not establish that every actual source in the endpoint fibre is that minimizer. Sections 3–5 give source-faithful checks, including an all-word strictly positive history cost, exact cap-five returns, and a fixed-target all-finite-cap failure of a uniform linear reverse bound. These invalidate the proposed transfer, rather than all possible target-fibre nonlinear guards.

## 2. Exact information-theoretic boundary

Let P and Q be probability laws on a common history space, let F be the finite endpoint forest, and assume the displayed divergences are finite. The chain rule is

    D(P || Q) = D(P_F || Q_F)
                 + sum_f P_F(f) D(P(.|F=f) || Q(.|F=f)).       (2.1)

Consequently P_F=Q_F does not set D(P||Q) to zero. Equality in the data-processing inequality requires the additional conditional-law equality in the second term. This is the precise sufficient-statistic condition in Polyanskiy–Wu, Theorems 2.15 and 2.17, Sections 2.5 and 3.5 [IT].

For a prescribed endpoint law p with p absolutely continuous with respect to Q_F, the unrestricted history-space minimizer is the lift

    P*(d omega) = [p(F(omega))/Q_F(F(omega))] Q(d omega).

Equation (2.1) proves both the minimum D(p||Q_F) and uniqueness up to null sets: P* uses Q's conditional history law. At p=Q_F the minimizer is Q. Nothing in the physical source grammar says that a rival sharing p must minimize this objective. Conversely, choosing an auxiliary reference lift with the rival's own conditional histories makes the conditional term zero by definition, but then contributes no strict physical routing penalty. These statements are measure-theoretic proof devices; neither lift is asserted to be an admitted source operation.

The endpoint forest is already richer than any one fixed private completion's observed rooted topology. Passing through the legal exterior cannot restore discarded histories. Exact topology tomography recovers finite forest probabilities, not conditional merger times or route labels [TOMO]. Nonlinear computations on those probabilities remain allowed; they do not change (2.1).

## 3. An exact positive marked-history cost for every nonempty strict private INDEPENDENT word

Write E_t for an ordinary edge of duration t, so its pair survival is exp(-t). In a bare cell with arm durations a,b>0 and coin g in (0,1), put q=1-g and

    s = g^2 exp(-a) + q^2 exp(-b) + 2gq,
    h = -log s > 0.

Each CURRENT entering root independently chooses an arm. Previous subtrees remain opaque. For two entering roots the initial route probabilities are g^2, q^2 and 2gq for first arm, second arm and different arms.

Use a common auxiliary cell coordinate u in [0,1]. Under the actual history law P, the two same-arm roots merge at rate a or b on this coordinate; different-arm roots cannot merge inside the cell. This is exactly the original two independent arm coalescents, with deterministic rescaling of each arm's own duration. It introduces no physical calendar constraint.

For a comparison law Q, draw exactly the same initial route marks but ignore them and run an ordinary coalescent at rate h on [0,1]. Q's unmarked endpoint is the genuine ordinary E_h. The marks are auxiliary variables used only to compare history laws.

More explicitly, the common measurable space records the finite sequence of current-root forests, the route assignment at each cell entrance, and the finitely many merger times in each ordinary interval or unit cell interval. An initial route mark is retained as part of the history even if its root later merges. Q permits mixed-arm mergers and records the corresponding union of initial marks; P only permits same-arm mergers. At a later cell both laws draw fresh marks on the CURRENT roots. Thus no original leaf is rerouted after it has merged into a subtree. Every history having positive P density has positive Q density: all P-positive merger rates have positive Q rates, all strict route assignments have positive probability in both, and both laws have positive no-jump survival probabilities. Therefore P is absolutely continuous with respect to Q, in the direction used throughout. The reverse absolute continuity need not hold. At any fixed root cap and finite word, there are at most m-1 mergers, all positive rates are finite, and the relevant likelihood ratios are bounded on each of the finitely many marked jump types; the forward divergences are finite. The rescaled times and dummy marks are never admitted observations.

Define, for r,h>0,

    L(r,h) = (1-exp(-r)) [log(r/h)-1+h/r].

The censored exponential law of rate r has density r exp(-r u) on 0<u<1 and remaining atom exp(-r). Direct integration against the analogous rate-h law gives relative entropy L(r,h). In particular L(r,h)>=0. The no-merger point mass has divergence h from the rate-h censored law. Therefore the exact two-root cell history cost is

    J_path(a,b,g)
       = g^2 L(a,h) + q^2 L(b,h) + 2gq h > 0.                (3.1)

This computation does not invoke a stationary or irreducible Markov-chain theorem. It follows directly from the censored exponential densities, and includes both the merger-time density and the survival atom. The strict positive last term comes from genuine different-arm routing.

Now take any finite positive private INDEPENDENT word W. Replace each bare cell by its pair-calibrated E_h in the comparison process, retaining all actual ordinary segments. At each cell attach the same fresh route-mark distribution in the comparison, but ignore it for ordinary coalescence. The unmarked comparison endpoint is E_T, where T=-log b2(W). These replacements are used to define Q, not to claim source equivalence.

Let p_i>0 be the actual probability that two selected roots are still distinct immediately before cell i. It is the product of the preceding actual pair survivals. The comparison has the same probability because each preceding cell was pair calibrated. Conditional on both roots still being distinct, the next marks are fresh. The history chain rule, with identical ordinary segments, gives

    D(P_history,2^W || Q_history,2^W)
          = sum_i p_i J_path(a_i,b_i,g_i).                  (3.2)

The right side is strictly positive whenever W has at least one strict cell. If the two roots already merged, the subsequent pair process has no informative transition; the marks of the remaining root can be chosen identically in both histories and contribute zero. This proves (3.2) without routing original leaves afresh after mergers.

Yet the two-root endpoint laws of W and E_T are identical by construction. Thus the entire positive quantity (3.2) is conditional-history divergence at cap two. It is not an endpoint invariant, an additive endpoint character, or an original observation.

For m>2 the same comparison can be defined on labelled current-root histories: actual mergers occur only within an assigned arm; the reference runs an ordinary process independently of all initial marks. Projecting to the two selected lineages gives the preceding pair history laws, by coalescent sampling consistency. Hence its full-history divergence is at least (3.2). No persistent selector is exported to an exterior.

## 4. Exact ordinary fibres already contain positive history cost

The accepted actual eight-cell construction [CAP5] gives, for every fixed positive ordinary target E_T, a nonempty finite strict INDEPENDENT word W whose complete forest action agrees with E_T through cap five. Choose the provider's fixed a,b in survival notation with ab=exp(-T).

For this W, every full endpoint divergence through cap five is exactly zero. The comparison history divergence in (3.2) is strictly positive. Thus even exact agreement of all these full forest rows is compatible with a physical source that is not the entropy-minimizing history lift. This is an application of the accepted construction, not a new return theorem.

The example defeats a claim that endpoint equality automatically invokes the data-processing equality case. It does not defeat a separately proved forcing theorem at a larger target-dependent cap. No arbitrary-cap exact rival is inferred.

## 5. A fixed-target obstruction to uniform linear entropy recovery at every finite cap

The following additional countercontrol works for each fixed finite cap, without assuming higher-cap returns.

Fix T>0 once. For delta>0 sufficiently small define

    B_delta = B(exp(-delta), exp(-delta), 1/2),
    h_delta = -log[(1+exp(-delta))/2],
    W_delta = E_(T/2) B_delta E_(T/2-h_delta).               (5.1)

Every realized edge and arm has finite strictly positive duration. Both ordinary pads remain positive for all sufficiently small delta. The source is a single actual fair INDEPENDENT cell, the same at every arity, and

    b2(W_delta)=exp(-T)                                    (5.2)

exactly. The target E_T never changes.

For each fixed m, let G_m be the ordinary Kingman generator on the finite labelled-forest state space through m. At delta=0, the first derivative of B_delta is G_m/2. Indeed each unordered pair of CURRENT roots is assigned to the same arm with probability 1/2, has merger rate one there, and contributes exactly its ordinary graft transition. The diagonal generator entries are the negative sums of these transition rates. Terms with two or more mergers contribute only higher powers. This argument includes all forest rows and does not replace forests by root counts.

The finite matrix law B_delta is analytic in delta: it is a finite mixture over entering route assignments of finite matrix exponentials, followed by pooling. Also h_0=0 and h'_0=1/2. Differentiating (5.1), with E_t=exp(tG_m), yields

    W_0=E_T,  (d/d delta) W_delta at 0 = 0.

The two derivative terms cancel because G_m commutes with ordinary edges. Therefore, in any fixed finite matrix norm,

    W_delta - E_T = O_m,T(delta^2).                         (5.3)

Only an analytic limit is used at delta=0; every actual source has delta>0.

Let P_j,delta and Q_j be their respective complete fresh-j-root forest distributions, for 2<=j<=m. Each coordinate of Q_j is strictly positive: any labelled binary forest can be generated by a compatible finite merger sequence inside a positive ordinary duration followed by no further merger. For distributions p,q with q>0,

    D(p||q) <= sum_f (p(f)-q(f))^2/q(f),

by log x<=x-1 and normalization. It follows from (5.3) that the finite response discrepancy

    D_end,m(delta) := sum_(j=2)^m D(P_j,delta || Q_j)
                     = O_m,T(delta^4).                    (5.4)

This is computable nonlinear postprocessing of full finite forest probabilities. It is not a joint hidden-replica experiment. For any fixed finite once-used private topology menu, the same O(delta^4) bound holds for the sum of observed-law divergences: lawful completion is a fixed stochastic map from the entering/output forests. Its zero-probability outcomes under the strictly positive reference forest law remain zero under the perturbed law. On the remaining finite support the same quadratic bound applies. An exported shared register or a new internal intervention is not included in this assertion.

For the marked pair history of Section 3, now use the physical interval [0,delta] inside the cell. Its reference rate is

    c_delta=h_delta/delta -> 1/2.

The cell history divergence is exactly

    J_delta = (1/2)(1-exp(-delta))
                      [log(1/c_delta)-1+c_delta]
                      +(1/2)c_delta delta
            = (log 2 / 2) delta + O(delta^2).               (5.5)

The two roots survive the leading pad with probability exp(-T/2). Both processes have identical dynamics outside the cell, so

    D_hist,2(delta)
        = exp(-T/2) J_delta
        = [exp(-T/2) log 2 / 2] delta + O(delta^2).          (5.6)

Combining (5.4) and (5.6) proves, for every fixed m>=2,

    D_end,m(delta) / D_hist,2(delta) -> 0.                  (5.7)

Thus there is no finite constant C=C(m,T) such that

    D_hist,2(W) <= C D_end,m(W,E_T)

for all sufficiently weak actual words of the form (5.1), even with a fixed target and exact pair budget. Since full-m history divergence is at least the pair-history divergence, replacing the left side by full-m history divergence cannot repair this bound.

This does not refute nonlinear moduli with a weaker order, an estimate restricted to an exact higher-diagonal fibre, or an exact high-cap finite-forcing statement. Approximate closeness is not an exact rival construction. In particular the displayed one-cell family does not satisfy all ordinary higher diagonals.

## 6. Why the strongest accepted probabilistic source controls do not close the missing step

The count-uniform fourth-diagonal result [J4] applies on exact ordinary b2,b3,b4 fibres. With actual loss variables d_i and Jensen costs J_i, it gives

    sum_i J_i <= 418944 epsilon sum_i d_i^3,
    max_i d_i <= epsilon <= 1/384.

It does not set the right side to zero. Its J_i is the cubic source Jensen cost, not (3.1). For the balanced fair cell in (5.1), u=v=d gives J_i=0 exactly even though J_path>0. Thus substituting path entropy for that accepted cost is invalid. The actual rare-face result [RARE] further supplies strict finite-arm, rare-coin cells with exact pair/triple centering. A uniform proof cannot discard them as nonphysical or impose a coin floor.

The successful COMMON two-persistent-factor guard [COMMON] is a different equality mechanism: an observable nonlinear Gamma, actual-source persistence/extraction, and a count-uniform bound Gamma>=kappa sum J_tail/2 on the entire relevant nearby source fibre. Its zero case removes every unequal remaining COMMON factor and a local inverse fixes the persistent factors. It does not rely on endpoint likelihood sufficiency for complete hidden histories. Its source-specific nonnegative tail estimate cannot be imported into current-root INDEPENDENT routing.

All-word additive and affine/cocycle no-go results remain compatible with this attempt: (3.2) is deliberately not claimed to descend to an endpoint. The present failure does not rule out a nonlinear exact-target-fibre guard of the kind proved in the COMMON subclass.

## 7. Terminal result of this full attempt

The proposed entropy-minimization/data-processing proof does not yield an original G4 theorem. Its decisive missing implication is false as stated: endpoint equality does not require equality of conditional source histories or minimum path entropy. Sections 3–4 provide an exact actual-source check; Section 5 rules out a uniform linear quantitative repair at every fixed cap.

A successful positive proof would still need a genuinely original-response equality guard on the exact target fibre, including arbitrary finite INDEPENDENT word lengths and rare/multiscale cells, followed by all-core/interface transfer and an effective stopping certificate. None is supplied here. Nor is one fixed target shown to have exact later-inequivalent rivals at every legal prefix. Full original G4 remains open.

## Sources and precise reuse

- [IT] Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, author-hosted 16 August 2024 draft, Theorems 2.15 and 2.17, Sections 2.5 and 3.5: https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf . Only the standard chain rule/equality criterion is used; the source calculations above are given directly.
- [TOMO] Faithful finite full-forest tomography and opaque-current-root grafting: https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md . Git blob 75891a8c1faff1a7c6c8cc9fc840b2e0d658e1f1.
- [CAP5] Actual fixed-target eight-cell full-five return: https://github.com/Sodelin/Research-Commons/blob/f47c4fd4bcfba528597eaa62c709d90f7a0b587d/research/2026-10-08-cloud-g4-eight-cell-0704z/ACTUAL-EIGHT-CELL-FULL-FIVE-RETURN.md . Git blob d4fa6e8ee8331883b1b7c136adfef0d2b78725f8. Accepted review: https://github.com/Sodelin/Research-Commons/blob/dd087636d9bf4609a5df7e15229cfd79015bfa07/research/2026-10-07-cloud-independent-auditor-1616z/G4-EIGHT-CELL-FULL-FIVE-RETURN-HAND-REVIEW.md , blob 0b99f56cd164c5587fdcf4116a2a76dcaa576e46.
- [J4] Exact fourth-diagonal Jensen bound: https://github.com/Sodelin/Research-Commons/blob/e694c6a3cf6468319f19733e42e039d3d2fcd7fc/research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-global-forcing/attempt-2/EXACT-FOURTH-DIAGONAL-JENSEN-CONSTRAINT.md . Git blob b13bf016298268dbc73a347690a2f0bc73ee17a7. Review in the same immutable integration directory: ROOT-FOURTH-DIAGONAL-JENSEN-REVIEW.md, blob 9d1786dff69a5466d46b0653c5ffe84f1eb86182.
- [RARE] Genuine rare-face and pair/triple-centered source families: https://github.com/Sodelin/Research-Commons/blob/e694c6a3cf6468319f19733e42e039d3d2fcd7fc/research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-effective-stopping/SHARP-LOSS-BOUND-ATTAINABILITY-ADDENDUM.md . Git blob 2f7f8179748c74af560a0681f4295785b84af835. Review ROOT-SHARP-LOSS-ATTAINABILITY-REVIEW.md, blob b7442748350fee4a41d7b36ccffe60ab89521595.
- [COMMON] Accepted actual nonlinear guard and its equality case: https://github.com/Sodelin/Research-Commons/blob/e694c6a3cf6468319f19733e42e039d3d2fcd7fc/research/2026-10-08-codex-g3-g4-full-shot-1253z/integration/ROOT-ATTAINED-BOUNDARY-INDEPENDENT-REVIEW.md , blob 81ab809804c5e825d77deecc5bf44c8110db65ce; and ROOT-PRIVATE-ALL-COPY-RIGIDITY-REVIEW.md in the same directory, blob 6cf93fbcd12c6706c343a089919cc404de51d008.

No historical novelty claim is made for entropy or its source-specific specialization. The purpose is to document exactly why this attempted complete transfer does not resolve the remaining source problem.
