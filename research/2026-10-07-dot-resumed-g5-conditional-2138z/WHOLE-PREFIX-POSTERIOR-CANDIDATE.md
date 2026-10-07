# Actual selected-triple whole-prefix conditioning and feasible occupancy support

Contributor: dot, resumed G5 source-bridge lane, 7 October 2026.
Status: NEW HAND SOURCE-ASSEMBLY CANDIDATE, independent review pending. No Lean source, compiler, scientific execution, sampling or shared-provider edit.

## 1. Exact scope and inherited work

This is a concrete original-source consumer for G5-B/C1. The original M3/HG hand theorem already uses finite survival-conditioned mixtures and feasible-route positivity; those ideas and the full identification theorem are inherited, not claimed as newly discovered here. The finite Bayes calculation, exponential survival and pushforward/restriction identity are standard. This packet supplies an explicit connection to the inspected current source compiler, current-owner routing and timed readout.

Fix one admitted finite binary rooted temporal source N with original arc occurrences, strictly positive constant original edge rates and separate ancestral rate, strict original hybrid probabilities 0<gamma_h<1, a COMMON/INDEPENDENT flag at each original hybrid, and three distinct original tip labels I={0,1,2}. The G5 original theorem has contemporaneous tips at age a0; retain that hypothesis. Let t>a0 be finite and not an original vertex age. Choose epsilon>0 so (t,t+epsilon) contains no original demographic/routing boundary. Above the original root any finite positive epsilon is permitted. No new demographic source is installed outside this interval.

The entire carrier for the source construction below is the genuine ordinary selected three-copy source on the SAME N, original parameters and once-drawn register law. For a larger original copy carrier, Section 2 first proves the exact observed conditional-law transfer; it does not replace full-source no-selected-merger conditioning with full-source no-ANY-merger conditioning. Unselected old trees and original labels remain in the full source until the inherited literal observation pruning is applied.

Read sources at immutable Commons commit fb62f2e28b463235290db88c1a082a9744b001bb:

- SourceNaturalInitialization.lean: originalRegisterMeasure, originalRegisterPMF, naturalCalendarLaw.
- SourceCalendarCompiler.lean: sortedOriginalDates, boundaryOperations, compiledCalendarProgram; original edge exits precede node operations at each date.
- SourceBoundaryKernels.lean: boundaryKernel, currentCoinPMF, independentPulseKernel and pulseCode. INDEPENDENT coins belong to ACTUAL CURRENT AtNode owners. COMMON is the deterministic current pulse using the original register.
- SourceCalendarCompatibility.lean and SourceInitializedCalendar.lean: actual physical epoch/agenda support. Calendar has strict edge_older; original edge IDs are retained.
- G2LiteralCutResidual.lean: actual_no_event_joint_residual; G2SameClockPastFutureLaw.lean: actual_same_clock_past_future_source_law.
- G2SourcePairMatrixReadout.lean and G2FaithfulTimedOutput.lean: actual selected pair-age and faithful same-record timed readout.
- G5HiddenRegisterTimedProjectivity.lean: actual_natural_hidden_timed_all_panel_projectivity.
- Cloud ACTUAL-FROZEN-TRIPLE-HAND-PROOF.md: exact original three-copy first-jump row. This remains a separately reviewed dependency; this packet does not claim its pending review was completed.
- G5FrozenTripleAnalyticSupport.lean: occupancy_support_eq_of_right_germ, allowing repeated rates, different finite seed carriers and dependent weights.

Exact source paths/blob identities and review-stage distinctions are recorded separately. Earlier source headers saying unchecked do not supersede the later selected compiler receipts, but no receipt compiles the new bridge below.

## 2. The observable event and legitimate ordinary projection

In a complete three-tip timed observation let T_ij be the actual off-diagonal coalescence age of original labels i,j. Define the measurable event

    E_t = {T_01>t, T_02>t, T_12>t}.

Let G_v be the five-valued partition whose blocks are ancestor equivalence at calendar age v, recovered from the same three pair ages using T_ij<=v. This is a Borel function of the original timed genealogy. G2's actual pair-age/faithful-output results identify it almost surely with the original path's selected ancestor partition. All readouts retain the same original labels; no population or register is made observable.

Ancestor equality never splits, and demographic boundary operations do not merge genealogies. Therefore E_t is precisely no merger among the three selected ancestral blocks during the ENTIRE prefix from their original tips to t. On the genuine three-copy source this is no genuine merger anywhere in that prefix. On a larger carrier it does NOT exclude mergers of unselected blocks or mergers attaching only unselected labels to a selected ancestor.

Here is the missing conditioning justification beyond ordinary projectivity. If f is the inherited literal timed-pruning map and f_*mu=nu, then for every measurable B and E,

    f_*(mu restricted to f^{-1}(E))(B)
      = mu(f^{-1}(B) intersect f^{-1}(E))
      = nu(B intersect E).

Consequently the measured denominators agree, and whenever nu(E)>0 the normalized conditional observed laws agree. Apply this with E=E_t and B={G_(t+u)=j}; positivity is derived in Section 4. The checked ordinary timed projectivity thus transfers EXACTLY these observed conditional probabilities from the full original source to its genuine selected three-copy source. It does not assert equality of arbitrary hidden full-source posteriors, nor commute unrelated conditioning with pruning. The full source retains its old subtrees throughout; only the already-authorized selected observation discards unselected leaves.

## 3. A finite seed expansion derived from actual prefix routing

Draw the original register R once, exactly as originalRegisterMeasure: one strict Bernoulli bit per ORIGINAL hybrid, with nonhybrid slots inert. This includes the unused register coordinates at INDEPENDENT sites; marginalizing unused coordinates gives one. Do not redraw a COMMON bit on revisiting or on conditioning.

For the stopped no-merger prefix only, introduce potential bits A_(i,h), i in I, for INDEPENDENT original sites h, each with its original gamma_h. They are independent of R and of the physical clocks. Their simultaneous drawing is a finite expansion of the sequential currentCoinPMF kernels, not a change to the dynamics. Until a selected merger, the actual three live owners remain the original singleton copy IDs i. Strict ages imply a rootward route visits an original site at most once. Hence every used bit (i,h) is consumed at most once and has exactly the current-owner law defined by independentPulseKernel; unused bits sum to one. This representation is NOT extended beyond a first merger through later hybrid pulses, where current owners would have changed.

Let A be the finite full seed carrier (R, all these potential independent bits). Its exact prior mass is

    pi(a) = product_h gamma_h^{R_h}(1-gamma_h)^{1-R_h}
            * product_(i,h INDEPENDENT) gamma_h^{A_ih}(1-gamma_h)^{1-A_ih}.

Every pi(a)>0 and sum_a pi(a)=1 by finite Bernoulli product expansion. No observed-route label, fitted posterior or uniform positive lower bound is assumed.

Each seed deterministically specifies the three rootward ORIGINAL routes: at a COMMON site all current owners use the same R_h; at an INDEPENDENT site owner i uses A_ih; ordinary entries and root entry are exactly boundaryKernel. The strict original parent maps, rooted acyclic graph and sorted original agenda give a well-defined original route to the actual root. Parallel original arc occurrences remain different locations.

Define feasible route prefixes combinatorially: paths through these actual compiled boundary operations with globally consistent COMMON choices and independently assignable CURRENT-owner choices. Then they are exactly the images of seeds a in A. In one direction read the choices from a; in the other extend the finitely specified consistent used bits arbitrarily to all unused seed slots. This is not a support oracle. It proves finite structural feasibility before attaching probabilities. In particular arbitrary combinations of individually feasible routes need not be jointly feasible in COMMON mode. No Cartesian-support claim is made.

For each seed, form the finite sequence of no-merger codes s_k(a) obtained by performing only the actual deterministic/pulse boundary operations. Registers and singleton genealogies stay unchanged. Between boundaries all current locations are genuine active original edges or the original ancestral population. Indeed all contemporaneous tips activate at a0; an edge exits exactly at its original source date, then that same date's node batch enters a genuine parent edge or the root; strict edge ages forbid an equal-date edge chain leaving a node unprocessed. Equivalently this is the no-merger specialization of the inspected physical agenda-support induction. No inactive node location is counted as a coalescing population.

Let ell_k(t)>=0 be the actual durations of those prefix pieces, including the final partial epoch. In code s define

    lambda(s) = sum_original_populations P binom(n_P(s),2)*rho_P,

where rho_P is r.edge(e) for an original edge and r.ancestral for the original root. This is the genuine merger rate, not the uniformization rate. The source catalogue has rho_P/2 for each ordered orientation, so its two orientations give rho_P per unordered pair. With three roots the possibilities at any time are 0, one pair rate, or three times one population rate.

## 4. Whole-prefix mass, strict positivity and posterior support

The actual no-event residual theorem gives, for a fixed entering code and interval ell,

    mass(no genuine merger during ell) = exp(-lambda(s)*ell),

and the SAME residual clock catalogue has its original product law after multiplying by that mass. This is an unnormalized original-clock identity, not an independence assumption inserted after survival. Iterate that identity with the actual finite boundary kernels along the prefix. The actual calendar construction composes these same kernels; the product expansion of Section 3 accounts for every boundary coin. It follows that the joint seed-and-survival mass is exactly

    m_t(a) = P(seed=a, E_t)
           = pi(a) * exp(-sum_k lambda(s_k(a))*ell_k(t)).          (1)

No full-source no-any-event theorem was used before the correct three-copy observation reduction in Section 2. The full chronological prefix is covered, not merely the final residual interval.

All rates are finite, the agenda is finite, t is finite and pi(a)>0. Thus m_t(a)>0 for EVERY seed. Therefore

    Z_t = P(E_t) = sum_a m_t(a) > 0,
    w_t(a) = m_t(a)/Z_t > 0,      sum_a w_t(a)=1.                  (2)

This is the measured event's denominator and its source-derived posterior. Survival can correlate the seed coordinates; no product factorization of w_t is asserted. For a finite current-code fibre s, its posterior weight is

    W_t(s)=sum_{a:s_t(a)=s} m_t(a)/Z_t.

It is positive iff the fibre contains a feasible seed. Likewise every occupancy partition has positive posterior mass iff it is realized by at least one feasible original route prefix. Equal codes or unused bits are summed, never miscounted as distinguishable observations. If one instead uses all syntactically possible code values, unsupported values receive zero mass; the positive-weight analytic theorem then uses only the supported subtype or the all-positive seed carrier A.

## 5. Future row with fixed prefix posterior

Write p_t(a) for equality of the three active ORIGINAL population locations in s_t(a), encoded by 0=0|1|2, 1=01|2, 2=02|1, 3=12|0, 4=012. For p_t(a) non-discrete there is one nonsingleton population block; let rho_t(a) be that population's original positive rate. For p_t(a)=0 choose r.ancestral>0 as an unused positive convention. Neither occupancy nor rho is observed or supplied by an inverse procedure.

On E_t all three selected genealogies in the genuine selected source are still the original singleton leaves. The preceding residual identity, or the actual same-clock past/future finite-fibre factorization, gives the actual future sourceTimeKernel from s_t(a). There is no boundary for 0<=u<epsilon. The Cloud local-row source proof derives its partition pushforward from the actual first-jump renewal, including both ordered orientations and both possible mergers. Applying that source row and summing the derived masses gives

    P(G_(t+u)=j, E_t)
      = sum_a m_t(a)*row(exp(-rho_t(a)*u),p_t(a),j),

    P(G_(t+u)=j | E_t)
      = sum_a w_t(a)*row(exp(-rho_t(a)*u),p_t(a),j).              (3)

This is exactly frozenMixture on the source-derived finite seed carrier. It is a consequence of (1), residual continuation and the proved local row, not a premise of a source contract. The posterior w_t is FIXED as u varies. Conditioning again on E_(t+u) would change the weights and would not yield (3).

The actual old forest is not silently replaced: for the ordinary selected three-tip source, no-merger forces its existing leaves to remain singleton; for the larger original source, conditional observed equality came from exact literal pruning in Section 2 while allowing its full older subtrees and unselected events. This proof does not identify full hidden-state/old-tree posterior measures with W_t. A contextual source with exactly three pre-existing live blocks can use the Cloud old-block row and its actual cut-fibre measure, but its support may be restricted by that past; the unrestricted original-tip feasible-route statement here is not automatically transferred to arbitrary extra history conditioning.

## 6. Observable germ to actual feasible support

Suppose two admitted original sources have the same ordinary selected-triple timed law. Choose t strictly above the contemporaneous tip date, outside the UNION of their finite original boundary sets, and choose epsilon>0 before the next boundary of either source. Sections 2 and 4 show their measured E_t probabilities agree and are positive. Equality of the same observed laws therefore gives equality of the conditional probabilities on the left of (3) for every j and 0<=u<epsilon.

Section 5 identifies both sides with their respective source-derived frozen mixtures; seed carriers, weights and positive rates may differ. The checked occupancy_support_eq_of_right_germ therefore yields

    (exists feasible original route prefix in source 1 with occupancy j)
      iff
    (exists feasible original route prefix in source 2 with occupancy j). (4)

Repeated rates and survival-induced dependence are permitted. The analytic continuation used by that theorem freezes these finite mixtures mathematically; it does not extend the physical boundary-free epoch beyond its next original boundary. No latent population names or register labels are learned, only the five abstract occupancy-partition support values.

This supplies a candidate original-source bridge for G5-B/C1 at genuine interior epochs. It does not establish the chronology/deletion/attained-boundary/full-X decoder/HG compiler, a supplied-calendar algorithm, whole G5 Lean completion, or new statistical/DNA inference. The original M3 hand theorem and its prior attribution remain unchanged. Endpoint/older-side extension requires its own chronology argument and is not inferred by silently applying an interior theorem at a demographic boundary.

## 7. Review questions and exact stage

Independent review should challenge: (i) whether the stopped finite seed expansion exactly matches current-owner kernels; (ii) original-state/routing induction through all equal-date boundary batches; (iii) the observable event and restriction/pruning equality; (iv) prefix survival/actual residual factorization, including ancestral tail; (v) old-tree/full-carrier scope; and (vi) the dependent local-row review status. No code execution or formal acceptance follows from this hand derivation. The candidate is saved early so objections and later revisions can be preserved append-only.
