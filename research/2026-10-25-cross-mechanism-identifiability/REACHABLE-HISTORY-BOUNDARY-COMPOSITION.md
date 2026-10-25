# Candidate exact reachable-history classification with unknown boundary times

Author: dot (OpenAI), 25 October 2026. Written full composition candidate for scoped review. The reachable-epoch supplier is reviewed; this unknown-history composition is not yet accepted. It preserves the original ghost-permitting master and does not claim an effective arbitrary-input recognizer, sequence-data inversion, stability or historical novelty.

## 1. Exact class and observable

The source is a finite piecewise-constant structured-Kingman history with an unknown finite number of demes and positive-duration epochs. Coalescence rates are strictly positive and finite; migration generators are finite, with structural zero edges allowed. At each boundary, every currently surviving lineage routes independently by one row-stochastic matrix. There is no instantaneous lineage merger. Root absorption is required: every finite sampled genealogy reaches one ancestor almost surely. A final single positive-rate ancestral population is a sufficient special case, not asserted equivalent to all absorbing histories. These are the original baseline assumptions, not arbitrary continuous time variation or shared COMMON routing. Source check: MASTER-CONTRACT-AND-FIRST-ATTACK.md section 2 explicitly requires root absorption and gives final single-population closure as an example; its sampling paragraph allows hidden initial routing only when explicitly declared. The two initial-sampling scopes above preserve that distinction.

Sampling is contemporaneous at time zero from a fixed finite labelled taxon/population set X, with arbitrary finite labelled haploid copy panels. The baseline theorem uses the declared deterministic taxon-to-initial-deme sampling map P. A separately stated variant permits unknown row-stochastic P only when independent per-copy hidden initial routing has explicitly been admitted on both sides of the comparison; recovery of P in that variant is included below. This is not an automatic enlargement of the baseline. This does not silently admit common initial routing, serial samples, an unknown mutation clock or population labels not in X.

The observable is the complete family of labelled unmarked timed-genealogy laws: merger identities and times are visible; deme locations, migration marks and routing coins are not. All comparisons use the same X and time units.

## 2. The reachable reduction, not a replacement master

For the initial epoch, let S_0 be the migration-reachable closure of the union of supports of P's rows. At a later boundary, take the support of the boundary-routing rows indexed by the preceding reachable set, then close it under the new epoch's migration graph. Call this S_j.

Restrict each epoch generator/rate vector to S_j, and each routing matrix to the preceding reachable rows and the new reachable columns. The restricted generator has zero outward leakage by the definition of reachability; boundary rows remain stochastic. Columns can be zero at the boundary when they become reachable by migration immediately afterwards. Such states MUST be retained.

Remove a boundary only when its restricted routing is a bijective hidden-name permutation and the generator and rates agree across it under that same permutation. Adjacent matching epochs then concatenate, with future boundaries and their actual calendars retained. This produces a finite reduced history. States inaccessible in one epoch may enter a later S_j; their later activation is not deleted. What is lost is only their unobservable pre-activation description.

UNREACHABLE-GHOST-PULSE-COUNTEREXAMPLE.md gives a literal negative answer to the original pulse-anywhere predicate: adding a stochastic pulse solely among ghosts that remain unreachable for the entire sampled history changes that predicate but none of these laws. The proposed reduced-history object is the strongest candidate identifiable quotient at observation level G, not a redefinition that erases the negative answer.

## 3. Candidate theorem

Two promised finite histories in section 1 have equal all-panel unmarked timed-genealogy laws if and only if their reachable reduced histories are isomorphic by a coherent sequence of hidden-deme permutations preserving:

- the taxon-labelled initial map P;
- every observable boundary time;
- each restricted generator and coalescence-rate vector;
- every restricted independent routing matrix in its adjacent coordinate frames.

The theorem concerns the reduced demographic process, not reconstruction of dormant/unreachable state names, unused routing rows or the literal raw number of structural events. Its necessity proof below is a composition of the reviewed local acquisition and the explicitly stated boundary/coherence arguments; the latter composition remains to be reviewed.

## 4. Initial acquisition and taxon anchoring

Independently average each sampled lineage's taxon label over X, retaining its distinct copy ID. This is a finite linear combination of the available taxon-panel laws, not access to a new taxon. Conditional on the chosen labels, the declared independent entry law makes the resulting hidden locations independent with distribution p_bar=|X|^(-1) sum_x P_x.

Apply the reviewed reachable-epoch acquisition to this product-entry family. It supplies the full reachable initial generator/rates and coherent prepared tuples, retaining any original typed taxon reporters jointly. A reporter from taxon x paired at time zero with a prepared state i has merger-density limit P_xi lambda_i. Disjoint copies of these reporter/prepared pairs give products of entries of P under the SAME residual new-state alignment. Mixed products with future tests retain the joint source frame.

Finite positive orbit interpolation selects one P atom in the already acquired generator/rate frame. Since the taxon rows are labelled, no taxon permutation is allowed. The residual group H preserves the entire selected initial prefix, including P. The same conditional mixture is retained for every future tuple and test.

## 5. Unknown first observable boundary from acquired laws

Let (Q,lambda) be the selected current constant epoch at local time zero, with its coherent response laws L_(n,a) for every finite ordered reachable-state tuple a. Define

    T=sup {t>=0 : for every n,a, the restriction of L_(n,a) to (0,t)
                        equals continuation of (Q,lambda) from a }.

This is an exact observable-law functional. It is not a finite scan or a decision procedure for the universal equality predicate. In a finite promised source there is a first actual non-silent reduced boundary tau, unless none remains.

Before tau the laws agree with constant continuation. If they agreed through a horizon beyond tau, take a sufficiently short right interval before the next boundary. Choose epsilon > 0 with tau+epsilon < t and before the next actual boundary. For each n and cylinder F supported entirely inside (tau,tau+epsilon), the probabilities of no main merger before tau followed by F obey

    y_n(F)=exp(K_n tau) r_n(F),
    y_n^0(F)=exp(K_n tau) r_n^0(F),

where K_n is the known killed generator on the full reachable occupancy space. It is identical in every residual H frame. The y vectors are taken from the ALREADY acquired initial joint laws. The assumed finite-horizon equality and invertibility of exp(K_n tau) imply equality of these post-boundary response vectors r_n and constant-continuation vectors r_n^0 ONLY for F in this short right neighborhood. That local equality is sufficient for the invisibility argument, whose derivatives and prepared probes use an arbitrarily short positive constant epoch. Equality for unrestricted later F is not inferred here.

The zero-entry invisibility argument then applies: initial star coefficients count directly populated new states; zero cross-old-state pair hazards force disjoint routing supports; equality forces a bijection onto exactly the old count; pair-density exit derivatives minus within-active directed triads force all ghost leakage to vanish; first/second coherent moments fix the same rate/generator frame. Thus equality would make the boundary a removable permutation with unchanged dynamics, contradicting its non-silence.

Therefore T=tau. If no non-silent boundary remains, T=infinity. Conversely, a finite source with any remaining non-silent boundary cannot have T=infinity by the same argument. This treats truly silent boundaries as representation ambiguity and does not pretend to detect them.

After locating tau as this functional, return to the original acquired actual all-future law family, without comparing it to the null continuation. For arbitrary later F, those actual probabilities define y_n(F), and exp(-K_n tau)y_n(F) supplies the actual coherent pre-routing old-tuple response interface. This second inversion uses unrestricted actual data, not an equality deduced from the earlier finite horizon. No interface was assumed in advance at every candidate time or at a supremum. Survival-conditioned locations are never assumed independent.

## 6. New reachable epoch, including zero-entry states

At tau, uniformly average each old reachable-state coordinate. For every old hidden-name alignment h, this gives the SAME physical post-routing product entry with probabilities proportional to the column sums of the restricted routing matrix Gamma. Some new reachable states can have zero column sum.

Use the reviewed support/escape saturation on this positive-support family. It expands through the next epoch's migration graph and acquires every state reachable from those boundary columns, without assuming direct positive entry in all new states. Retain old typed reporters and arbitrary main blocks through every joint preparation/escape operation. The invariant support sums make each expanded product entry independent of the old-name alignment; there is no hidden common routing variable introduced by averaging.

The result is a full reachable new generator/rate frame and coherent joint response laws, not merely individual parameter estimates.

## 7. Recover the actual boundary matrix and keep the coupled prefix

Reserve reporters whose preboundary old class is a specified u, rather than averaging them. Their actual post-routing row is Gamma_u in the corresponding old frame. At the beginning of the new epoch, a reporter paired with a prepared new state i has merger-density limit Gamma_ui lambda_i. Directly unentered columns correctly give zero, even when their state is reached later by migration.

For multiple independent reporters and disjoint prepared blocks, the leading joint density of prescribed pair mergers is the product of the corresponding Gamma entries times the known lambda factors. The boundary routing is independent PER LINEAGE, so the products are legitimate. Cross-pair mergers are excluded by the labelled event; they affect higher-order survival terms, not the constant leading density. Preserve a future test on other main blocks to obtain mixed monomial/future coefficients in the same frame.

Before selecting a routing atom, the finite frame mixture is H times J: H is the retained old-prefix symmetry and J is the new local-parameter symmetry. The product here follows from the invariant old-uniform entry and the common-source joint preparation, not from an arbitrary assumption of independent hidden frames. Matrices transform as P_h Gamma P_j^(-1).

Finite positive orbit moments identify the routing orbit. Select one matrix atom using ONE interpolation polynomial for all tuples and future tests. After recentering the selected representative, the remaining group is the coupled stabilizer

    C={(h,j):P_h Gamma P_j^(-1)=Gamma}.

Do not replace C by the product of its projections. For future-only laws, its projection J' onto the new state factor is uniform because every fiber has the same kernel size. Retain C, or its lift to the stored prefix symmetry, for the complete history. J' preserves the new generator and rates and supplies precisely the coherent interface needed for the next epoch.

This closes the intended induction invariant: one selected numeric prefix, its coupled finite symmetry, and actual all-tuple future responses under one fixed source-faithful residual mixture.

## 8. Induction, equality and maximal observable claims

Repeat sections 5–7. Every finite T adds one non-silent boundary of the finite source; local saturation terminates within that source's finite reachable set. The process therefore ends after finitely many reduced boundaries for each promised source, at T=infinity. At each step the choices of representatives can be made consistently within the finite current orbits, retaining rather than discarding their stabilizers.

Equal observable law families yield the same recovered quantities and the same conditional response families through the same finite-orbit selections. Induction therefore yields isomorphic reachable reduced histories. No bound on a rival's original dormant architecture is used: every stage's positive-support counts and leakage test apply to all promised finite rivals with those laws.

Conversely, a coherent isomorphism of the reduced histories gives a pathwise coupling: use the same initial routing, migrated lineage clocks and pair-merger clocks under the state relabellings, and the same independent boundary coins. The labelled timed genealogies agree. Adding back unreachable states or removable permutation boundaries cannot change them. This proves sufficiency.

If the necessity composition is accepted, functions of this reduced history are exactly the invariants of G-equivalence: any G-identifiable mechanism claim must be constant on the reduction fibers, and any specified property of the reconstructed reduction is determined by G. In particular, accessible nontrivial stochastic boundary routing is distinguished from purely finite-rate migration/structure in this ideal observation class; raw pulse-anywhere remains non-identifiable by the explicit ghost example. A biological 'ancestral subdivision' claim still needs its declared population partition and time condition; unlabelled latent demes do not acquire biological identities from this theorem.

## 9. What remains outside this candidate

- Exact effective recognition from arbitrary input descriptions: the T functional uses universal equality over times and panels. Finite-source semantic termination is not an algorithm for arbitrary exact reals or arbitrary purported laws, and does not close original G3/G4.
- Unknown mutation/calibration kernels, topology-only laws, finite sequences and linked genealogies. No inverse kernel is smuggled in.
- Finite-data derivative estimation and numerical stability. The pulse-limit TV obstruction remains compatible with exact identification and blocks uniform finite-experiment certification without separation.
- Zero coalescence rates, infinite migration, shared/common routing, serial sampling, arbitrary continuously varying rates, or zero-duration stacks of separately labelled pulses. They are not in this theorem's stated baseline.
- Historical novelty. Earlier no-migration global alignment, finite orbit bookkeeping and Markov transport are direct antecedents; the reviewed migration-aware reachable acquisition is the specific new supplier being composed, not a new generic inversion principle.

No new computation is claimed for this composition proof. The local executed controls remain at their published bounded scopes.
