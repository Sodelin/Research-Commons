# A small, falsifiable basketball portability pilot

**Author:** dot (OpenAI-assisted research), prepared for Nolan. **Date:** 2026-10-21. **Status:** proposal plus executed synthetic diagnostic, not NBA validation, novelty claim, causal identification result or improvement over EPM/DARKO/LEBRON.

## 1. The concrete proposal

Test whether a very small context-interaction extension to offensive regularized adjusted plus-minus improves **out-of-sample lineup scoring forecasts after a player changes teams**, while reporting when the new deployment lacks historical support. Do not start by inventing a new all-in-one name or replacement-level wins scale.

The intended improvement is narrower than “better player rankings”: lower forecast error, more honest uncertainty and fewer confident extrapolations in changed environments. It could fail all three tests. Role awareness, interactions, shrinkage and portability concerns are established ideas. The possibly useful contribution is their particular transparent implementation and a demanding transfer-specific evaluation, not a claim to have discovered them.

First version concerns offensive points per possession only. It does not measure defense, total NBA impact or a player's inherent talent. Defensive and net-impact extensions wait for evidence that this simplest version helps.

## 2. Two different estimands, one primary

**Primary, observable predictive estimand:** expected offensive points per possession conditional on a specified offensive five, defensive five, date and pre-possession context, using only information available before the forecast cutoff. A fixed future block's realized scoring supplies an observable, noisy evaluation outcome. Evaluate post-team-change possessions separately, without calling their realized outcome the incoming player's isolated contribution.

**Secondary, model-dependent deployment contrast:** for a stated distribution Q of four teammates, five opponents and game contexts, compare the fitted expected lineup scoring with eligible player p versus player r occupying the fifth offensive slot:

    Delta(p,r;Q) = 100 E_Q[m(p, four, opponents, context)
                          - m(r, four, opponents, context)].

This is a conditional model contrast unless additional causal assumptions hold. Q must be explicit and frozen before evaluation, not silently chosen to make a player attractive. It is not the realized result of a trade: trades can also change coaching, health, minutes and everyone else's actions. If the proposed deployment is unsupported, present a scenario contrast and support warning, not an identified player-value estimate.

**Fantasy is separate.** Fantasy points weight box-score events with league rules and usable starts. A screen or rotation can improve team offense without earning fantasy points. This pilot cannot be inserted into a custom fantasy scoring calculator as a replacement for stat/minutes projections. Fantasy evaluation would require a different outcome, availability and lineup-eligibility model.

## 3. Minimal model that can actually be implemented

Use possession or short-stint records with reconciled offensive and defensive lineups. Let z_p be the player p offensive indicator and d_q the opponent q indicator. Baseline (also include the common lineup perimeter-attempt-mix main effect in X):

    m0 = mu + sum_p z_p a_p + sum_q d_q b_q + gamma' X.

Fit weighted ridge regression; stint weights are possessions. X is deliberately short: home court, period, pre-possession score margin and season intercept. No outcome-created variables. Penalize player coefficients; handle intercept and reference constraints explicitly. First reconcile score, substitutions, free throws and possession boundaries. Zero-possession stints must not be divided into rates.

Compare an additive-only ablation, an additive-plus-common-context baseline, and the candidate. Give all models the same tuning budget. Candidate adds one interaction per offensive player:

    m1 = m0 + sum_p z_p u_p (s_{-p} - s_ref).

s_{-p} is the mean of the other four offensive players' **lagged** three-point-attempt/FGA rates, calculated strictly before the forecast cutoff. It is a public-data teammate perimeter-attempt-mix proxy, not measured floor spacing, gravity, shot quality or the player's complete offensive role. Use a fixed training-derived shrinkage prior for low-attempt teammates and record its value. Center on a training-only reference. Penalize u more strongly than main effects; choose penalties using blocked validation, including the option u=0. Both models receive the same recency weighting and cutoff data.

This adds one parameter per player rather than all player pairs, triples or lineups. It is not guaranteed to represent the important interactions. A rim finisher might respond differently to other teammates' shooting tendencies than a self-creating shooter, but this is a testable modeling hypothesis, not a conclusion about any particular player.

When replacing p by r, recompute **every affected teammate's** s_{-j}; otherwise the proposed replacement contrast omits spillovers already encoded in this model. Do not interpret u_p alone as the complete replacement effect. An algebraically redundant design can still produce stable predictions under regularization while leaving coefficients nonidentified; inspect design rank and predictive sensitivity rather than assuming coefficient uniqueness proves identification.

## 4. Support and uncertainty are part of the output

For each requested player/deployment report the target teammate perimeter-attempt-mix proxy, its historical range, counts of distinct games and possessions near the target, teammate/opponent overlap and sensitivity to regularization. A preliminary support flag could require at least ten historical games near the target and target location inside the player's training 5th–95th percentile range. These thresholds are engineering choices to tune only on validation, **not a positivity theorem**. Marginal overlap on one scalar does not establish overlap in complete lineups, coaching or health.

Separate three things:

1. Sampling uncertainty conditional on the fitted model, assessed using game or larger temporal blocks, not independent possession resampling.
2. Model sensitivity across predeclared penalties, decay windows and feature exclusions.
3. Unsupported-deployment sensitivity. If a response slope is bounded by an assumed L, show how the range changes with L and distance from observed support; label it assumption-based. Do not manufacture a finite bound without a defensible restriction.

Block-bootstrap intervals have no automatic finite-sample guarantee under changes of team, health or strategy. Evaluate empirical coverage and width on future observable outcomes. A predictive interval for future scoring includes outcome noise; an interval for expected scoring does not. Neither is automatically an interval for causal replacement value.

Causal interpretation additionally requires well-defined interventions/consistency, adjustment for relevant lineup-selection confounding, overlap, a defensible account of interference within the lineup, and stability or an explicit model of environment change. Coach choice, undisclosed injuries and tactical targeting threaten these assumptions. More possessions do not repair a missing counterfactual comparison.

## 5. Closest established work, not straw-man baselines

- **RAPM:** additive player adjustment plus regularization is the natural reproducible baseline. Our added interaction is a hypothesis to test, not proof additive RAPM is generally inadequate.
- **BPM:** the official description identifies it as box-score-based player contribution estimation. It is useful as a lower-data comparator, not the strongest available predictive baseline. [BPM methodology](https://www.basketball-reference.com/about/bpm2.html).
- **EPM:** its creator describes predictive skill estimates, tracking inputs and RAPM combination. It already addresses noisy small samples and career information. Do not claim our one-feature extension has these capabilities. [EPM methodology](https://dunksandthrees.com/about/epm).
- **DARKO:** a dynamic, next-game projection system with player-stat and plus-minus forecasts. A static model should not be credited for beating an unfair stale snapshot. [DARKO methodology](https://www.darko.app/about).
- **LEBRON:** already uses role-informed stabilization and a box prior with adjusted on/off estimates; explicitly distinguishes impact from talent and acknowledges deployment/fit. “Add role” is not novelty. [LEBRON introduction](https://www.bball-index.com/lebron-introduction/).
- **De Bacco, Wang and Blei (2024):** causality-inspired plus-minus explicitly models lineup assignment and hypothetical replacement. This is particularly close conceptual prior art. Its presence rules out claiming replacement counterfactuals as a new idea; its identification assumptions do not eliminate all possible individual unobserved confounding. [Primary paper](https://proceedings.mlr.press/v236/bacco24a.html).
- **Josephs and Upton, Hypergraph adjusted plus-minus:** jointly models individual and group contributions. Interaction modeling itself is prior art. [Primary paper, revised 2025](https://arxiv.org/abs/2403.20214).
- **Petridis and Pelechrinis, L-RAPM (2026):** lineup ratings with player-informed priors specifically address sparse lineup observations. Include it if a reproducible implementation and lawful data are available; this review checked the abstract, not its full empirical protocol. [Primary preprint](https://arxiv.org/abs/2601.15000).

This is a bounded prior-art screen, not an exhaustive novelty search. Published methods may have additional implementations or unpublished commercial capabilities.

## 6. Data and benchmark gate

Publicly documented PBP Stats endpoints expose lineup totals, game logs and possession queries. The possession endpoint documents a 500-result cap, so a single response must never be assumed a complete season. [API documentation](https://api.pbpstats.com/docs); [maintainer possession documentation](https://pbpstats.readthedocs.io/en/v1.3.5/pbpstats.resources.possessions.html).

Potential inputs, only after authorization/rights verification: appropriately licensed play-by-play/lineup records and box scores or user-provided authorized exports. Public visibility does not establish permission for downloading or model training. No paid tracking, credentials, access bypass, bulk commercial-metric scraping or redistribution is assumed. API documentation availability is not blanket permission to redistribute source data. Public availability and reproducible complete retrieval must be checked before acquisition.

No audited possession/lineup corpus was used in this pilot. The executed experiment is synthetic only; no NBA data validation is claimed.

Required data schema: game/date, possession/stint ID, offense/defense team, ten player IDs, points, possession count, pre-possession context, source/version and completeness flags. Maintain game-level score/lineup reconciliation checks, missingness counts, train-cutoff fingerprints and a versioned feature manifest.

## 7. Locked evaluation proposal

Proposed development: seasons through 2023–24. Tune on 2024–25 using forward chronological blocks, no random possession split. The 2025–26 season may serve as a retrospective audit, but selected season aggregates have already been inspected; do not advertise it as globally untouched. The first genuinely prospective target is games after a frozen protocol/data snapshot later than this memo, with the exact cutoff recorded before seeing those outcomes. No prospective test has yet been launched or registered.

At each evaluation cutoff, freeze all player ratings and feature construction. Forecast the first ten played games for each verified team change. Define roster-change eligibility from roster transactions, not subsequent performance. Changes with no subsequent appearance remain counted in the cohort disposition rather than quietly disappearing. Analyze availability separately. Ten-game completion can run beyond a calendar horizon; fix a closing date in advance and report incomplete cases.

Primary diagnostic is conditional on realized lineup exposures: compare predictions for the same observed possessions so minutes forecasting cannot create an artificial edge. Clearly call this an exposure-conditioned forecast evaluation, not a fully pregame lineup forecast. A later operational pregame test would supply the same independent minutes/lineup forecast to every competing method.

Compare (A) additive ridge; (B) same ridge plus the one interaction; (C) a role-stratified shrinkage baseline; (D) available historical as-of EPM/DARKO/LEBRON/BPM snapshots mapped to the same outcome with an offensive/defensive combination calibrated using training only. Do not use present-day revised historical ratings as if they were contemporaneous. Where timestamps, lawful access or offense/defense components are missing, omit that comparator with an explicit reason. Do not silently substitute a weaker baseline and claim superiority to commercial systems. Seek L-RAPM or the causal model as additional comparators if feasible.

Primary score: possession-weighted squared error on game/team offensive rates, with uncertainty for **paired** error differences clustered at least by game and sensitivity to repeated players/teams. Report transfer and stable-team cohorts, support strata, prediction-interval coverage/width and risk-versus-abstention coverage curves. Every model is scored on the same cases; show all-case loss as well as any gated subset. A method must not win by dropping its hardest cases. Standardized transfer-cohort membership and game aggregation are fixed before testing.

Success gate: lower paired forecast loss in the transfer cohort without material degradation in the stable cohort, and empirically defensible uncertainty at useful coverage. Predefine the material degradation threshold before the prospective test. A win on prediction does not validate causal player replacement values. A loss, unstable signs, excessively broad intervals or near-universal abstention is a publishable-to-the-user negative finding, not a reason to search new splits until something wins.

## 8. Executed synthetic stress test

Run `python synthetic_portability_v2.py` with existing Python/numpy. Two hundred seeds, twenty fictitious players, two hundred observations per player. Training context-1 probability .15 changes to .85 at evaluation. Noise SD5 in arbitrary centered response units, not NBA points per100 possessions. Reported losses are squared response units. Player main effects plus a common context slope are compared with player-specific slopes shrunk toward that common slope. The common context term is included to avoid crediting interactions for an omitted main effect. This is **not a full five-on-five RAPM simulation** and has no NBA data.

With true heterogeneous context effects, mean squared error against the known conditional mean falls from **8.3860 to 1.9931**. With context effects exactly zero, it rises from **0.1537 to 0.3404**. Independent future outcome noise would add25 to each expected squared error. These constructed examples demonstrate both the potential mechanism and the overfitting cost; they do not estimate NBA effect sizes, tune a basketball model or beat a real metric.

An exact zero-overlap construction gives two worlds with identical observed data at context0 but target context1 means8 and−4. Any single prediction has worst-case absolute error at least6 across those worlds. The interval[−4,8] follows only after assuming known baseline2 and absolute slope≤6; with estimated baseline it also needs sampling uncertainty. With no bound on the slope the observed data give no finite target bound. This is the strongest immediate design lesson: report missing support instead of mistaking shrinkage's chosen extrapolation for information.

## 9. Result and exact next step

**Result:** one tractable candidate, honest benchmarks, an executable positive/negative-control diagnostic and a precise nonidentification example. No NBA superiority, new theorem, novel statistic or causal-effect guarantee established.

**Next step:** obtain and audit one complete historical season of lawful possession/lineup data plus the preceding season for lagged features; verify ten-player reconstruction and score reconciliation before fitting anything. If that passes, fit only the additive and one-interaction models under the predeclared chronology, then expand the benchmark. Missing data or inaccurate lineups stop the empirical stage, not the conceptual inquiry.

## Access audit correction incorporated before release

The independent access review found important restrictions: NBA's [Stats FAQ](https://www.nba.com/stats/help/faq) says data downloads are not permitted, including personal/academic uses. This pilot must not use an API as a workaround. DARKO's [assistant terms](https://www.darko.app/assistant-terms) distinguish reconstructed pregame history from archived originally published daily estimates; historical refits can revise those histories. They do not supply a blanket bulk dataset license. Sports Reference's [data-use policy](https://www.sports-reference.com/data_use.html) requires a separate permitted-use review; the review encountered a403 for full policy retrieval, so training/redistribution authorization is unresolved. A parser's MIT software license is not a license for upstream basketball data.

Accordingly the next empirical step is first to establish a permitted complete dataset and timestamp provenance, **not automatically to download a season**. If no such source is available, keep the pilot synthetic or use an authorized user-provided dataset. No third-party raw tables or commercial metric histories are included in this packet. No genuinely prospective NBA benchmark has been started.
