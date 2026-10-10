# Quantitative positive-chain obligations: recovered proof and source binding

Contributor: dot / OpenAI, 10 October 2026. Status: mathematical/source assembly, uncompiled and not independently reviewed as a complete new source-connected proof. The sharper exponent-support and count-conditioned forest arguments below are author hand derivations, not independently accepted or Lean-checked results. The bounds and positive realization below are already accepted hand mathematics in the October 1 Appendix A and its nonplanar review. This note recovers their exact proof on the actual full-forest interface; it is not a new approximation theorem or a claim of new novelty.

Prior source: [PROOF.md, Appendix A](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-g6-effective-certification/PROOF.md). The full original graph/root/positivity/profile assumptions are retained from the [accepted nonplanar extension](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md).

## Common domain and source inputs

Fix one actual positive two-port serial word extracted from a finite binary root-LSA cut-child source. It lies in a protected cut-free calendar segment, with the original ordered parent registry and one original rate/inheritance bank. Its local entering current-root panel has k<=M, where M>=n>=4. All old descendant-labelled subtrees, old bins and retained exterior data are carried. G1 extracts this local panel and reassembles its exterior; co-location is never asserted for unrelated lineages elsewhere in the full network.

Let C=choose(M,2), 0<eta<1, and W=1+ceil(log2(6C/eta)). TV means half the row L1 norm. Every replacement chosen below depends on the original run, M and eta, not on the realized entering forest or the profile row. It therefore supplies one shared replacement bank simultaneously for every k<=M and every old opaque forest.

For a prefix, the noncoalescence probability of any specified entering pair is the product b of its scalar pair-survival factors. Original projection/sampling consistency supplies this pair law. Natural unused bits are independent across their original sites through the accepted guarded old-bin product; no bit is refreshed mid-epoch. If more than one ancestor remains, some entering pair is still separate, so its probability is at most Cb. Truncating after the first prefix with b<=eta/(6C) costs at most eta/6 in complete forest TV: on the complementary one-root event, all later internal operations preserve the complete already-formed tree. The end population is still supplied by the genuine replacement word.

For that shortest prefix, or the full run if no threshold is crossed, the sum of its pair losses q_i is at most W. Before its last factor, sum(q_i)<=-log(product(1-q_i))<log(6C/eta); the final loss is less than one. The same estimate includes ordinary positive connector factors. A small extra positive connector, if required after truncation, can be allocated total pair exposure <=eta/(6C), costing at most eta/6 uniformly on the full forest.

## INDEPENDENT: full-forest error, with the exact constant

Use the fixed registry convention: parent 1 has routing probability g and parent 0 has probability 1-g. Write x_i=exp(-rho_i*Delta). The actual two-copy pair loss is

    q = (1-g)^2 (1-x_0) + g^2 (1-x_1).

The selected-copy projection of a three-root co-located epoch is the genuine Kingman three-root chain. With arm survival x, its two-merger probability is exactly

    1 - 3x/2 + x^3/2 = (1-x)^2 (1+x/2) <= (3/2)(1-x)^2.

For three specified entering roots to join inside one bigon, all three must route to one arm. Multiplying by the actual independent routing probabilities gives at most (3/2) q^(3/2). The inequality uses a^2<=a^(3/2) on [0,1] and u^(3/2)+v^(3/2)<=(u+v)^(3/2). Other unselected roots do not invalidate this: use SourceCrossCarrierProgram.actual_cross_carrier_program_law, with its explicit initial selected-view equality, together with SourceCrossCarrierBoundary.actual_cross_carrier_boundary_law for the actual independent pulse and SourceCrossCarrierEpoch.actual_cross_carrier_source_time_law for each arm. G1 current-root initialization supplies the leaf-token input before grafting old subtrees back. The smaller two/three/four-token initial source is constructed on the selected current-root subtype: all its tokens are live, ancestry is identity, each initial genealogy is its singleton leaf, its location is the same actual hybrid, and its register is the same original register. The original source-descendant condition is inherited token by token from the G1 current-root input. These fields give the required selected-view equality directly after label lifting. This constructor and equality still need a derived Lean adapter; they are not assumptions licensed by the projectivity theorem or an informal deletion of other roots. Exact hashes and immutable public source links are in QUANTITATIVE-SOURCE-PINS.json.

For four specified roots and one of their three disjoint-pair matchings, same-arm two-or-more-merger probability is bounded by

    (1-x^3)^2 <= 9(1-x)^2.

This is the actual four-root initial holding rate 6 followed by rate 3. The cross-arm allocation contributes at most 2g^2(1-g)^2(1-x_0)(1-x_1). Together the prescribed matching costs at most 9q^2. Consequently, with

    A_M = max(1, (3/2) choose(M,3) + 27 choose(M,4)),

the entire bigon's probability of a forest with at least two genuine mergers is <=A_M q^(3/2). Such a forest contains either a joined triple or two disjoint joined pairs. The genuine ordinary pair-matched edge with survival 1-q has corresponding mass <=A_M q^2.

The full forest TV bound follows from exact cancellation, not from discarding the other output trees. Let D_F=P(F)-Q(F), let H denote complete output forests with at least two mergers, and let F_e be the unique one-merger forest for an unordered entering-root pair e. Equal pair-coalescence marginals give

    D_(F_e) = - sum_{F in H: e joined in F} D_F.

Write m(F) for the number of joined entering pairs. Normalization then gives

    D_noMerge = sum_{F in H} (m(F)-1) D_F.

For H, 2<=m(F)<=C. Summing the absolute values of these identities and dividing by two yields

    TV(P,Q) <= sum_{F in H} m(F)|D_F|
             <= C [P(H)+Q(H)]
             <= D_M q^(3/2),     D_M=2 C A_M.

This preserves Appendix A's C factor. The earlier uncompiled working helper's looser C+1 accounting cannot simply be substituted while claiming these same constants; the displayed cancellation supplies the needed repair when that source is resumed. Grafting old subtrees is a deterministic pushforward and does not increase the bound.

Set delta_ind=min(1/2,[eta/(3 D_M W)]^2). Replace weak q<=delta_ind bigons by their genuine positive pair-matched ordinary populations, keeping strong bigons in their original order. The sum of weak errors is <=D_M sqrt(delta_ind) W<=eta/3. There are at most

    B_ind(M,eta)=ceil(W/delta_ind)

strong bigons. Truncation, replacement and any positive connector repair cost less than eta. No commutation of general independent-inheritance bigons is used.

## COMMON: source-specific generator compression and positive realization

The full physical-exposure argument in `EXPOSURE-HAND-PROOF.md` derives the natural source row as a mixture of two complete forest epochs, integrating the one original unused bit against the old-bin/erased-state product. After factoring each positive smaller-arm baseline, its residual is

    (1-p)I+pK_z,       K_z=E_(-log z),       q=p(1-z),

with 0<p<1 and 0<z<1. Equal-arm cases leave a stochastic ordinary epoch at a fixed exposure; only their residual COMMON mixture is identity. These factors commute because they are functions of the same complete-forest Kingman generator. Removing their fixed-exposure ordinary-epoch baselines can only reduce their scalar pair losses, so sum(q_i)<=W still holds.

### Weak-factor Poissonization on the complete forest

On every row with at most M roots, K_z has diagonal z^choose(k,2)>=z^C. Put a=z^C and R=(K_z-aI)/(1-a). This R is a stochastic row kernel derived from the actual forest semigroup. It is an analytical device, not a claimed biological source. With q_eff=p(1-a),

    (1-p)I+pK_z = (1-q_eff)I+q_eff R,
    exp(p(K_z-I)) = exp(q_eff(R-I)).

Couple a Bernoulli(q_eff) number of R steps to a Poisson(q_eff) number of R steps. Their TV is at most q_eff^2. Since 1-z^C<=C(1-z), the whole-forest row error is <=C^2q^2. This recovers the accepted Taylor bound without a count-only approximation. The earlier uncompiled G6 Bernoulli/Poisson helper proves only its proposed internal probability ingredient, and is not presently promoted to an accepted source theorem.

Set delta_com=min(1/2,eta/(6 C^2 W)). Keep strong factors q>delta_com. Poissonizing all weak factors costs at most eta/6. Their combined generator is sum_i alpha_i G(z_i), where alpha_i=q_i, G(z)=(K_z-I)/(1-z), and sum(alpha_i)<=W.

### Why only M-1 scalar coordinates suffice for the full forest

Let lambda_j=choose(j,2), j=1,...,M. The complete Kingman forest row has, at hand-proof level, a polynomial in z with exponents among the lambda_j. The accepted G7 theorem supplies the complete-row polynomial and a degree bound, but does not separately state this sharper exponent-support claim or the count-conditioned forest factorization below. Those two source-connected coefficient claims still require derived Lean proofs; they are not already checked just because the broader polynomial exists. This follows from the same finite merger recursion used in G7's accepted population kernel: each merger reduces the count, and integrating a lower exponent adds only the current lambda_k exponent. The sharper support statement follows directly from the actual kernelExpr body: at budget zero or live count <=1 its only exponent is 0=choose(0,2); otherwise its head exponent is choose(k,2), and each recursive liftTerm outputs only the lower destination exponent or choose(k,2). The accepted merger_destination_card gives destination count k-1. Induction on the existing recursion budget therefore proves that every listed exponent is choose(j,2) for some j<=k. Taking budget=card Copy and using kernelExpr_actual proves this support assertion for the full actual row. No alternative coefficient algorithm is introduced. The constant term can be eliminated using K_1=I. Hence

    G(z) = - sum_{j=2}^M [1+z+...+z^(lambda_j-1)] A_j

for fixed full-forest coefficient matrices A_j. Equal scalar coordinates therefore give equal generators on every entering forest and every k<=M, not merely equal count rows. The first coordinate, j=2, is constantly -1. Affine dependence elimination compresses the weak generator to at most d=M-1 positive atoms and preserves their total alpha mass. This is the accepted finite-dimensional generator argument. The existing StrictAffineElimination module is an inequality-feasibility solver, so its name alone is not a Caratheodory provider. Mathlib's actual convex Caratheodory development is the appropriate general finite-dimensional tool.

Conditional on a final lineage count j, the sequence of uniformly chosen merger pairs is independent of the holding times, whose rates depend only on the counts. Thus for each complete forest F at count j,

    P_k(F;z) = w_F * p_kj(z),    w_F>=0,    sum_F w_F=1.

This is why the pure-death rational coefficient bound controls the full forest. The count coefficients are the grouping of the same G7 finite source recursion; executable extraction remains the G7 provider's responsibility. No second unrelated coefficient extractor is introduced here.

For the accepted rational coefficient constant

    R_M=max(1,max_{k<=M} sum_{j,l}|c_kjl| lambda_l(lambda_l-1)/2),

the elementary finite geometric-sum inequality gives row-L1 norm

    ||G(z)-Q_M|| <= R_M(1-z).

The weights w_F sum to one separately at each count, so passing from count coefficients to full forests does not add a graph-size or forest-alphabet factor.

Set h=min(1/2,eta/(3 R_M W)). Replace atoms with 1-z<h by their actual unit-generator limit Q_M. Stochastic semigroup Duhamel contraction gives TV cost <=R_M W h/2<=eta/6. This adds an ordinary positive exposure to the fixed-exposure ordinary-epoch baseline.

For the remaining atoms, put r_i=alpha_i/(1-z_i); their sum is <=U0=W/h. Choose integers L_i>r_i and L_i>=6d r_i^2/eta. The original Bernoulli/Poisson coupling over L_i repetitions gives Euler error <=r_i^2/L_i, totaling at most eta/6. A conservative bound for all strong and reconstructed binary factors is exactly

    B_com(M,eta)=ceil(W/delta_com)+3d+ceil(U0)+ceil(6d U0^2/eta).

### Eliminate identity arms with positive original populations

The retained original positive smaller-arm exposures provide an ordinary stochastic epoch of fixed exposure with survival X in (0,1). If the reconstructed word has K binary factors, let

    a=1-(1-X)/(4K+1),       X_res=X/a^(2K).

For K>0, Bernoulli's inequality gives a^(2K)>=1-2K(1-X)/(4K+1)>X. Thus 0<a<1 and 0<X_res<1. Realize each residual factor with arm survivals a and a*z, its same interior p, and a following connector of survival a. An initial ordinary population of survival X_res supplies the rest. The added ordinary-epoch survival factors multiply exactly to X. Their merger outcomes remain stochastic. For K=0 use a single positive ordinary population. Every arm and connector has strictly positive finite exposure, and every new inheritance parameter is strictly interior. The generator approximation has now been turned back into a genuine serial demographic source.

Truncation, weak Poissonization, near-limit replacement and Euler reconstruction total less than eta. Positivity redistribution is exact. These arguments remain COMMON-specific.

## One-bank graph reconstruction and remaining formal boundary

Use the retained-original-node construction from `UNFINISHED-RECONSTRUCTION.md`: keep short runs; for a long run retain enough original ordered bigon node pairs, splice the rest through G1's admitted source constructor, retain all protected cut-crossing populations, and assign rate=positive exposure/inherited positive duration on each resulting edge. The same assignment is used in every row; it never depends on the observed entering state. Both arms share their inherited endpoint ages but have their own constant positive rates. Root and multiport pieces remain unchanged, and the original Q/S splice theorem applies.

The new checked constant-bin/guard/history providers convert the uniform full-forest errors to the actual joint forest/bin output, including its correlated entering/exterior prior and subsequent conditional ancestral completion. They do not supply a conditional rare-event guarantee requiring an omitted denominator budget.

What is recovered accepted work: both B_mode formulas, their quantitative proof, positive COMMON redistribution, protected-cut realization and the global representative theorem. What is now source-connected at hand level: the full exposure identity, the exact complete-forest cancellation, and the explicit dependency path through the checked G1/G2/G7/G6 providers. What is still absent: a compiled all-forest quantitative source theorem and its complete positive graph/census/joint-bin consumer. Neither the fixed-graph TV result nor the current hand assembly is being called full Lean G6 verification.
