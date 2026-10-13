# Actual four-taxon COMMON fixture for the informative padded rows

Author: dot, 13 October 2026. Hand-derived source fixture and local exact-data checks; no new Lean instance, native forward table, or compiler execution. This is a regression fixture using accepted constructions, with no novelty or general G3 claim. `PHYSICAL-FIXTURE.json` is an inspectable mathematical record, not a claim that the existing native parser accepts this new schema. `COMMON-MENU.json` uses the existing supplied-menu schema.

## 1. One original source and one physical tuple

The four taxa are A,B,C,D. Vertex indices, original names and ages are:

| Index | Name | Age | Role |
|---:|---|---:|---|
|0|R|4|root|
|1|U_AB|3|tree|
|2|U_CD|1|tree|
|3|S_A|2|tree|
|4|H_A|1|hybrid|
|5|A|0|leaf|
|6|B|0|leaf|
|7|C|0|leaf|
|8|D|0|leaf|

The original directed edge occurrences are:

| ID/index | Endpoints | Duration | Pair survival |
|---|---|---:|---:|
|e0 / 0|R → U_AB|1|1/2|
|e1 / 1|R → U_CD|3|1/2|
|e2 / 2|U_AB → S_A|1|3/4|
|e3 / 3|S_A → H_A|1|8/9|
|e4 / 4|S_A → H_A|1|8/9|
|e5 / 5|H_A → A|1|3/4|
|e6 / 6|U_AB → B|3|1/2|
|e7 / 7|U_CD → C|1|1/2|
|e8 / 8|U_CD → D|1|1/2|

For each occurrence e, set its pair rate to `-log(x_e)/duration_e`, and set ancestral pair rate to 1. All rates and durations are strictly positive and finite. This exact assignment is shared by every row. The parallel occurrences e3 and e4 remain distinct even though their endpoints and rates agree.

There is exactly one original hybrid, ID `H:pendant-A`, index 0, at vertex H_A. Its ordered parent registry is `(e3,e4)`. The probability of original parent bit 1 is Gamma=1/3; bit 0 has probability 2/3. This is a genuine interior COMMON coin, drawn once per locus for all current lineages. In the inherited native parent-zero convention the parameter is 2/3. The `source_fit_bank` variable is `g_H_A`, alongside x0,…,x8. Do not swap the incoming occurrences to compensate for a mistaken convention.

The configuration carrier has one element `natural`, of mass 1, whose mask at `H:pendant-A` is null. The natural bank has two positive-mass configurations, of weights 2/3 and 1/3. No source existence or target is assumed by the certificate: the graph and physical tuple are explicitly supplied here. No extra parameter predicates are imposed.

## 2. Original-source admission

The graph is obtained from the rooted quartet ((A,B),(C,D)) by inserting one parallel-arm bigon on its pendant A bridge, with positive leading and following edges. This is exactly the permitted construction in the inherited [source proof, Sections 1.1, 3 and 4.2](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md).

Directly: R has degree (0,2); U_AB,U_CD,S_A have (1,2); H_A has (2,1); the four leaves have (1,0). Every edge strictly decreases age, so there is no directed cycle. Every vertex is reachable from R. No nonroot vertex dominates all four leaves, because the A/B and C/D routes split at R. The sole hybrid child edge e5 is a bridge. A planar drawing of the quartet with a small two-arc lens along its A pendant branch keeps all four leaves on the exterior face. Thus binary, root-LSA, cut-child and outer-labelled admission all hold. The local data check verifies the finite degree/reachability/bridge conditions; the explicit lens construction is the hand outer-face certificate.

The ages were chosen to equal the native `source_fit_bank::heights` recursion literally: each leaf has height 0, each other vertex has one plus its maximum child height. In particular U_CD has age 1, not the age 3 used in an early informal proposal. Its changed duration is compensated in the displayed rate, leaving its prescribed whole-edge survival unchanged. The final JSON and table agree. The unrelated H_A and U_CD operations may share date 1; no physical edge has zero duration.

## 3. Whole-bank law and directed survival

For either original coin value, the A-side route before first meeting B contains e5, exactly one of e3/e4, and e2. Its survival is

`(3/4) * (8/9) * (3/4) = 1/2`.

The meeting is at U_AB, at age 3, for both banks and all three arities. No A/B common ancestral edge is included in the directed A-side exposure. Equivalently, the exposure is log(4/3)+log(9/8)+log(4/3)=log 2. Tied boundary operations contribute no interval exposure.

This is a full source-law simplification, not a product-of-marginals argument: conditional on the one COMMON bit, the whole entering forest uses one arm. Both arm kernels are the same ordinary Kingman kernel E(8/9). The complete pendant kernel is therefore E(3/4) E(8/9) E(3/4)=E(1/2), by the ordinary source semigroup. Its two bank values give the same weighted quartet. The coin is averaged only after its complete use. Unary suppression adds the three edge exposures; it does not set a connector length to zero.

The resulting directed survivals are 1 on diagonal pairs, 1/2 within A/B or C/D, and 1/4 between those two cherries. Consequently the accompanying complete 16-pair menu has 48 exact normalized rows, all realized by this same tuple. The primary milestone remains the three A→B rows below. This equal-arm source does not test an observationally detectable Gamma reversal; retain explicit ID/convention assertions and the existing asymmetric-arm regression separately. A singleton configuration also does not exercise multi-site forcing correlations.

## 4. Exact legal padded rows, direction, event and normalization

At level k use exactly `((Fin k ⊕ Unit) ⊕ {A,B,C,D})`:

- selected A copies a0,…,a(k−1), with tags `inl(inl i)`, sample at A;
- selected copy b, tag `inl(inr unit)`, sample at B;
- four distinct baseline copies, tags `inr A`,…,`inr D`, sample at their respective taxa.

The full input copy counts are 6,7,8 at k=1,2,3. The baseline A is different from a0, and baseline B is different from b. The JSON supplies explicit indices and tags. All original taxa are sampled at every level. Use the completed rooted labelled unranked forest law on the entire padded carrier first. The observed event is the preimage, under passive pruning to the selected tags, of the singleton forest containing the one specified comb. Delete only the four baseline leaves in the readout, suppress unary genealogy vertices, remove empty pruned trees, and quotient only by child swaps. Do not erase the gene-tree root, aggregate over all comb orders, or run a smaller input instead of the padded input.

The comb starts at b and left-folds grafts with a0,a1,… in that order:

- k=1: `(b,a0)`;
- k=2: `((b,a0),a1)`;
- k=3: `(((b,a0),a1),a2)`.

The accepted `actual_legal_observed_moment` and `actual_randomized_legal_moment` providers identify this actual readout, divided by `combCoefficient k = 2^k / ((k+1)! k!)`, with the one-bank moment `E[X^choose(k,2)]`. With X=1/2:

| Level k | Padded copies | Exponent | Comb coefficient | Normalized moment | Raw event probability |
|---:|---:|---:|---:|---:|---:|
|1|6|0|1|1|1|
|2|7|1|1/3|1/2|1/6|
|3|8|3|1/18|1/8|1/144|

One can also see why the specified event has this factor: any merger of two A lineages before their meeting B prevents the B-starting comb. Conditional on no such merger, the particular post-meeting order has the displayed ordinary Kingman probability. The accepted full-panel projectivity theorem justifies this calculation despite the baseline copies. This is not an assumption that the hidden no-merger event itself is observed.

## 5. Existing certificate and exact claim limits

The A→B certificate is `P(x)=x^3−3x/4+1/4=(x−1/2)^2(x+1)`. Its coefficient vector on exponents (0,1,3) is (1/4,−3/4,1); the supplied moments are (1,1/2,1/8). Their pairing is exactly zero. P is nonnegative on [0,1], and P(0)=1/4 is nonzero. The sum-of-squares record uses `(x−1/2)^2 + x(x−1/2)^2`, matching the existing singleton generator.

The actual source has exactly one distinct survival value in the A→B pushforward, but two positive natural bank configurations. The generic L=3 support wrapper concludes only `card ≤ L−1 = 2`. To derive at most one from this polynomial for arbitrary compatible sources, additionally use its explicit positive root set {1/2}; that is a separate cubic-root corollary. Neither conclusion bounds graph/hybrid size or proves arbitrary-input source acquisition.

## 6. Exact encoding and remaining executable checks

All nine whole-edge survival coordinates and the natural coin probabilities are rational. The calendar durations here are positive integers. Coalescent exposures and physical pair rates are logarithmic expressions; they are not falsely encoded as rational/algebraic rates or rounded decimals. If one instead fixes unit rates, the necessary durations would in general be logarithmic and cannot be substituted as rational dates.

The existing `source_fit_bank` representation explicitly preserves logarithmic rates and exact positive-root constraints. For example, e6 has total survival 1/2 over duration 3, so a unit calendar subinterval has survival `(1/2)^(1/3)`, not 1/2. All of its subinterval coordinates derive from that same edge rate. The ancestral rate is 1; unused ancestral interval coordinates must retain the existing inactive-marker convention. This fixture supplies no automatic acceptance by the older rational-inverse-rate calendar DTO.

Next checks for the existing integration owner:

1. Authenticate these graph/occurrence/label maps and the ten native survival/inheritance coordinates. Run actual binary, root-LSA, cut-child and outer admission, retaining the exact witness and original ordered occurrences.
2. Bind the literal height calendar and the same survival tuple. Verify parent-zero 2/3 complements to Gamma1/3; verify the fixed graph's fractional interval powers by their positive algebraic root constraints, without evaluating logarithmic rates as rationals.
3. Under a separately admitted COMMON8-or-equivalent profile and pre-expansion resource guards, obtain the actual full rooted labelled tables for the three padded allocations. The currently selected four-copy profile must report UNKNOWN; the proposed COMMON6 profile alone cannot run k=2 or 3.
4. Apply the actual pruning/event operation to those tables, obtaining precisely (1,1/6,1/144), then normalize to (1,1/2,1/8). Check total mass, nonnegativity, duplicate-tag rejection and changed-pruning negative controls. Do not substitute the formulas above for an emitted-table execution receipt.
5. Reuse the existing singleton/certificate checker and actual-row wrapper; keep source instance proof, wrapper elaboration, native refinement, and final execution/audit receipts separately labelled.

## 7. Exact prior and source pins

- [21:49 informative-row review](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/research/2026-10-13-dot-informative-row-review-2149z/README.md).
- [Original positive-source construction and complete forest compiler](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md), Git blob b41fdf706e4dfcb5d14ffdbc88631012674ef1f4.
- [Selected G4ActualLegalPanelComb](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/4fd78fc530e103512f4dc98a7e60ac2d592ad666e7feac17b5ab1456f1a961c9.lean), SHA256 4fd78fc530e103512f4dc98a7e60ac2d592ad666e7feac17b5ab1456f1a961c9, Git 230d6073bd20c74c8d07f473b4c7c0d7a592448c. Uses `paddedSample`, `paddedKeep`, `paddedA`, `paddedB`, `actual_legal_observed_moment`.
- [Selected G4WholeProfileDetermination](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09.lean), SHA256 fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09, Git 5a866bc90937ae00981a0f1305a58a07704036e4; `randomizedLegalCombMoment` and `actual_randomized_legal_moment`.
- [Current supplied actual-row support wrapper](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/research/2026-10-13-astra-legal-row-support-2115z/lean/Astra/ActualLegalRowSupport.lean), Git e08d222e15f75a986c4544475db9bb2a4db0c60e. Its new-wrapper compilation status remains separate.
- [Existing singleton input](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/research/2026-10-13-astra-unified-solver-0645z/examples/singleton-generator.json), Git 31727f73e9e243adbc29ff39158e9a4935769dae, exactly (1,1/2,1/8).
- [Native source_fit_bank](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/source_fit_bank.rs), SHA256 e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a, `heights`, `edge_expression`, `run` and the `g_<vertex-name>` variable bank. Source inspected, not executed here.

This fixture closes the hand-level missing realization for the proposed example. It does not execute the new 6–8-copy native bridge, create a general source recognizer, or alter the active integration packet.
