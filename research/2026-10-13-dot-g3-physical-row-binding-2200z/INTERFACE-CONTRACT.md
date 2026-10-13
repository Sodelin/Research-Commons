# Same-source physical binding for the padded COMMON row

Author: dot. 13 October 2026, 22:02 UTC. Static source audit and proposed integration contract. No native or Lean execution was performed. This is an interface obligation, not a newly proved refinement theorem.

## Finding

The existing encoders already fix the external row, and the Lean provider already fixes its mathematical meaning. The missing connection is an authenticated same-source map from original occurrences and physical parameters to the native **rooted, labelled, full-joint** table, followed by the existing passive pruning and specified-comb event. Neither a fit-bank result nor a table summing to one supplies this connection.

The smallest useful test is the existing four-taxon fixture at levels 1, 2, 3, requiring respectively 6, 7, 8 distinct copies. Six copies alone reaches the constant normalized moment at level 1. This contract does not authorize a profile change or another compiler.

## 1. Fixed input and admission record

Fix one actual source N, calendar C, ordered original-parent registry H, strictly positive edge/ancestral pair rates r, and strictly interior original inheritance probabilities p. Fix the external taxa and protected edge/hybrid IDs, a complete configuration list with exact nonnegative masses summing to one, and its original-ID masks. These data precede every pair and level. All rows refer to this same record; no level-specific fitted source or probability bank is permitted.

Separate the following maps, and check their domains and injectivity rather than identifying equal strings across namespaces:

* vertex enumeration v: native vertices ↔ original V, preserving root;
* edge-occurrence enumeration e: native edge slots ↔ original E, preserving both endpoints;
* taxon enumeration t: native leaf slots ↔ original X, commuting with the leaf embedding;
* hybrid enumeration h: native hybrid slots ↔ original Hybrid N;
* protected-edge and protected-hybrid label injections into these same original occurrences;
* each row's copy enumeration c into the native sample positions, described below.

Require e(incoming[h,0]) = H.parent(h,false) and e(incoming[h,1]) = H.parent(h,true), with notation adapted to the selected registry API. Two edges with equal endpoints remain distinct. The native fit provider enforces inherited edge-order and hybrid-name ordering; do not silently reorder its parents to make an incompatible registry pass. A deliberate renumbering needs its own complete commuting map, including masks, parameters and readout.

Structural parser acceptance is only native-domain validation. Attach the actual RootedBinary/Calendar/registry witnesses and any CutChild, outer-labelled, protected-coordinate or other admission hypotheses required by the downstream physical provider. A generic native Source.validate success is not evidence for all those hypotheses. Nonempty protected parameter_constraints are currently refused by common_packet, so this version cannot quietly drop them.

## 2. Parameter and forcing convention

For each original edge occurrence define x_e = exp(-r_e * (C.age(source e)-C.age(target e))). Strict duration and rate give 0<x_e<1. The formal native LAW edge coordinate must be exactly this x_e, not an independent variable with an arbitrary convenient value.

For hybrid h, let Gamma_h denote the original probability of bit 1. LAW's G_h weights incoming[0], so G_h = 1-Gamma_h. The selected source_fit_bank already performs this complement and preserves the original incoming array. Reuse it where its domain applies; do not implement another convention converter.

Forced **bits** are not complemented: mask 0 means the original incoming[0] occurrence, and mask 1 means incoming[1]. For evaluating the existing COMMON routing polynomial, the corresponding G-coordinate is 1 for forced 0, 0 for forced 1, and 1-Gamma_h for natural/null. Endpoint substitutions here encode deterministic control; they do not make the original physical inheritance tuple non-interior. The existing forced_parent method returns incoming[bit] directly and documents this distinction.

Important limitation: source_fit_bank::bind derives a height calendar from fitted whole-edge survivals. Its result is not literal authentication of a separately supplied C,r. Either (a) preserve supplied C,r and prove the x_e identity directly, or (b) invoke the accepted COMMON exposure-invariance result with explicit identical whole-edge exposures and all its hypotheses. Path (b) cannot silently preserve protected raw rates/dates. Its rational_calendar_request deliberately rejects logarithmic rates; no rounding into that DTO is allowed. Algebraic descriptors outside the selected binder's supported arithmetic remain unsupported.

## 3. Exact tagged-copy map

For level k>0 and pair (i,j), the Lean carrier is ((Fin k ⊕ Unit) ⊕ X). Reuse external_encoding.fixed_queries:

* selected:A(q+1) ↔ inl(inl q), sampled at i;
* selected:B ↔ inl(inr ()), sampled at j;
* baseline:x ↔ inr x, sampled at x.

Compose these tags with an explicit bijection to native sample indices. There are n+k+1 copies even if i=j. All n baseline copies enter the full forward computation. Keep only the selected k+1 copies in the passive output map; the baseline copies must not be removed before evolution. Native sample slots identify copies, not taxa: multiple slots can map to one taxon without being merged as labels.

The retained event is the singleton rooted unranked forest containing the left fold comb(B,[A1,...,Ak]): first cherry (B,A1), then graft A2, and so forth. The source comb is literally a foldl. Erase child orientation, not the root or copy labels. Native law.rs exposes both rooted and unrooted tables: use rooted. Its unrooted split table loses information needed for this event. A string comparison without the label map and orientation quotient is insufficient.

## 4. One complete configuration draw

Let ν be the supplied PMF on whole configuration records. Construct OriginalMask on every original hybrid: the protected injection supplies its null/0/1 value and all unprotected sites are natural. Preserve original configuration IDs and zero-mass records in the request ledger. A derived complete-mask distribution may combine equal masks or omit zero mass only with an exact pushforward equality; no renormalization or coordinate-marginal product is allowed.

The mathematical row draws cfg~ν once and an independent original natural COMMON bank once, then applies that complete cfg mask to the same source realization. Reusing the same configuration law across levels means equality of the row experiment, not coupling separate observed queries or supplying cross-row counterfactual data.

For the existing native COMMON full table P_k(T;x,G), the proposed evaluator is

    W_k(T) = sum_cfg ν(cfg) * P_k(T; x, G^cfg).

This is one sum over complete configurations. Polynomial endpoint substitution at all forced sites must be justified against overrideCoin semantics. Natural COMMON routing must match one stored bit per original hybrid; independent current-root routing is outside this contract. No individual cfg table is treated as an additional observed query.

## 5. The exact commuting equality

Let D_c map a native rooted terminal tree to its singleton Lean unranked forest using the copy bijection. Let K_k be paddedKeep and E_k the singleton comb event above. The required source-law bridge is

    (D_c)_* W_k = randomizedFullForestLaw N C H p r ν masks (paddedSample k i j).

This equality must be obtained from the selected native compiler's full-joint correctness and the maps/physical-coordinate identities above. It is presently an obligation, not a field that may be asserted by a fixture provider or inferred from a hash.

The observable consequence is

    sum_{T : pruneForest K_k (D_c T) = E_k} W_k(T)
      = c_k * randomizedLegalCombMoment N C H p r ν masks i j k,
    c_k = 2^k / ((k+1)! k!).

The selected Lean definition proves which event and division are intended, and combCoefficient_pos supplies c_k>0. A native readout implementation needs its own commuting proof with pruneForest, including suppression of single-child nodes after removing leaves and quotienting child orientation. Reuse existing decoders/pruning helpers where present; this document does not introduce a replacement.

Finally compare the normalized native value with the *supplied* moments[k]. The readout's required_event_probability is merely c_k times that supplied number, not an independent source check. Only after the equality is proved/checked for every required level may actual_rows_certificate_annihilates consume rows. The new wrapper's own elaboration/axiom evidence is separately pending at the reviewed source cutoff.

For the first concrete demonstration, a universal native full-PMF refinement is stronger than necessary: checked proofs of its three particular actual Lean event equalities can discharge the rows premises directly, alongside the independently tested native computation. Record which evidence is supplied. Native equality to three rational numbers alone does not prove those Lean premises; a compiled support wrapper still assumes rows. A fixture with only the tested native correspondence must retain that conditional status. The full-PMF equality above remains the reusable general integration target.

## 6. Named tests and proof obligations

These are specifications for the existing test owner, not claims of new execution:

1. TAGGED_PADDED_BIJECTION: n+k+1 distinct labels, sample commuting, exact keep set; fail if any baseline copy is pruned before the full law. Include i=j and equal text in distinct ID namespaces.
2. PARENT_ZERO_COMPLEMENT: asymmetric Gamma (e.g. 2/3), natural G=1/3; force0 routes incoming0 and force1 incoming1. Complementing a forced bit must fail. Use unequal-arm survivals with an observable branch difference: the primary equal-arm bigon fixture cannot detect this error from its output probabilities alone. Its occurrence-map assertions remain necessary but are not that asymmetric control.
3. PARALLEL_OCCURRENCE_SEPARATION: identical endpoints with unequal edge survivals remain separate slots; endpoint-only maps and unannounced parent swaps must fail.
4. SHARED_TUPLE_ACROSS_LEVELS: one source/parameter/PMF identity across k; changing an edge survival or Gamma on just one row invalidates binding.
5. JOINT_MASK_CORRELATION: use two correlated sites with asymmetric branch responses; exact whole-mask averaging must agree with its input and distinguish a product-of-marginals mutation. Include zero mass and null versus forced masks.
6. ROOTED_PRUNED_COMB: evaluate the specified labelled comb from rooted full tables, compare orientation-equivalent encodings, and reject use of unrooted split signatures or a union of different cherries.
7. NORMALIZATION_123: coefficients c1=1,c2=1/3,c3=1/18. The proposed a=1/2 fixture has normalized (1,1/2,1/8) and raw (1,1/6,1/144). This checks event direction/scale, not hybrid convention coverage. The generic L=3 support wrapper concludes cardinality at most 2. The fixture's singleton support, or the sharper bound at most 1 from the explicit polynomial (x-1/2)^2(x+1), requires a separate root-identification corollary on the positive survival domain. It is not the generic wrapper's conclusion.
8. PHYSICAL_EXPOSURE_BINDING: verify every x_e identity from the same positive C,r; a changed protected raw rate/date cannot pass solely by matching exposures unless its explicit predicate is invariant.
9. REQUEST_AND_PROFILE_BINDING: bind exact request bytes, semantic maps, source hashes, selected profile and full output to the receipt. Oversized/unsupported work returns UNKNOWN; partial tables or a correct total mass are insufficient.

General obligations remain A: actual physical admission; B: native full-joint compiler refinement under original occurrence/coordinate maps; C: joint-mask substitution; D: copy/pruning/event transport; E: exact arithmetic and normalization; F: executable result/request and profile binding. Finite tests can falsify defects and authenticate a particular replay. They do not establish A–F universally, source acquisition, complete NO, or general G3.

## Sources and reuse

Immutable audit cutoff: fb0c09628c33798e332ef3ff35992fa8ad2c5b04 in Sodelin/Research-Commons. See SOURCE-LEDGER.json for individual bodies and Git blobs.

* research/2026-10-13-astra-native-common-compatibility-2106z/README.md and compatibility.py: report explicitly UNBOUND, four-copy selected native profile.
* research/2026-10-13-astra-unified-solver-0645z/external_encoding.py: existing tags, complete configuration table, event fold and exact normalization.
* research/2026-10-13-astra-legal-row-support-2115z/lean/Astra/ActualLegalRowSupport.lean: same-source universal realizer and rows premise; no parser/refinement claim.
* research/2026-10-13-dot-informative-row-review-2149z/README.md: reviewed informative 7/8-copy milestone.
* Native source revision 4e556c4ae6225d18fabf30bc7d3347a468749ebc: law.rs (routing lines 126–143, validation 223–230, rooted/unrooted output 307–319); source_fit_bank.rs (forced_parent 173–176, inherited order 224–227, height/edge/Gamma construction 397–412, explicit non-verification flags in canonical_response).
* Selected original G4WholeProfileDetermination source fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09: randomizedLegalCombMoment and actual_randomized_legal_moment; G4ActualLegalPanelComb: paddedSample/paddedKeep/paddedA/paddedB. These existing definitions are the receiver, not new mathematics proposed here.
