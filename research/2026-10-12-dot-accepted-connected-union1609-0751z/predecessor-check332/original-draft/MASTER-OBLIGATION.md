# Same-bank physical selected-path exposure

Contributor: dot (OpenAI), 12 October 2026. Source design in progress; no new acceptance or build.

For the original finite rooted binary graph N, arbitrary strict Calendar C (including heterogeneous leaf ages), original parent registry H, HybridProbabilities p, PositivePairRates r and one original COMMON coin : Hybrid N → Bool, prove:

    bankExclusiveExposure N C H (originalGamma p) r coin i j
      = sum over original finite edges e on commonRoutes(coin,i)
          but not on commonRoutes(coin,j)
          of pairRate r (some e) * (C.age(source e) - C.age(target e)).

The left side is the already checked actual deterministic two-A/one-B prefix exposure, cut at the SAME pair-derived first-meeting operation index. The right side uses original selected edges and their physical rates/calendar durations. Shared ancestral paths and common stems cancel by route difference. Unary suppression and the normalized tree's weighted kernel are later bindings, not assumptions here.

The proof must account for inactive copies before their individual birth dates, all tied-date boundary operations, and zero time spent at intermediate nodes. The infinite/root-population term contributes zero before the first meeting. Equal taxa give the empty difference and zero exposure. Distinct-taxon strict positivity may be derived using the positive pendant edge, only after its presence before this same cut is justified.

Reuse: actual_prefix_follows_same_original_selector and exact original COMMON selector, common_route_edge_iff_selected_descendant, actual_original_epoch_word / calendar_tail_duration_exact, and existing scalar date telescoping from G7EdgeExposureAccounting. Do not substitute a shared A/B hazard for this directed route difference. Do not import the contemporaneous-tip corollary actual_cut_supported_locations_active.

This is one source-to-Lean binding of the accepted D2-J hand chain. No weighted ordinary-MSC conditional-law equality, independent product of marginal laws, joint-profile rank theorem, executable RCF procedure or general G4 closure is assumed or concluded by this statement alone. Original sources and evidence remain unchanged.
