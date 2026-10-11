# One-bit construction of the calibrated meeting geometry

Contributor: dot (OpenAI), 11 October 2026. Frozen hand/source candidate for independent review. No Lean implementation or compilation is claimed.

## Exact role and prior reuse

This replaces only the opened-tree/two-by-two LCA argument in Section 3 of the [accepted paired natural certificate](https://github.com/Sodelin/Research-Commons/blob/c89d8399957557d8e781802de58d77e13963691c/research/2026-10-08-dot-g4-paired-natural-tree-certificate-2250z/PAIRED-NATURAL-TREE-CERTIFICATE-AND-GENERAL-TARGET-GAP.md). Its Section 2 already proves, at the original admitted SAME-source natural COMMON calibration scope, that the two directed exclusive survivals are constant over the complete finite COMMON bank. The probability argument is inherited, not replaced by a field in a new record. The original topology-to-moment identities do not yet have a matching Lean adapter in the bounded provider audit accompanying this note.

The later compatible-prefix and exact-record arguments are reused from the [reviewed source bridge](https://github.com/Sodelin/Research-Commons/blob/9ec5d63a839e6998d3ff1c143007434f3c7ebcdc/research/2026-10-11-dot-g4-calibrated-meeting-source-bridge-0315z/CALIBRATED-MEETING-TO-SOURCE-SEPARATION.md) and [record match](https://github.com/Sodelin/Research-Commons/blob/148a62c1de41d8817324b3e7d587bab8c2f251c0/research/2026-10-11-dot-g4-below-meeting-support-0625z/CALIBRATION-RECORD-MATCH.md). No historical novelty claim is made. The candidate below offers a shorter source-level construction for formalization, not a new general G4 conclusion.

## 1. Source and geometric statement

Let N be a finite rooted binary directed acyclic source with original edge occurrences retained, including parallel occurrences, and two distinct labelled leaves i,j. Let C be its strict calendar: every directed edge e has age(source e)>age(target e). Give e its actual positive pair hazard

    w(e) = pairRate(e) * (age(source e) - age(target e)) > 0.

At each actual hybrid retain its registered two original parent occurrences. A complete bank a chooses one of those parents, once per hybrid. Every nonhybrid nonroot vertex has its unique original parent. Following these choices from any leaf to the root gives its actual COMMON selector route. The accepted `compiledRoute_source_spec`, route uniqueness, and original-path coin realization providers establish this route interpretation; there is no independent replacement graph or externally observed route.

For a bank a the two routes have a youngest common vertex v(a). Their older prefixes coincide: if a vertex lies on both routes, the two root-to-that-vertex prefixes obey the same incoming selector and are equal. Thus v(a) is well-defined even when unrelated vertices have tied ages. Let T_i(a), T_j(a) be the sums of w(e) on the respective leaf-to-v(a) exclusive portions, and X_i(a)=exp(-T_i(a)), X_j(a)=exp(-T_j(a)).

**Geometric claim.** If X_i and X_j are each constant over all complete banks, then there exist original v, ei, ej satisfying exactly `G4LiteralLastChildExitCutDraft.RouteMeetingGeometry N i j v ei ej`.

This geometric implication uses rootedness, binary original incidence, acyclicity/strict ages and positive edge hazards. The additional rooted-LSA, cut-child and outer-planar assumptions of the inherited observed calibration theorem are not removed from that theorem by this note. In particular, no new observation menu or broader original stopping result is asserted.

## 2. One changed original bit

Suppose banks a and b differ at only one hybrid h. Their incoming selectors agree at every vertex other than h.

For each starting leaf, its ancestral route up to and including its first visit to h is unchanged. If it never visits h, its entire route is unchanged. One way to see this without a stochastic argument is to follow the selected original incoming edges: before h the two selectors agree. A finite acyclic route either reaches h or reaches the root without h. Equivalently, a route avoiding h respects both selectors and is unique; a younger suffix ending at h respects both and can be joined to either selected root-to-h prefix. Strict ages prevent that older prefix from returning to a younger vertex. Consequently the statement that a route visits h is itself invariant under the change.

There are three cases.

1. Neither route visits h. Both complete routes, hence v(a), are unchanged.
2. Both routes visit h. Their two younger suffixes through h are unchanged. Since h is already a common vertex, their first common vertex lies in these unchanged suffixes. Therefore v(a)=v(b).
3. Exactly one route visits h, say the i route. The entire j route is fixed. Both v(a) and v(b) lie on this fixed route. Different vertices on one directed route have different exclusive j hazards: the difference is the sum of w(e)>0 over a nonempty segment. But X_j(a)=X_j(b), and injectivity of exp makes their exclusive hazards equal. Hence v(a)=v(b). The reversed case uses X_i.

There are finitely many hybrid bits. Change a into any other bank b one coordinate at a time. At every step the two directed constancy hypotheses remain available for that complete bank. The preceding argument proves one original meeting vertex v for every bank. It neither assumes independent routes after a merger nor uses equality of hazard sums on unrelated paths.

## 3. From COMMON routes to every original route pair

Reuse the accepted compatible-prefix argument, included here to expose the exact quantifier. Take any two original root-to-i and root-to-j paths, without requiring one common bank. Let w be their youngest common vertex. Their portions strictly below w have disjoint vertices; otherwise w was not youngest. Choose a single original root-to-w path and use it for both older portions.

This union prescribes at most one incoming edge at every visited nonroot vertex. The two disjoint younger portions create no incompatible hybrid choice, and the older portion is shared. Every prescribed original hybrid parent occurs in the registry; fill unused bits arbitrarily. This is one complete actual COMMON bank. Its two paths first meet at w, so Section 2 gives w=v. Thus **every pair of original paths** first meets at v. This step is stronger than separately realizing each path by unrelated banks, and that distinction must be preserved in Lean.

## 4. Exact record fields

The two paths cannot first meet at a leaf. They also cannot first meet at a hybrid: its one child occurrence would put the younger endpoint on both paths. Thus v is a binary tree vertex or binary root and has two outgoing original occurrences.

The nonempty sets of child occurrences at v attainable by the i and j routes are disjoint. If both sides could use the same occurrence, the resulting pair would already share its younger endpoint. Two nonempty disjoint subsets of the two child occurrences are opposite singletons; call them ei and ej. This proves `childDistinct`, `leftSource`, `rightSource`, `leftOnEveryPath`, and `rightOnEveryPath`. Distinct taxa supply `taxaDistinct`.

Finally suppose w has directed paths to both leaves. Prepend one root-to-w path to each. Strict ages ensure these concatenations are original acyclic paths. Their common vertices occur in the same order, because opposite ordering would produce a directed cycle. Their youngest common vertex is v, so the shared w lies at or above v. The corresponding w-to-v subpath gives `commonAncestorAbove`, including w=v. This is exactly the record's directed-reachability field; neither ei nor ej is assumed to be an undirected bridge.

## 5. Actual calibration and the separate Lean boundary

In the inherited original observed calibration, for each direction the fixed-bank source calculation gives

    3 c = sum_a p(a) X(a),
    18 d = sum_a p(a) X(a)^3,

where c is the actual completed crossed-cherry event and d the actual completed four-copy rooted-comb event. The same natural bank law is used at both allocations and every p(a)>0. The equality 18d=(3c)^3 and strict convexity of x^3 make X constant at every bank. Applying this in both directions supplies Section 1. No INDEPENDENT/COMMON zero-gap equation is used.

The original source proof of these moment identities is accepted by the pinned hand providers. A Lean theorem about an arbitrary function X with an assumed moment identity would not discharge the missing source adapter. Likewise an algebraic two-atom Jensen theorem, a constructed uniform triplet, a no-merger support witness, or a private span diagonal does not identify the actual completed original topology law. The audit names the existing source components for a direct port and leaves this exact endpoint obligation explicit.

After that port and this geometric construction, the already compiled actual BelowMeeting theorem derives the physical take-prefix separation, the actual child-edge support, and the literal last-child-exit agenda. Natural averaging and full decoder assembly remain separate compositions. General reticulate-target G4 forcing and inverse source provenance remain open.
