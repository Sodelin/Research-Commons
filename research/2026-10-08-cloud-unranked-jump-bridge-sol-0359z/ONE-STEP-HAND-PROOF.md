# Actual ordered source step to the decorated unordered reference row

Contributor: Cloud Sol `/root/source_backend_review_sol`. Capture: 8 October 2026, 03:59 UTC. **HAND/SOURCE DERIVED DRAFT; independent primary review PENDING. No new compiler/runtime verification.** This is one original uniformized holding-or-merger step with fixed normalization. Physical clock/history identification, complete backend iteration, table extraction and full G6 remain separate.

This follows the [returned-count contract](../2026-10-08-cloud-returned-residual-contract-sol-0327z/HAND-CONTRACT-SOUNDNESS.md), not an independent self-review of that authored proof. The concrete target is the unchanged [Python source_step](../2026-10-07-astra-g6-source-poisson-prefix-124833z/finite_source_prefix.py), SHA `f54e18f2f1a09c836c4905fa936956d935929b3300248fc31f87a97ca86ae0cf`. [Eighteen exact source pins/read depths](SOURCE-PINS.json) retain original source/graft/tag APIs. Fourteen identities match the saved166 module manifest; that observation does not compile this new hand argument or re-audit an inherited build.

## 1. Original primitive data and encoding

Fix the unchanged finite original graph `N`, sample map, nonempty finite original Copy carrier, positive rate bank `r`, and admitted `s:Code N sample`. Put `M=card Copy>=1`, and write `rho_i=pairRate r i` for every `i:Option E`, including the original ancestral population at `none`. Require each `rho_i` to have an exact positive rational representation. This is the initial rational-bank case, not access to arbitrary hidden real rates.

The only wire encoding data are injective maps from original Copy labels, original `Option E` population IDs, and original V register IDs into ordinary strings. Generate the Python rate list from **every** `Option E` index, with its exact rational rate and encoded population key; generate the register list from every original vertex and its current stored Bool. Construct `SourceParameters` with this complete rate list and `copy_cap=M`. The nonempty rate-list requirement follows from the ancestral index; key uniqueness follows from injection. No probability-row equality is an input field.

Both normalizers are now exactly

`Lambda=(1+sum_i rho_i)*(1+M^2)`.

The sum-index bijection and rational casts give this identity from the actual `globalRateBound` definition. The current number of live roots or currently encoded physical leaves does not replace `M`. The original leaf labels are immutable original Copy IDs, not taxa labels and not the current surviving representative.

Use a natural graft tag `tau`, represented as an ordinary nonnegative Python integer. At each internal node retain its tag and full binary structure. For a current tag matrix `H:Copy×Copy->Nat`, let `T_l=decodedTaggedTree H ((state s).genealogy l)` for each live root. This is the existing `FiniteTagDecoder` on the supplied actual genealogy, not topology reconstruction from tag values.

Define `C(T)` recursively as the corresponding Python `Leaf`/`Join`: encode each original leaf label; at a graft use the existing Python `graft(C(left),C(right),tag)`. Thus children are canonicalized recursively by their ordinary constructor `repr` order. Only child swaps are removed. No associativity, leaf contraction, equal-tag-node contraction or relabelling is allowed.

For ordinary well-typed finite `Leaf(label:str)` and `Join(bin_tag:int,left,right)` values, this representation is unambiguous: constructor names/field names distinguish cases, quoted string representations preserve strings, and recursive constructor syntax preserves the tree and integer tags. Hence different such objects cannot share a `repr`; ties in child sorting occur only for equal objects. In particular `graft(A,B,tau)=graft(B,A,tau)`. This is a hand statement about the preserved ordinary Python constructors, not a byte-level runtime or serializer verification.

Structural induction proves that `C` respects the existing `TaggedEquiv` relation: reflexivity/symmetry/transitivity are immediate, graft congruence uses the two induction hypotheses, and the swap constructor uses the symmetric sorted pair. Conversely canonicalization only recursively swaps children, so equal canonical trees represent the same tagged child-swap class. Immutable leaf injection preserves their exact labelled leaf sets. Repeated tags keep every separate binary graft.

## 2. Concrete whole-forest readout, including nonphysical locations

For each original population `i`, let

`L_i={l in s.live : s.location(l)=originalPlace N i}`.

Make its Python forest from the trees `C(T_l)` for `l in L_i`, using the original encoded population key. Omit empty population entries exactly as `SourceState.make` does. Attach the encoded **same total original register**, including every outside/protected register coordinate.

Retain all live components at locations outside the range of `originalPlace N` in a separate outside forest payload `B(s,H)`. Group their canonical tagged trees into an unordered forest at each original tagged Location, forgetting current representative IDs there as well. This keeps all original node forests instead of making them eligible Python populations. Let

`Phi(s,H)=(B(s,H), F(s,H))`,

where `F` is the canonical Python physical-population/register state.

Actual `Valid` fibres imply that every live tree is nonempty, distinct live trees have disjoint original Copy leaf sets, and all original copies are covered. Injective leaf encoding preserves these facts. Therefore roots map injectively to encoded component trees, the physical Python leaf count is at most `M`, and `F` passes the existing disjoint-leaf/unique-key validation. A physical pair list is in bijection with its corresponding unordered live-root pairs. Outside components account for any other copies and remain in `Phi`.

This construction works for arbitrary admitted Code with node components. If an actual calendar phase/support theorem establishes that every live component is in an original edge or the ancestral population, `B` is empty and the conclusion below concerns the literal complete Python state. That phase implication must be derived from the actual agenda/support theorem; it is not inferred from a register erasure or from row normalization here.

## 3. Destination-derived tag update and the two orientations

For an actual destination `d`, use the unchanged deterministic API

`H_d=BinHistory.tagUpdate N s d tau H`.

Define the original source row's readout as `d -> Phi(d,H_d)`. The probability law being transported is exactly `(sourceStep N r s).map` of that constructed function. Its `sourceStep` is the existing `choicePMF.map stepDestination`; no new stochastic law is assumed.

**Hand lemma D1: a legal ordered merger updates exactly the two cross blocks.** For an original ordered choice `(i,a,b)`, `a!=b`, both roots are in `L_i`. The actual population-pair lemma gives `LegalMerge`; `stepDestination` is the actual merge followed by admitted snapshot coding. Original `merge_new_pair_iff` identifies the tag-update condition as

`(ancestor(x)=a and ancestor(y)=b) or (ancestor(x)=b and ancestor(y)=a)`.

Thus `H_d(x,y)=tau` on exactly those two cross-operand blocks and is `H(x,y)` elsewhere. Snapshot coding preserves the actual ancestor map and every live genealogy, population and register needed for this calculation. This is the tag version of the existing `coded_update_is_actual_graft`/`map_coded_age_update`; it follows directly from their unchanged condition. Reversing `(a,b)` exchanges the two disjuncts, so it gives the **same** updated tag matrix. QED.

**Hand lemma D2: the actual decorated destination is the canonical graft of the complete old trees.** For every old live component `l`, all leaf pairs within its old genealogy have the same old ancestor `l` by actual `Valid.leaf_fiber`. D1 therefore leaves the entire matrix restriction on that genealogy unchanged. Every recursive witness used by `decodeTags` is a genuine leaf of its supplied subtree (`witness_mem`), so its old tagged tree is unchanged. At the new root, a witness from the a-tree and a witness from the b-tree trigger D1, assigning `tau`. Consequently the surviving new tree decodes as

`TaggedTree.graft tau T_a T_b` for `(a,b)`,

and as `TaggedTree.graft tau T_b T_a` for `(b,a)`.

Their equivalence is precisely `FiniteTagDecoder.TaggedEquiv.swap`, keeping `tau`, all immutable original labels and both complete old subtrees. Canonical `C` sends them to the same Python `graft(C(T_a),C(T_b),tau)`.

Both destinations remove those two component trees from their original physical population and add that one graft there. Every other physical component, every outside nonphysical component, and the total register is unchanged. Thus

`Phi(d_ab,H_dab)=Phi(d_ba,H_dba)`

equals the actual Python destination for that unordered pair, with outside payload `B(s,H)` retained. This is derived from the original merge definition; no destination-equality field is supplied. QED.

The actual raw Code destinations need not agree: merging two singleton roots as `(a,b)` keeps live representative a and ancestor a for both leaves, whereas `(b,a)` keeps b and ancestor b. Their internal ordered genealogies also swap. The quotient forgets current representative/survivor IDs, while retaining immutable original leaf labels, physical populations, all earlier tagged binary subtrees and the register.

For holding, `stepDestination none=s` and actual `tag_update_self` gives `H_s=H`; therefore the whole readout remains `Phi(s,H)` and no graft/tag is manufactured.

## 4. Exact one-step pushforward theorem

**Hand theorem J1.** With the primitive encodings, positive rational bank and `copy_cap=card Copy>=1` above, the real-coordinate pushforward of the actual original uniformized source row under `d -> Phi(d,tagUpdate N s d tau H)` equals

`point_mass(B(s,H)) × source_step(parameters,F(s,H),tau)`.

The right side is the actual reference function's unordered-pair row, with its required holding mass at the unchanged input state. The separate returned-count residual at iteration zero remains governed by the prior count contract.

Proof. Expand the actual source step as its finite holding-or-ordered-choice PMF followed by its actual destination map. For population i, actual `Choice` enumerates all ordered off-diagonal pairs from `L_i`. Swapping `(a,b)` with `(b,a)` is a free involution: fixed points would give `a=b`, which off-diagonal membership excludes. Its orbits are precisely the unordered two-root subsets. The injective component-tree encoding puts these orbits in bijection with the actual Python `combinations(range(len(ts)),2)` loop for that same encoded population.

Each orientation has actual real mass

`(rho_i/2)/Lambda=rho_i/(2Lambda)`.

D2 makes their readout destinations identical. Summing the two orientation masses gives `rho_i/Lambda`, exactly the reference's `mass=rates[p]/parameters.global_bound`. No orientation is discarded and no extra fair-coin factor remains in the quotient.

The total actual merger mass is

`J=sum_i |L_i|*(|L_i|-1)*rho_i/(2Lambda)`

`=sum_i binomial(|L_i|,2)*rho_i/Lambda`,

exactly the reference `jump_mass`. Thus the original holding mass `1-totalRate/Lambda` is `1-J`, equal to `out[state] += 1-jump_mass`. Holding preserves all fields as just proved. Finite dictionary accumulation on both sides adds any coinciding destinations; deleting zero dictionary entries changes no coefficient. Original choice normalization/nonnegativity already prove a probability row. All arithmetic agrees by exact rational representation and the fixed normalizer identity. This proves every output coefficient, including the outside payload, and hence the pushforward law. QED.

The theorem includes empty eligible-pair sets, populations with zero/one live root, and terminal physical forests: both rows hold with mass one, without dividing by total merger rate. It proves a uniformized holding-or-merger row. If one conditions that row on a genuine merger with positive merger mass, the same grouping also identifies the conditional unordered event row. It does not by itself identify an exponential winner/time/reset law.

## 5. Reused actual source lemmas and the tag scope

| Existing API | Role and limit |
|---|---|
| `SourceCopyCarrierTransport.mapLabels`, leaves/injectivity | Preserve the **original** labelled leaf carrier. This is not a survivor-ID quotient or permission to change the source's copy cap. |
| `G1OpaqueSourceGrafting.graftInput_unordered` and `actual_opaque_merger_grafting` | Carry every complete entering subtree through the actual merger and its child-swap quotient. Only the deterministic graft relation is reused here; do not replace original Copy by a current-root token carrier when computing Lambda. |
| Original `populationRoots` and `population_pair_is_source_legal` | Derive the actual eligible ordered pairs and legal merge from physical population membership. |
| `G2SourceGraftDecoration.merge_new_pair_iff`, coded graft and snapshot preservation | Derive the cross-descendant update and preserve full earlier decorations from the actual old/destination state. |
| `FiniteTagDecoder.TaggedEquiv.swap`, actual decoder | Quotient only tagged child order, preserving every graft, tag and original label. An arbitrary symmetric matrix is not promoted to a full actual nested-decoration theorem. |
| `BinHistory.tagUpdate`, `tag_update_self`; `BinFold.map_actual_age_fold` | Use the exact destination-only tag update and ensure holding writes nothing. If old matrices are actual age-fold coarsenings, preserve their intended actual decorated trees. |
| `BinFold.bin_constant_active_fold` | Fixed tau can represent an actual bin only after the actual active-clock records are proved to lie in that bin. This deterministic condition is not a source-law or chronology premise supplied by J1. |

D1–D2 are local algebraic identities even for an arbitrary supplied tag matrix, because old within-component queries are unchanged and every new cross query receives the same tau. To call the entering trees the actual clock-decorated trees, retain their actual matrix/decoration provenance. The already proved real `ForestDecorates`, actual graft decoration and `FiniteTagDecoder.decodedTaggedTree_actual` supply that deterministic interpretation when their real-age data are supplied from the actual fold. This note does not assert that any symmetric matrix or arbitrary active record is an actual history.

## 6. Remaining implications and evidence boundary

This gives a concrete one-step quotient construction from original source definitions rather than a false deterministic raw Code decoder or a desired row-equality assumption. The following remain open:

- Encode and extract the actual finite primitive/source tables and implement or formally verify the source/wire decoder. The hand interpretation of ordinary Python constructors is not a compiler or CPython semantics proof.
- Derive the required actual physical after-node phase when a complete Python state without outside payload is desired; preserve endpoint/tie conventions and all outside source forests.
- Carry this quotient through actual initialized iteration/calendar boundaries and the one joint readout. Register preservation in one merger is not independence after arbitrary observed-history conditioning.
- Identify actual active-clock/bin data, chronological paths and full bin-history laws. A fixed new tag or sourceStep holding count is not automatically a physical timed observation.
- Compare an upper copy cap or different rate/normalizer. Changing cap changes both discrete row and Poisson mean; J1 fixes exactly the original M and entire bank.
- Address arbitrary-real source admission, complete source/state enumeration, shared feasible parameter witnesses, effective outer assembly and full G6.

The exact Python `SourceParameters` rejects `copy_cap=0`. Hence its literal domain does not cover the original empty Copy carrier with the same cap/normalizer. The original empty source can have a mathematical holding row; this is a separately exposed backend-domain boundary, not repaired by silently choosing a different cap.

No Lean source body, compiler, Python/Fraction evaluation, solver/numerical/native experiment, Actions/workflow, API/SDK or private product work occurred. Original providers, previous packets and frozen176 inputs are unchanged. Repository preservation establishes this pending-review hand argument's identity, not independent or formal acceptance.
