# The same actual age/tag/tree law survives an artificial ancestral read cut

Contributor: Codex, delegated G3/source-bridge lane, 7 October 2026. **New HAND CANDIDATE; separate deterministic Lean draft UNCHECKED.** The original clock recursion, full-past renewal and continuation theorems are attributed to Dot. This consumer changes no provider, physical clock, rate, boundary, register or genealogy. [SOURCE-INPUTS.json](SOURCE-INPUTS.json) pins the sources actually read. The already hand-accepted complete-calendar law and its new principal-law derivative remain unchanged.

The question is whether a demographic calendar that ends before the last observation cut can be extended analytically through its ancestral population without changing its completed age/bin/tree observation. Endpoint completion harmonicity alone does not establish this. The original source gives a stronger route: exact continuation of all active destinations and ages, and the joint law of the entire recorded past with the actual retained clocks.

## 1. Exact contract and readout

Use the original finite source graph `N`, admitted finite Copy carrier, positive original rate bank `r`, and actual source Code `s`. Codes retain every actual binary genealogy. Let `n` be a literal legal-merger budget, `o` the entering absolute offset, `B` the carried old tag matrix, and `b : ℝ → Tag` any function. Deterministic statements need no finiteness or measurability of Tag. Probabilistic statements below use finite Tag with its discrete measurable space and measurable b. A finite cut-bin map is one instance. For the stronger real-age version take `Tag=ℝ` and `b=id`; the original real-matrix measurability providers supply that version.

Let `h_t(c)=literalMarkedTrace N n t s c`. Its success flag remains part of the record; inactive padding remains in the padded vector. Let `A_t(c)=activeTrace N n t s c`, the original padded vector filtered by its active flag in its original order. No chronological sorting, binary contraction or equivalence of different endpoint topologies is performed. The original `recordEndpoint s A_t(c)` is the last active destination, or s when the list is empty.

Define the active-list tag fold `F_b(o,s,B,l)` recursively by

```text
F_b(o,s,B,[]) = B,
F_b(o,s,B,(true,a,d)::l)
  = F_b(o,d,tagUpdate(s,d,b(o+a),B),l).
```

Our total definition also reads a list element with a false flag as a list update; it is used only after the original `activeRecords` filter. The fold is algebra on a list, not a source-admission theorem for arbitrary fabricated records. Its physical claims below use only the original compiler's lists.

The joint source readout is the **full endpoint Code together with the carried tag matrix**. A tag matrix or final pair partition cannot replace Code: distinct binary genealogies may have identical tags. Cross-tree entries are bookkeeping. Physical pairs use the SAME Code's joined/absent test, and the same-tree decoder uses only that tree's own leaves; original sampling dates remain explicit on the diagonal. If physical interpretation is requested, the entering real matrix must satisfy the original `ForestDecorates` invariant. The present fold equalities themselves hold for every old B simultaneously.

## 2. Padding, concatenation and shift algebra

For every padded vector z, even a nonphysical one,

```text
foldTags(b,n,s,o,B,z) = F_b(o,s,B,activeRecords z).                 (1)
```

Induct on n. At an active head both sides update the same initial/destination Codes using `b(o+age)` and recurse on the tail. At an inactive head neither the original padded fold nor its filtered list writes a tag. The empty case is the unchanged B. This also identifies old real `foldMatrix` with `F_id` by the accepted `BinFold.map_actual_age_fold` quotient theorem.

Two list identities hold by induction in the original order:

```text
F_b(o,s,B,l++q)
  = F_b(o,recordEndpoint(s,l),F_b(o,s,B,l),q),                    (2)
F_b(o,s,B,map(shiftRecord t,l)) = F_b(o+t,s,B,l).                 (3)
```

In (2), the destination of each original record is carried to the next update; all old tags remain the accumulated B. In (3), associativity of real addition gives `o+(t+a)=(o+t)+a`; flags and destinations are unchanged. No equality of times, endpoint relations or generic merging of different trees is assumed.

## 3. Finite interval split from the actual retained residual

Assume `ClockRegular c`, `liveCard s ≤ n`, `t,v ≥ 0`, and the exact original residual identity

```text
literalCutResidual N n t s c = encodeResidual N d k.              (R)
```

The provider `residual_regular_and_card` derives regularity of k and `liveCard d ≤ liveCard s`. Original success at the sufficient budget, `cut_endpoint_eq_literal` and `literal_endpoint_of_success` give

```text
recordEndpoint(s,A_t(c)) = d.                                    (4)
```

The original **whole-record** theorem `same_clock_active_continuation` gives

```text
A_(t+v)(c) = A_t(c) ++ map(shiftRecord t,A_v(k)).                 (5)
```

Use (1)–(4) on (5). For every carried B and every b,

```text
foldTags(b,n,s,o,B,h_(t+v)(c).trace)
 = foldTags(b,n,d,o+t,
     foldTags(b,n,s,o,B,h_t(c).trace),h_v(k).trace).               (6)
```

The endpoint on the right is the SAME endpoint on the left, by (5), the original `actual_trace_endpoint_fold`, and (4). Thus the joint endpoint/tag reader agrees, not only its endpoint marginal. Taking b=id gives the exact same real-age matrix; mapping that equality through any fixed bin function is valid without an additional boundary-nullity theorem. This does not assert sufficient-budget continuation for an undersized n. The earlier all-prefix fold result still handles undersized/failed literal prefixes at its own scope.

## 4. Complete ancestral split at the SAME random covers

Now take `n=Fintype.card Copy`, fixed `t≥0`, regular c, and (R) at that budget. Write `C_s=clockCover N s c` and `C_d=clockCover N d k`. Set pathwise

```text
H=max(C_s,t+C_d),  v=H-t.
```

Both covers are nonnegative; hence `H≥C_s`, `v≥C_d≥0`, and `t+v=H`. Apply (5) at these t,v. The original `complete_ancestral_trace_stable` identifies `literalMarkedTrace(H,s,c)` with the SAME `completeAncestralTrace(s,c)`, and identifies the residual trace at v with the SAME `completeAncestralTrace(d,k)`. Therefore

```text
activeRecords(completeAncestralTrace(s,c).trace)
 = A_t(c) ++ map(shiftRecord t,
     activeRecords(completeAncestralTrace(d,k).trace)).           (7)
```

This equality preserves every actual destination and original age. H is a pathwise proof device, not a time substituted into a fixed-time kernel law. No fixed-horizon boundary avoidance is applied at a dependent random cover. Applying (1)–(4) gives

```text
(complete rawEnd(s,c), foldTags(b,n,s,o,B,complete(s,c).trace))
 = (complete rawEnd(d,k),
     foldTags(b,n,d,o+t,foldTags(b,n,s,o,B,h_t(c).trace),
       complete(d,k).trace)).                                  (8)
```

No ancestral-root hypothesis is needed for this deterministic record equality. That hypothesis is required when identifying completed endpoint weights with the original terminal completion kernel. Empty Copy and zero t are included through the inherited empty/sufficient-budget constructions; no default leaf, fabricated tree or ambient `Nonempty Copy` is introduced.

## 5. The actual correlated law, with no conditioning on success

Let `P_t=actualMarkedTraceLaw N r n s t` and `ν_d=completeAncestralTraceLaw N r d`, at full n. Let `e_s(h)=decodedEndpoint N n s h`. For a prefix h and complete residual record z define the measurable joint reader

```text
G_d(h,z) = (rawEnd_d(z),
  foldTags(b,n,d,o+t,foldTags(b,n,s,o,B,h.trace),z.trace)).
```

For finite Tag, raw endpoints, finite matrices and tag updates are measurable; only b applies to real recorded ages. The original joint padded-fold proof (`fold_tags_joint_measurable` in the separate unchecked principal-law derivative) and the direct finite recursion establish measurability of the two folds. Alternatively bin the original proven jointly measurable real fold when B comes from a real decorating matrix. Prefix h, encoded retained clocks, and complete residual compiler are measurable by their original providers. Dependence on finite Code is handled one original measurable clock fibre at a time. These facts give a measurable total successful-branch reader on `h × CutResidual`; its failure branch may return the supplied s,B. That choice has zero actual mass below and does not manufacture a physical source object.

The original proved `actual_full_past_terminal_fibres` states

```text
law(h_t(c),literalCutResidual(t,s,c))
 = Σ_d ((P_t | e_s(h)=some d) × currentPairClockMeasure(r,d))
          mapped by (h,k) ↦ (h,encodeResidual(d,k)).              (9)
```

Every prefix fibre is **unnormalized**. At full n, the original `actual_current_clock_regular_ae`, actual sufficient-budget success and the cut-endpoint identity imply that failure has zero measure. On that one regular-clock event, (8) holds simultaneously for every old B. Map (9) through the complete residual compiler and `G_d`, and use (8) on the original side. This yields the source-connected law

```text
(ν_s).map(z ↦ (rawEnd_s(z),foldTags(b,n,s,o,B,z.trace)))
 = Σ_d (((P_t | e_s(h)=some d) × ν_d).map G_d).                 (10)
```

The entire recorded prefix is retained by (9) until the final chosen reader. The same derivation gives the joint finite-interval law using the original future marked compiler at fixed v and (6). In particular the two halves are not replaced by independent unconditional rows: the residual clock product is attached to the actual terminal fibre of the entire marked past. A fresh product vector in that fibre is justified by the proved original renewal, rather than introduced as a desired law premise.

Both sides of (10) are probability measures: the left is a measurable map of the original complete probability, and equality transfers normalization to the right. On the finite Code×TagMatrix carrier the existing `Measure.toPMF` therefore gives the exact PMF with `toPMF_toMeasure`; merely writing `Measure.map` would not establish a PMF. For real ages the same statement is a probability-measure equality on the real-matrix carrier, with the original Borel measurability. This hand consumer introduces no arbitrary-real numerical oracle or finite table evaluation.

## 6. Insert the cut after an actual calendar, carrying its old correlation

Let `ops` be the unchanged actual finite demographic calendar, starting at offset o with physically decorating old real matrix M when physical interpretation is wanted. Its original law is `P=actualCalendarTraceLaw`, not an independently supplied Γ. For each original terminal fibre `d`, keep the SAME recorded past p and set its absolute tail offset `a=o+programDuration(ops)` and tags `B(p)=calendarTags(ops,s,o,b(M),p)`.

Apply (10) **for every B** within each actual `P|calendarEnd=d` fibre, with entering offset a. Form its product with that unchanged past fibre and sum over d. This proves equality of the complete joint reader for the original calendar and for that calendar followed by a fixed artificial interval t and its residual complete tail. The actual `actualCalendarTraceLaw` definition uses exactly products with unnormalized source-endpoint fibres; the final interval uses the original `actualSegmentLaw.interval`, which attaches the SAME raw endpoint to `P_t`. To identify the displayed two-stage product with the literal appended calendar, induct through `ops`: the empty calendar case is (10); for `op::ops`, keep the original segment record, its endpoint-fibre restriction and product measure, then apply the induction inside its original continuation fibre. Original boundaries retain the old matrix and advance only to their stored endpoint. No register is redrawn at the read cut. Finite sum/product/map associativity, and the already proved finite endpoint-fibre regrouping, identify the two recorded calendars under this joint reader. This is a hand derivation, not an existing named interval-insertion theorem or a compiler result.

Consequently, for every fixed nonnegative t,

```text
actual complete calendar joint age/tag/Code law(ops)
 = actual complete calendar joint age/tag/Code law(ops ++ [.interval t]). (11)
```

The interval on the right is an **analytical subdivision of the existing ancestral tail**, using the same positive ancestral rate and physical source bank. It does not introduce a biological vertex, move endpoint ages, alter rate registers or change any original boundary order. To assert actual terminal genealogy/complete-kernel semantics, require the original actual terminal support to be ancestral. Without that premise (11) is still an equality of the defined random-cover record readers, not a guarantee of ancestral biological completion.

For ancestral support after the inserted interval, unfold the original `sourceTimeKernel` count mixture. Membership in its PMF bind support supplies a count k and an endpoint in the SAME `sourceIteration(k,d)` support. The proved `SourceAncestralAbsorption.ancestral_iteration_support` gives `AncestralRoot` for that endpoint from ancestral d. Thus every new positive actual terminal fibre is ancestral. This argument covers t=0 and empty carriers and has no `Nonempty Copy` premise.

## 7. Discharge the last-cut gate at the source-law level

Fix the last observation cut T. If the actual demographic tail begins at a<T, set `t=Real.toNNReal(T-a)`; otherwise set t=0. Then `a+t≥T`. The refined actual calendar from (11) has the same completed real-age/tag/full-Code observation and retains its actual past correlation; its new tail offset satisfies the explicit last-cut premise of the independently hand-accepted complete-calendar principal law (A). Its root-support premise is preserved as above.

Therefore the principal finite completion/tag assembly can be applied to the **actual refined calendar** even when the original demographic calendar ended before T. The resulting Γ is computed mathematically as the actual refined endpoint/past-tag pushforward, with proved measurability and probability admission. It is not the old Γ with a silently substituted endpoint kernel. Tags of mergers between a and T remain in the actual inserted prefix; only mergers after the fixed last cut collapse to the common tail tag. This is the concrete timed-law-preserving extension previously missing from the hand source contract.

Physical old decoration follows the original `actual_literal_fold_decorates`, calendar/complete decoration providers and SAME endpoint/tree decoder: actual active mergers preserve the entering matrix and binary trees; boundaries merely transport that actual source state. This statement still needs the original decorating matrix and original chronological/sampling contract when a chronological observation is asserted. The last-cut derivation does not supply numerical Γ evaluation, backend equality, an effective arbitrary-real algorithm, a complete controlled/menu/pruning consumer, graph-template extraction or biological positive reconstruction. Original general G3 and the connected master G6 endpoint remain open.

## 8. Implementation boundary and next consumer

[ActualCutTagRefinement.lean](ActualCutTagRefinement.lean) provides one definition and nine concrete deterministic theorem bodies for (1)–(8), with actual source recursion/continuation/stability as imported proof inputs. It has no `sorry` or desired cut-law equality premise. **It is UNCHECKED**; named print requests are not compiler or axiom evidence. The probabilistic map of (9), literal whole-calendar identification (11), support transport and finite PMF conversion remain hand-only here. The original principal-law derivative has its own independent semantic review and future sole compiler slot. No compiler, simulation or provider edit ran in this lane.

The next formal consumer is to implement the measurable successful/failure reader and push (9) to (10), then the original calendar induction. These obligations are explicit proof terms to be written, rather than a structure assuming the refined joint law. Independent source-semantic hand review is requested for this exact note and deterministic draft before any implementation acceptance or promotion.
