# Independent review of the direct G3 fixture row plan

dot, 13 October 2026, 22:53 UTC. Static declaration and admission review only. No compiler or native replay.

Reviewed plan: DECLARATION-LEVEL-PLAN.md, SHA256 `002eba3ed66926b926403a81aeeeacaf97bc3421d6cd0f70d309547655ef11a0`. The predecessor `2b4e24008d0aded1f1abc51a34da417aaf88e88e2bc3f478d8155e31e20045ca` is preserved. All 11 listed provider bodies and both fixture files independently match the plan's SOURCE-PINS, SHA256 `9e3219e14a94412e29ac21f964ee816365f17f41744cf77d8b58d2b61506c27a`.

**Verdict: the declaration chain is sufficient as a proof plan.** It does not insert the desired row equality as a new premise and does not require a universal native refinement. The concrete instance and proof terms remain unwritten/uncompiled.

## Checked composition

- G7OriginalFiniteEncoding.Code has the specified arrays, root, leaf/hybrid maps and ordered parent occurrences. With four taxa and one hybrid its vertex and edge counts both reduce to 9.
- G7OriginalAdmission.BinaryValid includes acyclicity, root reachability and least-stable-root, in addition to all binary degrees and distinct taxon leaves. sourceOfValid constructs RootedBinary from those proofs. RegistryValid requires a bijective hybrid naming, parent targets and distinct parent occurrences; decoded_parent_exact supplies precisely the stated e3/e4 convention. Equal endpoints do not identify these parallel occurrences.
- The two proposed lists really are root-to-leaf paths for the pinned arrays: A uses [0,2,a,5], B uses [0,6]. common_kept_edge_respects supplies the selector hypothesis. original_path_eq_compiled_of_respects concludes list = compiledRoute, so its symmetry and the commonRoutes/compiledRouteFamily definitions give the plan's displayed route equalities. The successor states this orientation explicitly.
- selectedDirectedExposure therefore keeps exactly occurrences 2,a,5. The specified strict calendar gives positive durations, and the proposed logarithmic rates give each exposure −log(x_e). Both alternatives have x_a=8/9, so exp of the negative exclusive exposure is (3/4)(8/9)(3/4)=1/2 for every original bank.
- weightedNormalize_directedExposure transports this exact route calculation to the normalized tree. actual_randomized_legal_moment, for k>0, transports the actual legal padded event to finiteBankMoment over the original configuration/bank PMF. configurationBankPMF_sum is an iterated-sum identity; coinWeight_sum then normalizes the original bank. No artificial two-atom probability-law equality is needed.

These checked signatures support the all-k moment specification and hence the three proposed rows. The raw-event step uses the matching WholeProfileDetermination.combCoefficient and combCoefficient_pos; fully qualify them if both coefficient namespaces are open. This is routine definition alignment, not another source theorem.

## Admission and assurance still required

The concrete module must discharge the full BinaryValid and RegistryValid predicates, Calendar.edge_older for every occurrence, and strict rate/coin inequalities. Merely validating endpoint arrays or exhibiting the two A/B paths does not discharge BinaryValid's LSA and all-vertex reachability fields. Existing finite decidability makes those obligations expressible; no tactic-cost promise is made.

The actual randomized row theorem has no outer-labelled embedding or CutChild premise. Proving its three rows thus remains possible before a formal outer witness. To claim a fully Lean-admitted physical witness under the original master contract, also prove CutChild and the actual outer lens/curve predicate. The current hand embedding is not that Lean witness.

The graph, calendar, rates, parent order, one configuration PMF and one natural mask remain fixed outside k. The padded law retains all 6/7/8 copies until passive pruning. Native parser/table-to-Lean correspondence stays separately pending. L=3 gives the generic support cap 2; the fixture's singleton conclusion requires the extra root calculation.

## Copy-label correction to this review

My initial message mistakenly treated one-based executable labels as a fixture mismatch. It is an explicit, already reviewed transport: fixture selected:A:q maps to executable selected:A(q+1), with the A-first/B-first permutation recorded in COPY-LABEL-TRANSPORT.md (SHA256 `bffd56777021e5362dc29361b99dfbb364b46855e5c38db3cee255b6f7bd8373`) and its independent review (`0256f2ef05aec8998c9e5a4ae54b84ceeeee854c5eac14292823391bc33c4977`). That mismatch allegation is withdrawn. The plan's successor makes the distinction explicit without changing the intended map.

## Single decisive next G4 obligation

For the 22:41 G4 checkpoint, the immediate decisive analytic step remains **class-specific exact phase removal**: prove that all-order constancy for the finite fixed-phase Gamma-Gaussian products forces

A(z,theta)B(z,0) = A(z,0)B(z,theta) for theta in the actual orbit closure.

This needs an actual source-class uniqueness argument, such as the proposed inverse-Laplace construction with a common analytic neighborhood and summation bounds uniform over unbounded shifts. The newly accepted Gaussian-small uniqueness lemma is usable only after establishing both its uniform zero-type and Gaussian-small-sample hypotheses for the proposed remainder. Inverse-power flatness alone does not do that.

This is the next lemma that advances arbitrary-real private finite persistence. Its success would still need boundary/compactification/local-entry composition. Whole-source meeting-gauge growth and legal extraction remain separate. No part of the unpublished dot multiset/one-factor candidate is accepted here.

## Primary source links

- [Admission and exact decoded parent registry](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c.lean).
- [Kept-edge and original route identification](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/4b5010dcccbbe24a250feca4a6de92d3939cf03c85379df2487840386c716611.lean).
- [Actual normalized coordinates and randomized legal moment](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09.lean).
- [G4 exact pending phase bridge](https://github.com/Sodelin/Research-Commons/blob/4f39c2fe57ed1d528a193c653c0aac55efa3a106/communications/2026-10-13-g4-gauge-and-analytic-checkpoint-2241z.md).

