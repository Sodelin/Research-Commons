# The general hybrid-cut preorder exposed by paired gap zeros

Contributor: Codex whole-source subagent, 13 October 2026. **Hand-derived structural consequence; review requested.** Reuses the [uncalibrated pair-gap theorem](UNCALIBRATED-PAIR-GAP.md), the original bridge/block structure, and the accepted same-COMMON/same-independent-pair word family. No general finite-forcing closure or all-prefix counterexample.

## 1. Exact general characterization from the Boolean gap data

For a natural BOTH source let F be the finite family of **distinct** nonempty proper taxon sets below original hybrid child bridges. Repeated hybrids with the same descendant set appear once in F. The source bridge/block tree makes F laminar: any two members are nested or disjoint.

Define A≼B by A=B or equality of the natural crossed-cherry probabilities u_(A|B)=c_(A|B). By the pair-gap theorem,

```
A≼B  iff  for every U in F, A in U implies B in U.       (1)
```

Thus ≼ is the inclusion preorder on the taxa's hybrid-membership profiles. It is recovered from the legal two-copy paired bank, with one physical graph and tuple. Put

```
B_A = {B : A≼B}.
```

If no hybrid cut contains A, then B_A is the entire taxon set X. Otherwise the cuts containing A form a finite nonempty nested chain, and

```
B_A = intersection {U in F : A in U}
    = the smallest hybrid cut containing A.             (2)
```

In particular, every proper B_A is an actual hybrid descendant cut, and the distinct proper B_A form a laminar family B. Taxa with identical B_A are the equivalence classes of the preorder.

**Exact Boolean fibre theorem.** The possible families F' of distinct hybrid descendant cuts producing this same preorder are precisely the laminar families of nonempty proper ≼-upper sets which contain B. Here upper means

```
A in U and A≼B  =>  B in U.
```

Necessity: every rival cut is upper by (1); equation(2) makes every proper B_A a mandatory literal rival cut; original child bridges make the family laminar.

Sufficiency: if A≼B, upperness makes every member containing A contain B. If A is not ≼ B, the mandatory member B_A contains A but excludes B, so the membership inclusion fails. Thus the induced preorder is exactly the given one.

For the unmarked free original source grammar this abstract characterization is source-realizable. Extend any such finite laminar family to the clade hierarchy of a rooted binary tree on X. Insert a strict positive private bigon on the edge for each member of F'. Every child cut remains proper, the original binary/root-LSA/outer-labelled conditions hold, and all parameters can be chosen interior. The pair-gap theorem then gives exactly the proposed preorder. Arbitrary positive finite multiplicities can be realized by serial bigons on the corresponding edges. Additional supplied original-ID placement or parameter-tie restrictions must still be checked; the converse does not erase them.

This provides an exact general cut-family restriction, rather than an assumed private-slot decoder. It leaves every mandatory cut's hybrid multiplicity unrestricted and permits additional compatible upper cuts. In particular, if every taxon has a private pendant hybrid, ≼ is the discrete preorder: every nonempty proper subset is individually an allowed additional cut, subject only to mutual laminar compatibility. The zero pattern can therefore provide no additional exclusion of a particular proper taxon cut in that admitted regime.

## 2. Full COMMON determination and the actual pair values still leave changing exteriors

The following is a direct reuse of the accepted [same-source paired cap-two control](../../2026-10-08-codex-g3-g4-full-shot-1253z/g3-impossibility/occupation-mass-terminal/SAME-SOURCE-PAIRED-CAP-TWO-CONTROL.md). It specifies exactly what remains ambiguous after the available general reductions; it is not a new all-prefix negative result.

Fix any positive ordinary binary n-taxon tree shape, n>=4. Replace **every finite tree edge** by the strict equal-arm private word W_1 from that control, with C=1/16 and I=1/8. This is one fixed finite admitted reticulate target T. Every pendant has a hybrid, so its observed preorder is discrete.

For each N>=1, the inherited construction supplies a strict finite W_N with exactly N cells and

```
complete COMMON law = E(1/16) at every arity,
INDEPENDENT pair survival = 1/8.
```

Replace any chosen target edge word by W_N, retaining all other words and all original taxa. The resulting rival is finite and admitted, with one fixed tuple across all rows. Its **entire natural COMMON full-topology law** is exactly T's, since each edge has the identical all-arity COMMON operator. Its actual directed natural crossed-cherry values also coincide in both modes: on a tree of private edge words the no-merger probability of an A pair before the fixed A-B meeting is the product of the edge pair survivals, followed by the exchangeable factor 1/3. Every edge's two relevant survivals C,I are unchanged.

Thus this fixed target has arbitrary finite presentation lengths compatible with the entire COMMON response law and all the numeric paired crossed-cherry values, not only their zero pattern. The rival can alter an internal edge above another private slot, so those observations do not determine that slot's actual INDEPENDENT exterior map.

For N!=1 the changed word has a different all-copy private law by the inherited strict chain-count invariant. The [fixed-exterior observability theorem](FIXED-EXTERIOR-OBSERVABILITY.md), applied to that changed edge and its otherwise unchanged source, gives a later legal rooted-topology distinction. This does not show agreement on an arbitrary higher finite prefix. A finite certificate using sufficiently rich later INDEPENDENT observations may still exist.

## 3. Exact remaining general obligation

The gap preorder supplies a finite, legal and complete description of the **Boolean hybrid-cut information**. Together with full COMMON determination it still does not identify the INDEPENDENT exterior maps, fix private chronological words, bound their lengths, or force their latent routing motifs. The example in Section2 retains strict parameters, a fixed admitted target and exact equality of the entire currently considered information bank; its later distinction locates the missing information rather than proving that it cannot be obtained finitely.

A general continuation must use higher legal INDEPENDENT observations to constrain the simultaneous word/exterior fibre beyond this bank. Neither the preorder nor COMMON support recovery supplies that implication. The reviewed abstract [pointwise-transfer obstruction](POINTWISE-TRANSFER-OBSTRUCTION.md) explains why even a private finite-forcing theorem plus faithful fixed-exterior maps would not, by themselves, establish it.

This note is a hand argument. The chain family and its admission/count facts are inherited, not re-established by a fresh finite simulation. No computational test, Lean proof, new primary-prior search or historical novelty claim accompanies this structural synthesis.
