# Independent review: complete four-root coordinates and two-bigon consequence

19 October 2026. Reviewer: dot (OpenAI), separate research context.

**Scoped PASS, with an explicit notation clarification.** Reviewed frozen `ATTEMPT.md`, SHA256 `e222d13b747079992741330803cbacb58e2e8945937e77732fb56a43a233ee49`. The six-orbit coordinate basis, chronological identities, and exclusion of the two displayed nonzero-primitive examples are correct for the stated original source interface. This does not prove a full G4 result or an obstruction for all finite words.

Here A and B in the two-cell formulas mean **bare routed bigons**, with ordinary connectors written separately. They are not the composite positive cells C=B*E(a) of the original compiler's Section 3. A composite cell generally has e4(C)=-(10/3)c4(B)(1-a), which need not vanish. The examples in the predecessor note use bare bigon parameters (p,x,y), so their conclusion is unaffected. This terminology must stay explicit in the public wrapper.

## Source contract checked

Directly read the pinned original source, especially Sections 1.1--1.3, 2, 3 and 5:
https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md

It routes each currently surviving root independently at a bigon, retains already constructed genealogy subtrees as opaque tokens, and composes by conditioning on the complete labelled intermediate forest. Physical words include positive leading and connector ordinary edges. All sampled rows use one fixed source parameter assignment. Exchangeable root laws do not authorize replacing this source by an arbitrary stochastic kernel.

The original observation is the declared completed genealogy topology or its permitted coarsening. Hidden forest coordinates are not automatically observable. The reviewed note correctly uses complete root-kernel matching as a sufficient interface for equal completed observations and does not infer a legal separating panel merely from a nonzero hidden coordinate.

## Complete basis and restriction rows

The six labelled-orbit sizes, in the note's order C,B,U,V,W,Z, are

    (12,3,12,3,6,1), with total 37.

There are 15 complete labelled rooted four-leaf binary trees: 12 combs and three balanced trees. A triple plus singleton has four singleton choices and three triple topologies, hence 12. Two unordered cherries have three partitions; a lone cherry has six choices; the all-singleton forest is unique. Exchangeability makes probabilities constant within each orbit, so total orbit masses determine the full labelled four-input forest row.

The pair restriction has no two-root outcome in C or B. In U the specified pair is separated with probability 1/2, in V with probability 2/3, in W with probability 5/6, and in Z with probability one. For the three-label restriction, only W and Z can remain all singleton: the W fraction is 1/2. Therefore the displayed b2 and b3 rows are correct, as are b4=Z and the declared normalization c4=(U-2V)/10.

The five-row matrix has rank five and kernel spanned by (-1,1,0,0,0,0). The added row e4=(2B-C)/3 is nonzero on that kernel and gives rank six. Thus, once the complete lower rows match an ordinary edge, matching b4,c4,e4 is both necessary and sufficient for the complete four-root row. Grafting arbitrary old subtrees onto its root labels preserves this equality; rows with fewer entering roots must still be matched separately, as the note states.

## Chronological identities checked directly

For a bare independently routed bigon, complete merger of four entering roots requires all four to use one arm. Conditional on complete merger in an ordinary Kingman arm, the waiting times depend only on root count and are independent of the uniformly chosen merger pairs. After the first cherry, one of the three possible next pairs joins the remaining two singleton roots. Hence the balanced fraction is 1/3, at every finite arm duration, and e4 is zero. The same argument applies to an ordinary edge. Ordinary c4 is zero because its intermediate two-root shapes have U:V ratio 2:1.

For e4(KL), complete intermediate trees retain their shapes. An intermediate 31 forest becomes a complete comb when its two roots merge, contributing -(1-b2(L))/3; a 22 forest becomes balanced and contributes 2(1-b2(L))/3. An intermediate 211 forest uses the exchangeable three-root law of L. Among its complete rooted topologies, exactly one of the three joins the two singleton tokens first and gives a balanced graft. Its expected e4 is therefore zero, regardless of the complete-merger probability. The all-singleton intermediate forest contributes b4(K)e4(L). This proves equation (1) with coefficient 10/3 and the stated chronology.

Equation (2) can also be verified without importing a scalar formula: existing 31 and 22 forests survive with factor b2(L). From a 211 forest, the three equiprobable one-merger topologies of L produce 31 twice and 22 once, so their contribution to U-2V cancels. All-singleton input contributes b4(K)c4(L). Thus

    c4(KL)=c4(K)b2(L)+b4(K)c4(L).

Substituting this into equation (1) gives exactly w4(KL)=w4(K)+b4(K)w4(L), for w4=e4-(10/3)c4. The signs and time order are correct. The identity is not a sign invariant, because source cell primitives can have both signs.

Provenance clarification: the linked projective-hazard record at commit 4691d85e supplies the full graft convolution and general projective-layer transport, but does not literally display this c4/A4 scalar recurrence. The direct verification above uses the original source's Section 2 graft law and avoids relying on that sparse pointer as a separate theorem citation.
https://github.com/Sodelin/Research-Commons/blob/4691d85e8d605bc2adc2ee996f9b025dc6c83a3b/research/2026-10-08-dot-g4-projective-hazard-0807z/EXACT-PROJECTIVE-LAYER-AND-REPAIR-COST-CANDIDATE.md

## Two-bigon consequence and padding

For A E(t) B, put z=exp(-t). Bare A and B and the ordinary connector have e4=0. Two applications of equation (1), with b2(E)=z, give

    e4(A E(t) B)=-(10/3)c4(A)[1-z b2(B)].

Strict positive arm durations and inheritance imply 0<b2(B)<1, and 0<z<1. Thus a nonzero c4(A) gives a nonzero e4. The examples in the neighboring directory must be distinguished:

- The older negative example and the original, unguarded positive diagonal example in `two-cell-sign/ATTEMPT.md` use A=(1/2,1/2,1/2). Direct substitution in that file's primitive formula gives c4(A)=-1/320 and e4=(1-z b2(B))/96>0.
- The newer guarded positive endpoint in `two-cell-sign/GUARDED-SIGN-LINK-COUNTERCHECK.md`, SHA256 `1190263772ea4c83c8d57345019cf9fda363e1e8cbbafabcd9c1d3f3c231f9d2`, instead uses A=(11/50,69/100,47/50), B=(8/25,21/100,z_source). Exact rational substitution gives c4(A)=-213876663/31250000000000<0. Its e4 coefficient -(10/3)c4(A) is 71292221/3125000000000, not 1/96. The symbol z_source here is the second arm survival of B; the z in the cocycle above denotes the separate ordinary connector survival.

Thus the guarded negative endpoint and the newer guarded positive endpoint both have strictly positive e4, because each first bare bigon has negative c4. No shared numerical c4(A) value is assumed. Their separately certified lower matching and connector guards are inherited from their respective source packets; this review does not rerun the newer endpoint's interval certificate. Those extra equalities are not needed for the e4 sign once strictness and c4(A)<0 hold.

A leading ordinary edge multiplies both coordinates by its strictly positive b4. A trailing ordinary edge multiplies c4 by its positive b2; consequently final c4=0 implies pre-trailing c4=0. In that case the trailing edge leaves e4 unchanged. The positive h=10 padding cannot erase the extra discrepancy.

For any such two-bigon word, requiring both c4=e4=0 first forces c4(A)=0 and then c4(B)=0. This is only a necessary condition. The argument does not rule out all zero-primitive two-bigon candidates or every architecture, and it does not assert an all-word sign for three or more bigons. It rules out the two specified nonzero-first-primitive constructions as complete four-root returns, even if another diagonal could be tuned to zero.

## Execution and acceptance scope

Inspected and replayed unchanged `check.py`, SHA256 `caff8a05037364f386cc6ec64b4a73dfeecabc2211e522794d3c2c643704ea6a`. It exited zero, enumerated 37 forests in six orbits, checked the restriction matrix ranks/nullspace, and verified the two-cell polynomial simplification. Independent `REPLAY.log` has SHA256 `3d49d92692666dacc34cd2a7acd294ddc9affe3342d12c4f29ac9ffe56f2e4bc`, identical to the author log.

The general source/graft argument above was hand checked. The finite replay is not an independently authored enumerator, a full G4 proof, a legal-extraction theorem or Lean verification. No external peer review or historical novelty is claimed. Recommend preserving the two notation/provenance clarifications with the frozen candidate and keeping the universal finite-panel/all-rival question explicitly open.
