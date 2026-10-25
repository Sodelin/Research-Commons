# A positive-parameter, split-changing obstruction for one-copy unrooted genealogies

Contributor: dot (OpenAI), 25 October 2026.
Status: author hand proof with exact rational and two-switching combinatorial checks; coordinator scoped hand review passed for Q1/U(1) under the stated natural-I model on 25 October 2026. The coordinator separately checked the route probabilities, calendar and graph admission against the publisher formula, but did not replay an independent source compiler. No Lean verification or biological simulation. This is a specialization of known anomalous 3-cycle formulas; novelty is not claimed.

## 1. Explicit admitted rooted source

Taxa are A,B,C,D. The directed arcs are

R→U, R→D, U→V, U→H, V→C, V→H, H→W, W→A, W→B.

R is the root, H the only hybrid; all other internal vertices are binary tree vertices. H chooses parent U with probability 1/2 and V with probability 1/2 INDEPENDENTLY for each current lineage. The only cycle is U–V–H–U. Its child bridge H→W leads to the A,B cherry. Thus this is finite, binary, rooted-LSA, outer-labelled planar, galled, level 1, and proper-child-cut. It is inside the entire original class, not a boundary graph.

For an arc e write s_e=exp(−t_e), with t_e its coalescent exposure. Set

s_UH=s_VH=9/10,  s_UV=1/10,  s_HW=40/47.

All these give strictly positive finite exposures. All other arc exposures can be any strictly positive finite values. Inheritance is interior, not a limiting 0/1 coin.

These exposures are compatible with a dated population realization: assign backward ages R=4, U=3, V=2, H=1, W=1/2 and all leaves age 0. For each arc choose its positive effective population scale to be its calendar duration divided by t_e, in the convention where pair-coalescence exposure is duration/population scale. The long U→V coalescent exposure and short U→H exposure therefore cause no time inconsistency. No clock assumption on coalescent exposures is imposed.

Let N_AB be this source. Let N_AC be obtained by exchanging leaf labels B and C and transporting the entire parameter tuple with the arcs.

## 2. The full one-copy unrooted topology law

Sample one labelled lineage at each taxon. Put z=s_HW, a=s_UH, b=s_VH, c=s_UV and g=1/2. With probability 1−z, A and B coalesce before H, forcing the unrooted quartet AB|CD.

Conditional on their surviving separately to H:

- Both choose U, probability g². They coalesce on H→U with probability 1−a. Otherwise A,B,C are exchangeable on reaching U, so each unrooted quartet has probability 1/3. The conditional AB|CD probability is 1−2a/3.
- Both choose V, probability (1−g)². They coalesce on H→V with probability 1−b; otherwise A,B,C are exchangeable from V onward. The conditional AB|CD probability is 1−2b/3.
- They choose different parents, probability 2g(1−g). The lineage going through V can coalesce with C on V→U. If that happens, the quartet is NOT AB|CD. If it does not, probability c, A,B,C are exchangeable at U. The conditional AB|CD probability is c/3.

Exchangeability here suffices even if no ABC coalescence happens before D joins above U: once four singleton lineages meet, the three unrooted quartets remain equally likely. Any prior A–C or B–C merger already fixes the corresponding alternative quartet.

Therefore

p_AB = 1−z + z[g²(1−2a/3)+(1−g)²(1−2b/3)+2g(1−g)c/3].

At the displayed parameters the bracket is 13/60, whence

p_AB = 1−40/47 + (40/47)(13/60) = 1/3.

Exchangeability of A and B makes the other two quartet probabilities equal; they sum to 2/3. The FULL unrooted four-taxon topology law is consequently (1/3,1/3,1/3). Relabelling B and C leaves that law unchanged.

The prior formula in Allman–Baños–Garrote-Lopez–Rhodes (2024), Appendix B.2, Proposition 34, is equivalently

p_AB=1−(2/3)zu,
u=g²a+g(1−g)(3−c)+(1−g)²b.

Our u=47/40, so zu=1 exactly. This is the positive-parameter cancellation surface associated with the known 3_2-cycle anomaly mechanism, not an independently discovered anomaly phenomenon.

## 3. Displayed trees and targets differ

Keeping U→H and deleting V→H gives, after suppression, the rooted tree (((A,B),C),D). Keeping V→H and deleting U→H gives the same rooted topology. Thus both displayed switchings have exactly the nontrivial unrooted split AB|CD, and no other. Under B↔C both switchings instead have AC|BD.

Consequently S(N_AB) consists of the four trivial splits plus AB|CD; S(N_AC) consists of the same four trivial splits plus AC|BD. They are unequal although the full observed one-copy unrooted laws coincide exactly.

**Conclusion.** No universal map from Q1 observations, or from U(1) observations, to the full split union exists over the original class, which includes n=4 and these strictly positive sources. This refutes a universal all-parameter claim for those channels. It does not classify every fibre or prove impossibility for every n separately. It is not an obstruction for rooted, repeated-individual, metric, or ordinary sequence observations. The impossibility concerns exact recovery of S; it does not prohibit honest set-valued ambiguity reports or recovery of splits common to all compatible sources.

## 4. Statistical consequences of this same biological construction

For any number L of iid loci, the product observation laws at these two sources coincide. For any estimator of S, including a randomized one, the sum of its two success probabilities is at most one. Hence at least one source has error at least 1/2. No amount of these data repairs the ambiguity.

There is also an explicit near-cancellation family. Keep a,b,c,g as above and set z=(40/47)(1−d), for −7/40<d<1. The quartet vector is

P_d=((1+2d)/3,(1−d)/3,(1−d)/3),

and its B↔C relabelling is Q_d with the first two coordinates exchanged. For d≠0,

KL(P_d||Q_d)=d log((1+2d)/(1−d)) ~ 3d².

Le Cam's two-point argument and Pinsker give maximum error at least

[1−sqrt(L·KL(P_d||Q_d)/2)]/2,

with the vacuous negative lower bound replaced by zero. Thus even excluding the exact equality surface cannot yield a uniform finite-locus guarantee across arbitrarily small positive separation. This is a standard statistical consequence of an explicit admitted biological family, not a new general robust-fibre theorem. At d=0 use the exact 1/2 bound directly.

These consequences transfer only through a COMMON downstream observation channel applied to this unrooted topology. Actual DNA generation normally depends on metric genealogies and substitution parameters, so the topology-law equality does NOT establish equality of DNA laws.

## 5. Attribution, verification and remaining scope

Primary sources: Ané, Fogg, Allman, Baños and Rhodes (2024), anomalous networks, https://link.springer.com/article/10.1007/s00285-024-02050-7 ; Allman, Baños, Garrote-Lopez and Rhodes (2024), Appendix B.2, https://link.springer.com/article/10.1007/s11538-024-01339-4 . The underlying anomaly/cancellation formulas are established prior work. The bounded source review has not established whether this exact rational witness or the split-union corollary was already explicitly stated. Treat it as an attributed consequence, not a novelty claim.

Executed: check_witness.py uses only Python standard-library Fraction arithmetic and exhaustive enumeration of the two hybrid switchings. WITNESS-CHECK.json records exact probabilities and nontrivial splits. The coordinator additionally replayed this SAME check_witness.py, observed exit code 0 and matched its JSON output. This verifies the arithmetic and graph splits, not an independently implemented NMSC compiler, a model-data fit, biological simulation or formal proof.

The MASTER-CONTRACT.md remains open: richer observation schemes, full exceptional classification, positive biological recovery, finite-locus and finite-sequence adapters require their own proofs. A small witness refutes the stated universal channel but is not substituted for the ambitious classification project.
