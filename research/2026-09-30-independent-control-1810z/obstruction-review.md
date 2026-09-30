# Independent-inheritance control obstruction: audit

The proposed four-taxon network and the proposed concordance-factor formula are correct under NMSCind. The numerical example gives a strict anomaly and refutes transfer of the min-subtracted CF support provider to the stated partial-control menu. Pairing it with the diamond in Section 6 gives the stronger failure of unrooted-quartet support identifiability from the complete profile of that available menu. Neither claim concerns a profile containing every possible control, rooted or metric gene-tree observations, or known attachment/order information.

## 1. Network and admissibility

The original network has arcs

`R→D,U; U→V,H; V→C,H; H→W; W→A,B`.

It is rooted and binary: R has outdegree two; U,V,W have indegree one and outdegree two; H has indegree two and outdegree one. Its sole undirected cycle is the triangle U–V–H–U. H→W is a cut-edge, and the four labeled leaves admit an outer-face planar embedding. Thus the original example is already in the level-1 subclass of the stated larger source class. Keeping either incoming arc at H and suppressing unary vertices gives the unrooted quartet AB|CD. Consequently every global switching displays AB|CD, and its switching occurrence is exactly one.

All four specified coalescent lengths are strictly positive and finite: put L=log(10/9) and M=log(10), and use t(HW)=t(UH)=t(VH)=L and t(UV)=M. A positive chronology with contemporaneous leaves is

`τ(A)=τ(B)=τ(C)=τ(D)=0, τ(W)=1, τ(H)=2, τ(V)=3, τ(U)=4, τ(R)=5`.

For the diploid convention t(e)=Δτ(e)/(2N_e), set N_HW=N_VH=1/(2L), N_UH=1/L, and N_UV=1/(2M). These are all positive and finite. Give the remaining arcs any positive finite lengths, using the same relation to choose their populations. Calendar durations satisfy Δτ(UH)=Δτ(UV)+Δτ(VH). Coalescent lengths need not satisfy t(UH)=t(UV)+t(VH), because these arcs have different population sizes. This is a time-consistent realization in the positive-duration arc model; it does not assume a common effective population size on all arcs.

## 2. Hand derivation of the quartet CFs

Write x0=exp(−t(HW)), u=exp(−t(UH)), v=exp(−t(VH)), w=exp(−t(UV)), and let a denote the gene-quartet probability of AB|CD. Each lineage at H independently chooses its U parent with probability γ and its V parent with probability 1−γ.

The A and B lineages coalesce on HW with probability 1−x0. This guarantees AB|CD, regardless of the later parental choice. Conditional on their surviving separately to H, there are three cases:

* Both choose U (probability γ²). They coalesce on HU with probability 1−u. If they survive, three exchangeable lineages A,B,C meet at U, giving each unrooted quartet probability 1/3. The conditional matching probability is 1−2u/3.
* Both choose V (probability (1−γ)²). The same reasoning on HV gives conditional matching probability 1−2v/3.
* They choose different parents (total probability 2γ(1−γ)). The lineage sent to V shares UV with C, and those two coalesce there with probability 1−w, producing a discordant quartet. If they survive UV, A,B,C are exchangeable at U. The conditional matching probability is w/3.

The exchangeability statement remains true for any positive finite length on UR: a coalescence among A,B,C selects each pair equally, and if all three survive to the root, the four-lineage coalescent gives each unrooted quartet probability 1/3. None of the omitted pendant or upper lengths changes these calculations.

Therefore

`a = 1−x0 + x0[γ²(1−2u/3) + (1−γ)²(1−2v/3) + 2γ(1−γ)w/3]`.

Interchanging A and B preserves the stochastic process and exchanges the two discordant quartets. Thus their probabilities are both (1−a)/2. More explicitly, in one split-parent assignment the V-side discordant quartet has probability 1−2w/3 and the other has probability w/3; the equally weighted opposite assignment exchanges them.

For x0=u=v=9/10, w=1/10, γ=1/2, the bracket is

`(1/4)(2/5)+(1/4)(2/5)+(1/2)(1/30)=13/60`.

Hence the CF vector in the order (AB|CD, AC|BD, AD|BC) is exactly

`(59/200, 141/400, 141/400)`.

It sums to one, and 59/200<1/3<141/400. Its min-subtracted vector is `(0,23/400,23/400)`. If normalized by its sum, the vector is `(0,1/2,1/2)`. This provider therefore places no support on the sole displayed quartet and positive support on both absent quartets, although displayed occurrence is one.

## 3. Endpoints and anomaly boundary

Forcing H to U gives `a_U=1−2x0u/3`; forcing H to V gives `a_V=1−2x0v/3`. Since all relevant lengths are strictly positive and finite, x0u<1 and x0v<1, so both endpoint matching CFs are strictly greater than 1/3. Each endpoint's min-subtracted provider therefore has support precisely AB|CD. At the numerical parameters, both endpoint CF vectors are `(23/50,27/100,27/100)`.

Set `A=1−2u/3`, `B=1−2v/3`, `C=w/3`, and

`f(γ)=Aγ²+B(1−γ)²+2Cγ(1−γ)`.

Here A,B>1/3 and C<1/3. The denominator D=A+B−2C is strictly positive. Completing the square gives

`γ*=(B−C)/D`,

`f_min=(AB−C²)/D`,

`f(γ)=f_min+D(γ−γ*)²`.

Both B−C and A−C are positive, so γ* lies strictly between zero and one. The optimized matching CF is `a_min=1−x0+x0 f_min`. A strict anomaly exists at this fixed x0 exactly when

`x0 > 2/[3(1−f_min)]`.

Equality is the boundary a_min=1/3. At a=1/3 all three CFs are 1/3 and the min-subtracted vector is zero. For any fixed γ, the equivalent strict-anomaly condition is `f(γ)<1−2/(3x0)`.

For an anomaly to be achievable with some allowed x0<1, it is necessary and sufficient that f_min<1/3. An equivalent transparent condition is

`(1−w)² > 4(1−u)(1−v)`.

For the numerical example, γ*=1/2, f_min=13/60, and the critical x0 is 40/47<9/10. At these fixed x0,u,v,w,

`a(γ)=23/50−(33/50)γ(1−γ)`;

the strict anomaly holds exactly when `γ(1−γ)>19/99`, equivalently

`(1−sqrt(23/99))/2 < γ < (1+sqrt(23/99))/2`.

## 4. The neutral bigon and the r=2 menu

The stated source class permits parallel arcs. Replace R→D by R→P, two parallel arcs P→J, and J→D. P is a binary tree vertex, J is a binary hybrid vertex, and J→D is a cut-edge. The added bigon is disjoint from the original triangle, preserves an outer-face leaf embedding, and adds exactly one hybrid. Thus r=2 and the augmented network is admissible. For example choose τ(P)=4 and τ(J)=2, with both parallel arcs having duration two and any positive finite coalescent lengths. Choose any interior inheritance probability at J in the uncontrolled source network.

Only the D lineage ever traverses J and its two parental arcs. No coalescence can take place there. Both paths reach the same vertex P and then R. Thus D's parental choice has no effect on any four-taxon gene-quartet probability. This remains true even if the parallel arcs have different coalescent lengths. The two controls `J=0` and `J=1`, each leaving H unforced, have exactly the anomalous CF vector calculated above.

This is the existing r=2 single-actuator menu with 2r−2=2 rows, omitting H. It satisfies the universal **exact two-ID pair-hitting** criterion: for any assignment `(H=h,J=j)`, the row `J=j` is compatible with that assignment and forces its J literal. There are four such pair assignments, all covered.

The shorthand “all assignments on at most two IDs must have a literal forced” is too strong and should not be used: a singleton assignment on H has no literal forced by this menu. In the occurrence argument, singleton certificates do not require that stronger condition to obtain probability at least g, and a zero-choice certificate has probability one. Here the displayed AB|CD certificate is genuinely zero-choice: every assignment of H and J displays AB|CD. Both rows therefore have displayed occurrence one. No parental bit has to be forced to certify its presence; the two other displayed quartets have occurrence zero in every row.

## 5. Scope of the single-network provider obstruction

This example refutes the universal claim that the min-subtracted CF support provider transfers to ordinary independent inheritance under this partial menu. Even though the menu is sufficient for the relevant displayed-occurrence witness guarantee, both available controlled CF providers return support on absent quartets and exclude the displayed quartet. A witness guarantee about switchings does not supply the missing CF-provider property under NMSCind.

The single-network argument alone does **not** prove failure of every provider on the available profile. Forcing H to either parent gives the tree endpoint CFs above and recovers the sole displayed quartet. The observed interior CF vector is nonuniform, with AB|CD its unique smaller coordinate, and its signed matching-minus-discordant contrast is −23/400. That information is discarded by min-subtraction. Any previously established known-order signed-provider result must be assessed on its own hypotheses and is not contradicted by this support-provider counterexample. The second-network construction below supplies the missing indistinguishability argument for the specified unknown-order partial menu.

No NANUQ formula is needed for this audit; the conclusion follows directly from the lineage-level independent-inheritance process and the exact control calculations.

## 6. Stronger matched-pair obstruction for the full available profile

Call the triangle-plus-bigon network above N_T. Give all its unspecified original and bigon arcs survival factor 1/2, retain x0=u=v=9/10 and w=1/10, and set both natural inheritance probabilities γ_H=γ_J=1/2.

Define a second original network by

`R→B,U; U→V,W; V→C,H; W→D,H; H→A`.

Replace R→B by R→P, two parallel arcs P→J, and J→B, giving the second network N_D. The H gall is the diamond U–V–H–W–U; the J gall is a separate neutral bigon. Both hybrid child edges are cut-edges. The network is rooted, binary, outer-labeled planar and level-1, hence in the admitted source class. It has the same four taxon labels and the same two hybrid identifiers H,J as N_T. The graph attachments and the outer order are not assumed known to the observer.

Set

`x_UV=x_UW=177/200`

and give every other original and bigon arc survival factor 1/2. Again set γ_H=γ_J=1/2. All coalescent lengths are positive and finite. For a positive contemporaneous-leaf chronology, take leaves at time zero, H at time one, V and W at time two, U at time three, and R at time four. The added P and J can be at times three and one. Choosing each population by N_e=Δτ(e)/(2t(e)) realizes every specified coalescent length and both equal-duration parallel arcs.

Both source networks satisfy the common length lower bound

`τ=−log(9/10)>0`

because every survival factor is at most 9/10: in N_T the maximum is 9/10, and in N_D the maximum is 177/200<9/10. All natural inheritance probabilities satisfy the same bound g=1/2. The forced control at J is an allowed endpoint intervention; the bound refers to the natural/unforced inheritance parameters.

In N_D, H has only the single A gene lineage below it, and J has only the single B lineage below it. Independent and common inheritance therefore coincide for this one-gene-per-taxon calculation. Choosing V at H gives the displayed unrooted tree AC|BD with internal edge UV; choosing W gives AD|BC with internal edge UW. The other arcs become pendant or upper edges for this quartet and do not alter its unrooted CFs.

In the order (AB|CD, AC|BD, AD|BC), the conditional tree CF vectors are

`H=V: (x_UV/3, 1−2x_UV/3, x_UV/3)`,

`H=W: (x_UW/3, x_UW/3, 1−2x_UW/3)`.

At x_UV=x_UW=177/200, their equal mixture is

`(59/200,141/400,141/400)`.

Equivalently the common baseline is x/3=59/200 in all coordinates, and each of the two displayed coordinates receives the increment (1/2)(1−x)=23/400. These are exactly the CFs of N_T.

The available menu in both states is the identical two-row menu `{J=0, J=1}`, leaving H naturally random. The J bigon is inert in each network, although its descendant taxon is D in N_T and B in N_D. Consequently each row has the same complete unrooted gene-quartet probability law in both states:

`Law_T(J=0)=Law_T(J=1)=Law_D(J=0)=Law_D(J=1)=(59/200,141/400,141/400)`.

With four taxa there are exactly three unrooted binary gene-tree topologies, so equality of this vector is equality of the entire one-locus unrooted-topology observation law. It also gives equal laws for any numbers of independent loci sampled under these menu rows. Infinite data under this fixed menu cannot distinguish the two states.

Their displayed occurrence vectors, however, are different:

`Q_T=(1,0,0)`,

`Q_D=(0,1/2,1/2)`.

Their displayed quartet supports are respectively `{AB|CD}` and `{AC|BD,AD|BC}`. Thus the complete available controlled profile cannot identify the displayed occurrence vector or its support on this source class. This is an actual fixed-menu identifiability obstruction, stronger than failure of the min-subtracted provider.

The common menu still meets the exact two-ID pair-hitting criterion in both states. N_T has the zero-choice certificate already discussed. In N_D, each displayed quartet has a singleton H-choice certificate, with occurrence 1/2 under either J control; no H forcing is needed to attain the g=1/2 occurrence guarantee. The occurrence coverage property therefore holds in both states while their full available gene-topology profiles agree.

The quantifiers are essential. This refutes a universal claim of displayed-support identifiability for the r=2, ID-only, 2r−2 partial-menu scheme with unknown order/attachments and only unrooted gene-topology observations. It does not assert failure for every menu, all possible controls, rooted gene-tree distributions, branch lengths or coalescent times, or an observer given the attachment graph or the relevant outer order. Adding an H endpoint control separates the states: N_T gives `(23/50,27/100,27/100)` with AB|CD its largest coordinate, while either N_D endpoint has its chosen AC|BD or AD|BC coordinate equal to 41/100 and the other two coordinates equal to 59/200. A known-order signed-provider theorem likewise has additional information absent from this matched pair.

This is the passive triangle/diamond indistinguishability construction adapted to the same identified-hybrid control profile by an inert J actuator. Its proof here is the exact lineage calculation and the two displayed-tree mixture, independent of any prior formula or section numbering.
