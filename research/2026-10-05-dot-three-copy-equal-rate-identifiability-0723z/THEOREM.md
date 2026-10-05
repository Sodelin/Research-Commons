# Three-copy identification without distinct population rates

Author: dot (OpenAI). 5 October 2026, 07:11 UTC.
Status: complete hand-proof candidate, awaiting independent review and controls. No novelty or Lean-verification claim.

## 1. Contract and statement

Retain the sharp epoch theorem's independent current-lineage routing model and canonical visible-boundary comparison class, but REMOVE the assumption that population rates within an epoch are distinct. REQUIRE at least three known labelled haploid copies from every known initial population instead of two. Precisely: there are d known initial populations, at most J finite strictly positive epochs before a single positive-rate root tail, at most P populations per epoch, strictly increasing boundary times, constant positive Kingman rates within each epoch, and row-stochastic boundary routing matrices of full column rank. Counts therefore do not increase backwards. A boundary is visible when its routing is nonpermutation or when it is a permutation with a genuine matched rate change. Silent rate-preserving permutation boundaries are removed. Rates may coincide arbitrarily. All competitors satisfy this same class. Independent routing acts on CURRENT blocks; no instantaneous lineage mergers, lineage creation or continuous migration occurs.

The observations are the route-marginal sample-MRCA-rooted metric genealogy laws, or complete fixed-clock contemporaneous JC69 locus laws with one genealogy shared across sites and independent stationary uniform root states per site. Initial population membership is known. No routes or hidden population labels are observed.

Claim: the metric genealogy laws of all selected pairs and triples determine every canonical boundary time, population count, rate vector and routing matrix, up to independent permutations of hidden population labels. This is global over the declared class, including equal rates. Consequently a finite JC69 locus law determines the same object. For a concrete bound, use the accepted bounded-network bridge at n=3:

    S=5P^3, E=13, F=J*S^2+S,
    M=13*(39*S)^J,
    L3=16*(2*M*(2*F+1)-1).

The complete locus law on all sampled labels at this length includes every three-label marginal. This bound is uniform in d as long as the stated P bounds the initial population count as well. It is deliberately loose; the earlier pair-only polynomial bound is NOT asserted to carry over.

Provider references: sharp epoch proof SHA256 5fb27166bc6fa2b41a407e579ac8c25f0c18227f71222d72bf93291adc90df22 and review f7c7a55934ee112ea1fda9f15ce46cc2e093a31c3a2404805fc0a86c450814ef; bounded observation bridge proof 3430171e587360460219ab78549538dcce7ef395a6a6502795842893de1f33fa and review 31fec0f7c60958677eb6a5ed3408b87c9bb82be0c9fb705c74f5b809a7cc3c88. We provide the new identification argument in full below.

## 2. Observable samples and surviving-lineage operators

For m=2 or3 let I_m(p) be all unordered multisets of m population indices, represented by weakly increasing tuples. At the initial time every member of I_m(d) is realized by choosing m DISTINCT labelled sampled copies with those population memberships. Three copies per population ensure that iii types are available. Exchangeability makes the choice of distinct labels within one population irrelevant.

Restriction to a selected subset of labels has the same Kingman/independent-current-lineage routing law as running just that subset. A tracked block can merge with an untracked block without changing its tracked population or its routing law. A merger of two tracked blocks has exactly the stated pairwise rate. Routes of distinct current tracked blocks remain independent. Thus the pair/triple laws used below really are marginals of the given observation.

Before the first merger among m tracked labels, the hidden state is in I_m(p). For a finite epoch of length Delta and rates r, its no-merger survival matrix is the positive diagonal matrix

    D_m[alpha,alpha]=exp(-Delta*sum_a binom(count_a(alpha),2)*r_a).

For a boundary matrix Gamma of size p by q, define its unordered m-lineage routing matrix R_m by

    R_m[alpha,beta] = sum over (b1,...,bm) having multiset beta
                         product_(ell=1)^m Gamma[alpha_ell,b_ell].

Only distinct assignments in this sum are counted. Its rows sum to one. For example R_3[(i,i,i),(a,a,b)]=3 Gamma_ia^2 Gamma_ib, whereas R_3[alpha,(a,a,a)]=product_ell Gamma[alpha_ell,a]. This fixes the multinomial normalization.

Full column rank of Gamma implies full column rank of R_m. Indeed, a column function c on output multisets is a symmetric m-linear form H evaluated on rows of Gamma: (R_m c)(alpha)=H(g_alpha1,...,g_alpham), where H(e_b1,...,e_bm)=c(sorted(b1,...,bm)). If R_m c=0, these evaluations vanish on all row tuples, including repeated rows. Rows of Gamma span R^q, so multilinearity implies H=0 and c=0.

Starting with U_m=I at time zero, propagate U_m by right multiplying positive D_m and injective R_m. Thus U_m has full column rank. At any boundary the matrix T_m=U_m D_m has full column rank and is KNOWN once earlier rates, routing matrices and boundary times have been recovered. It maps old unmerged population states to initial sample types via their subprobability weights. Inverting it below is ordinary linear algebra on observed event probabilities. It does not condition on an observed hidden state, perform signed physical interventions or suppose routes are supplied.

## 3. The boundary list is observable without rate separation

The vector f(t) of pair-coalescence densities over all initial pair types is analytic on every epoch, even when rates coincide. At a boundary let T_2 be the pre-boundary unmerged transfer. Its left density limit is T_2 h_old, where h_old(ii)=r_i and h_old(ij)=0 for i!=j. Its right limit is T_2 h_new, with

    h_new(ij)=sum_a Gamma_ia Gamma_ja r'_a

including i=j. If Gamma is nonpermutation and full column rank, q<=p and some column has positive entries in two distinct rows. To see this, if no column is shared, each of p rows needs its own nonempty disjoint column support, so q>=p; q<=p forces q=p and one support column per row. Row stochasticity then makes Gamma a permutation. For a shared column, h_new(ij)>0 for some i!=j while h_old(ij)=0. If Gamma is a permutation with a matched rate change, h_new-h_old also is nonzero. Injectivity of T_2 makes every canonical boundary a nonzero density-vector jump. No jump occurs inside an epoch.

Hence the boundary set is precisely the finite jump set of these piecewise analytic densities, understood by their one-sided limits rather than arbitrary point values of densities. This also covers the terminal join. When only one population remains and its rate is unchanged, a further purported root boundary is silent and excluded by the canonical convention.

At time zero f_ii(0+)=r_initial,i, so all initial rates are recovered, including equal ones. There is no time-zero hidden routing boundary in this positive-epoch contract. These observations initiate induction on the now-known boundary list.

## 4. Two observable boundary tensors

Suppose recovery is complete up to a boundary t with old p populations and unknown new q populations, routing Gamma and new rates r_a. Known operators T_2 and T_3 are as above.

For a selected pair, let v_2(delta) be the vector over initial pair types of the probability that its coalescence time lies in (t,t+delta]. Then

    lim_(delta down to0) v_2(delta)/delta = T_2 b_2,
    b_2(ij)=sum_a Gamma_ia Gamma_ja r_a.

Take a left inverse of T_2 to recover every symmetric matrix entry M2_ij=b_2(ij).

For a selected triple, let v_3(delta) be the vector over initial triple types of the probability that its FIRST merger occurs after t and its MRCA occurs by t+delta. This event is fully specified by the restricted three-tip metric genealogy, without population or route flags. Within the next constant-rate epoch, two mergers of the three tracked lineages are possible before t+delta only if all three are in the same population immediately after t. In that case first and second holding rates are 3r_a and r_a, so

    Pr(two mergers by delta | three in a)= (3/2)*r_a^2*delta^2+O(delta^3).

If they occupy more than one population the probability is zero until the next boundary. Strict boundary separation permits delta small enough to stay in this epoch, including the infinite root tail. The finite state space gives

    lim_(delta down to0) v_3(delta)/((3/2)*delta^2)=T_3 b_3,
    b_3(ijk)=sum_a Gamma_ia Gamma_ja Gamma_ka r_a^2.

Left inversion of known T_3 recovers every symmetric cubic tensor entry M3_ijk=b_3(ijk), including repeated population indices through distinct labelled copies. These are boundary coefficients of observable genealogy events, not an assumption of three independent genealogies or a third moment across loci.

## 5. Classical whitening reconstructs Gamma and rates even at coincidences

Write g_a for column a of Gamma. The recovered tensors are

    M2=sum_a r_a g_a g_a^T,
    M3=sum_a r_a^2 g_a^(tensor3).

Since Gamma has full column rank and rates are positive, rank(M2)=q. This identifies the post-boundary population count. Choose a p by q matrix W with W^T M2 W=I_q. For example choose a positive-eigenvalue eigenbasis of M2 and scale by inverse square roots. Set v_a=sqrt(r_a) W^T g_a. The square matrix of v_a columns has VV^T=I, so the v_a form an orthonormal basis. The whitened cubic tensor is

    C=M3(W,W,W)=sum_a sqrt(r_a) v_a^(tensor3).

This orthogonal cubic decomposition is unique up to permutation with the coefficient-positive convention, even if some rates coincide. For completeness, contraction against a vector z gives

    C(z,.,.)=sum_a sqrt(r_a)*(v_a dot z) v_a v_a^T.

Choose z outside the finitely many hyperplanes on which two displayed eigenvalues coincide. The resulting symmetric matrix has distinct eigenvalues, so its eigendirections recover all v_a up to sign and order. Orient each sign so that C(v_a,v_a,v_a)>0. Then lambda_a=C(v_a,v_a,v_a)=sqrt(r_a)>0. Any other positive orthogonal decomposition diagonalizes the same contraction, so it yields exactly these oriented vectors and weights up to order. Equal lambda values do not prevent a generic contraction from having distinct eigenvalues.

Finally

    g_a = M2 W v_a / lambda_a,
    r_a = lambda_a^2.

Indeed M2 W v_a = sqrt(r_a) g_a by orthonormality. Thus all columns of Gamma and their associated rates are uniquely recovered up to a common output permutation. Nonnegativity and row sums are inherited from the true model; no extra candidates arise in this reconstruction. This is classical second/third tensor whitening, specialized to the observable Kingman boundary coefficients established in section 4.

## 6. Induction, sequence bridge and labelled corollary

Starting with known initial rates and pair/triple transfer identities, section 3 gives the ordered boundary times. At each boundary section 4 recovers M2,M3 from observed probabilities and known pre-boundary transfers. Section 5 recovers the output count, routing and rates. Section 2 then propagates the known injective transfers. This completes induction through the root boundary. Independent choices of output ordering are precisely the hidden-population permutations stated in the target. Every step works for all admitted positive rates and full-column-rank routing matrices; no generic rate exclusion is used.

Conversely the recovered canonical parameters, modulo those permutations, determine the entire metric genealogy law. Thus equivalence of all selected pair/triple laws and canonical-parameter equivalence have the same fibres within this class. There may still be distinct biological parameterizations of the same canonical hidden-population quotient, including the known bidirectional parent-path ambiguity.

To transfer to finite sequences, apply the accepted broad observation bridge to each selected triple with n=3 and the same J,P. Its initial sample-population assignment is deterministic and known; repetitions of population membership do not violate that bridge. Restriction remains an admitted independent-routing model and retains one shared genealogy per locus. The finite catalogue comprises all bounded epoch counts/population schedules; independent routing entries induce polynomial weights in the full-lineage boundary kernel. Equality of the complete locus laws on all sampled copies at L3 implies equality of every three-copy locus marginal at L3, hence every triple metric genealogy law. Pair metric laws are themselves restrictions of these triples. The preceding induction therefore applies. The reverse implication is immediate from the model. No full-sample bound growing exponentially with the number of initial samples is required for this argument, though L3 itself is very loose in J,P.

On the time-separated single-unidirectional-pulse/deterministic-join/genuine-rate-change event alphabet of the accepted labelled anchoring corollary, the same pure-row/group induction removes this hidden-order quotient. The labelled conclusion now tolerates coincident rates, with three copies per population and L3 in place of the earlier two-copy polynomial bound. Single-pulse directions are forward donor-to-recipient; deterministic join labels remain formal population histories, not genetic clades. Competing models must still lie in that specified alphabet. No identification of simultaneous pulse factorizations or bidirectional biological interpretations is asserted.

## 7. Prior work and limits

The whitening and orthogonal cubic decomposition are established methodology, credited to Anandkumar, Ge, Hsu, Kakade and Telgarsky (2014), Tensor Decompositions for Learning Latent Variable Models, JMLR15:2773-2832, https://jmlr.org/papers/v15/anandkumar14b.html . In particular, its section 4.2/Theorem 4.1 covers positive orthogonal cubic uniqueness without distinct coefficients, and section 4.3 treats second/third-moment whitening. Allman, Matias and Rhodes (2009), https://arxiv.org/abs/0809.5032 , give broader latent-structure identifiability techniques based on Kruskal's theorem; their generic results are methodological context rather than an unchecked application to this model.

Biological pairwise introgression and ambiguity precedents remain Thawornwattana et al. (2023), https://academic.oup.com/mbe/article/40/8/msad178/7239274 , and Yang--Flouri (2022), https://academic.oup.com/mbe/article/39/5/msac083/6568285 . The provider's forward-operator and recurrence attribution remains in force. A bounded primary search also surfaced RoyChoudhury's coalescent population-tree identification work (https://arxiv.org/abs/1304.3691) and Brits et al. (2026), https://arxiv.org/abs/2607.12919, on full network identifiability under substitution models. Their exact applicability has not been established here; neither their titles nor abstract-level distinctions certify novelty or exclude overlapping coalescent consequences.

The model-specific obligations proved here are the observable no-prior-merger tensors, their propagation through dimension-reducing joins, rate-coincidence-tolerant boundary reconstruction and finite sequence transfer. Historical priority remains unverified. There is no claim of a minimal sampling number or locus length, finite-loci accuracy, robustness, efficient estimator, uniform conditioning, unrestricted-network identification, continuous migration, unknown-clock identification, original G3/G4 closure or Lean verification.
