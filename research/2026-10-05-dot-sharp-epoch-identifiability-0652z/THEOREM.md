# Finite sequence length identifies a broad pulse/merge epoch model modulo its exact hidden-state ambiguity

Author: dot (OpenAI). 5 October 2026, 06:42 UTC.
Status: complete hand-proof candidate awaiting independent review; no Lean or novelty-priority claim. All conclusions use CONTRACT.md, especially its competitor class and interpretation of hidden-population permutations.

## Theorem and explicit length

For any two models in the stated canonical visible full-column-rank independent-routing class, the following are equivalent:

1. Their canonical epoch-routing representations agree up to the specified hidden-population permutations.
2. Their marginal rooted timed-genealogy laws agree.
3. Their selected-pair coalescence-age laws agree for every unordered initial-population pair type, including two distinct copies from one population.
4. Their complete JC69 locus laws agree at length

       L_pair = 2(2J+1)(JP+1)-1.

The initial population labels and sampling configuration are fixed across the comparison. Counts, times, rate vectors and routing matrices are reconstructed rather than assumed. The length is an upper bound, not a minimum or a finite-number-of-loci accuracy guarantee.

The finite pair-moment bound used below applies more broadly than the sharp reconstruction: coincident rates do not invalidate that bound. The distinct-rate hypothesis is used to separate population components in the reconstruction.

## 1. Selected pairs retain the actual source semantics

Choose one actual pair for every initial population type (a,b), a<=b. For a=b use the two distinct labelled sampled copies. Thus there are D0=d(d+1)/2 pair types. We use their marginal laws, not independence between these overlapping pairs.

In the full sampled genealogy, restrict attention to the two current blocks carrying this pair until they meet. Within a population their mutual merger rate is r, regardless of additional lineages. Mergers with unobserved blocks do not change their populations, and do not turn one current lineage into independent descendants. At a boundary, the two tracked blocks route independently by the declared Gamma rows until they have merged. This is exactly the two-lineage marginal process. Once they merge, the pair is absorbed. No latent route is observed.

Therefore the unmerged pair states in an epoch with p populations are the unordered pairs (a,b), a<=b, including co-occupancy (a,a). A positive finite epoch of duration Delta has substochastic survival matrix

    D(Delta)[(a,b),(a,b)] = exp(-r_a Delta), if a=b;
                             1,                if a<b.

It is diagonal and invertible. The lost mass is precisely coalescence of the tracked pair.

## 2. Independent routing and its rank

For a row-stochastic matrix Gamma from p old populations to q new populations, its unordered-pair transition R(Gamma) has entries

    R[(i,i),(a,a)] = Gamma_ia^2,
    R[(i,i),(a,b)] = 2 Gamma_ia Gamma_ib,                  a<b,
    R[(i,j),(a,a)] = Gamma_ia Gamma_ja,                    i<j,
    R[(i,j),(a,b)] = Gamma_ia Gamma_jb+Gamma_ib Gamma_ja,  i<j,a<b.

These formulas follow from two independent current-lineage choices. They define a row-stochastic matrix of size p(p+1)/2 by q(q+1)/2.

If Gamma has full column rank, then R(Gamma) has full column rank. Here is an explicit normalization-independent proof. Let c index unordered output pairs and form the homogeneous quadratic polynomial

    P_c(y)=sum_a c_(a,a)y_a^2 + 2 sum_(a<b)c_(a,b)y_a y_b.

If R(Gamma)c=0, its diagonal input rows say P_c(Gamma_i)=0. Its off-diagonal input rows say the associated symmetric bilinear form B_c(Gamma_i,Gamma_j)=0. These statements give B_c=0 on all pairs of rows of Gamma. The rows span R^q because Gamma has full column rank. Bilinearity then gives B_c=0 on R^q, so every c vanishes. Thus the kernel is zero. Equivalently this is the injectivity of the symmetric-square map, with the displayed factors of two fixing the basis convention.

Let U_j be the matrix whose row for an initial pair type gives its unnormalized distribution over current unmerged pair states at the START of epoch j. Then

    U_0=I,
    U_j=U_(j-1) D_(j-1)(t_j-t_(j-1)) R(Gamma_j).

Inductively U_j has full column rank: the survival factor is invertible, R has full column rank, and U_(j-1) is injective on its column-coordinate space. This argument covers dimension-reducing joins; it does not require a square pair transition. Absorption causes no rank failure because survival probabilities are strictly positive over finite intervals.

## 3. Density vector and unique exponential components

Let f(t) be the vector of coalescence-age densities for the D0 initial pair types. On epoch j,

    f(t_j+u)=sum_(a=1)^p_j r_(j,a) U_j[:,(a,a)] exp(-r_(j,a)u).

All coefficient vectors are nonzero because U_j has full column rank; they are also nonnegative. Within-epoch rates are distinct. Thus this representation identifies the number p_j, the unordered set of rates, and their coefficient vectors from f on any nonempty open subinterval.

For completeness, this uses only classical linear independence of distinct exponentials. In any putative equality of two representations, collect their union of distinct rates. Differentiating at an interior time through one less than the number of rates gives a Vandermonde system for each vector coordinate. Its determinant is nonzero, so every vector coefficient difference is zero. Nonzero coefficient vectors ensure that no population rate disappears from the representation. This is a distribution-level uniqueness argument, not a claim of numerical conditioning.

## 4. Event visibility is proved from the source conditions

At a boundary t_j set T=U_(j-1)D_(j-1)(t_j-t_(j-1)); this matrix has full column rank. Let h_old be the old pair hazard vector: r_old,i on (i,i), and zero on (i,k) with i<k. Define h_new similarly. The one-sided density limits satisfy

    f(t_j-)=T h_old,
    f(t_j+)=T R(Gamma_j) h_new.

If Gamma is not a permutation, it has a column with positive entries in two different rows. To prove this, suppose instead that every column were supported in at most one row. Every row has a positive entry because its sum is one; consequently q>=p. Full column rank gives q<=p. Hence q=p, each row and column has exactly one positive entry, and each such entry is one: Gamma is a permutation, a contradiction.

For the overlapping rows i!=k and column a,

    (R(Gamma)h_new)_(i,k)
       =sum_b Gamma_ib Gamma_kb r_new,b >0,

while (h_old)_(i,k)=0. So these hazard vectors differ. Since T is injective, the observed density vector has a nonzero jump. If Gamma is a permutation, the two hazard vectors differ exactly when at least one matched rate changes; this is the other visibility condition.

Therefore EVERY boundary in this canonical class is a genuine jump of f. There are no within-epoch jumps. The jump set of the vector density hence determines all t_j and the actual number of finite epochs. Densities are defined almost everywhere, but each piece has a unique analytic representative and one-sided limits, so this jump set is determined by the laws.

If a permutation preserves all matched rates, the boundary is truly silent: it merely renames populations and leaves the whole lineage process unchanged. Removing it is a necessary presentation convention for the target, rather than an observation secretly supplied to the proof. Such boundaries are not admitted competitors here.

## 5. Inductive recovery of rates and routing matrices

The first epoch begins with the known pair-state identity matrix U_0. The within-population pair density near zero directly gives every initial rate r_(0,a). Subsequent epoch boundaries are known from Section4.

Assume all earlier epochs and matrices have been recovered, in their chosen hidden labelings. At t_j the known matrix

    T=U_(j-1)D_(j-1)(t_j-t_(j-1))

has full column rank. Section3 recovers the new rates r_(j,b), up to their ordering, and the vectors U_j[:,(b,b)] by dividing each exponential coefficient by its rate (with the known time-origin shift).

Choose any mathematical left inverse T_left. Then

    w_b=T_left U_j[:,(b,b)]
        =R(Gamma_j)[:,(b,b)].

For an old co-occupancy state (a,a),

    (w_b)_(a,a)=Gamma_j[a,b]^2.

All routing entries are nonnegative, so

    Gamma_j[a,b]=sqrt((w_b)_(a,a))

uniquely recovers every entry of that column. Off-diagonal old-pair entries provide the consistent products Gamma_j[a,b]Gamma_j[c,b]; they are not ignored by the model. Having recovered Gamma_j, compute all columns of U_j from the displayed recurrence and proceed to the next boundary.

The left inverse may have signed entries, but is an analytical reconstruction from laws, not a physical routing intervention. The procedure recovers all populations, rates, times and routing columns. Its only ordering freedom is the independent permutation of the hidden populations in each epoch. Initial labels are fixed and the root has one population.

Thus equal pair laws imply canonical equivalence. Conversely that equivalence relabels the entire ancestral state process, preserves all rates and routing probabilities, and fixes the sampled labels. It therefore gives equality of the full marginal timed-genealogy laws. Equality of full genealogy laws plainly implies equality of their pair laws. This proves equivalence of claims1--3.

## 6. A much smaller general pair-moment bound

Put c=8/3. For one selected pair, the k-site repeated nontrivial JC character moment is

    m(k)=E[exp(-c*k*T_pair)],   k>=0.

This uses one genealogy at a locus. The complete length-L locus law determines these moments for k=1,...,L by character products and site marginalization; m(0)=1 is known.

More generally, in any bounded pulse model with no within-epoch migration, a pair's density during an epoch is a finite mixture

    sum_a A_(j,a) r_(j,a) exp(-r_(j,a)(t-t_j)),

where A_(j,a) is the probability that at the start the pair is still unmerged and its two current blocks occupy population a. Conditional on such co-occupancy, their mutual Kingman merger rate is constant and other lineages do not change it. Terms with separate populations contribute no within-epoch coalescence. The root tail is one shifted exponential. Hence no Jordan or equal-rate resonance is needed for this pair-density statement, even when other sampled lineages or rate ties are present.

A finite-interval density term with amplitude A*r contributes

    A*r/(r+c*k) * [exp(-c*k*t_j)
                  -exp(-r*Delta_j) exp(-c*k*t_(j+1))].

The root term has only its left endpoint. Therefore each pair transform has the form

    m(k)=sum_(b in B) beta_b^k P_b(k)/D(k),
    beta_b=exp(-c*b),
    D(k)=product_(indexed rates r)(r+c*k)>0,

with at most J+1 boundary bases, including zero, and at most R=JP+1 indexed rate factors. Numerator degree is at most R-1. Repeated rates cause no difficulty: keep their indexed factors rather than introducing a zero rate-difference denominator.

For two models, clearing both denominators makes the difference an exponential-polynomial sequence with at most 2J+1 bases (the zero boundary gives the shared base1) and polynomial coefficient degree at most 2R-1. The factor (E-beta)^(2R) annihilates each term, so the sequence has a monic recurrence of order at most

    2(2J+1)R <= 2(2J+1)(JP+1).

Its first K values k=0,...,K-1 determine all later values. Thus equality of pair moments through L_pair=K-1, along with the known zeroth moment, implies equality of all integer moments. The transformed age exp(-c*T_pair) is supported in [0,1], so compact moment determinacy and the inverse logarithm give equality of the pair-age laws. Root time is finite, so no mass at zero is added by the transformation.

This finite-length argument does not require distinct rates or the sharp routing-rank conditions; those are used in Sections2--5 to identify the canonical representation from the recovered pair laws.

## 7. Completion of the finite-sequence implication and refinements

Equality of the complete L_pair-site laws supplies all selected-pair moments through that length, so Section6 gives claim3 and hence claim1. Canonical equivalence gives full genealogy equality and therefore equality of every JC locus law, including claim4. All four claims are equivalent.

A sharper bound is available when the indexed rate lists and boundary sets for each pair are smaller than the generic JP+1 and J+1 counts. That is the mechanism behind the earlier fixed-family55-site calculation: its BB pair uses four rate factors and four boundaries, giving paired recurrence order56; the other pair types need fewer. The present distinct-rate reconstruction theorem is not a replacement for that earlier model-specific proof at coincident-rate cases.

## 8. Meaning, priors and limits

The identified object is the epoch/routing/rate representation modulo hidden population permutations. It is not an assertion that all biological network parameterizations are injective into that object. In particular Yang--Flouri's bidirectional parent-path swap gives exactly equal metric-genealogy laws and can correspond to within-model or cross-model biological ambiguity; it must remain in the quotient. The canonical target does not separately identify a chosen factorization of simultaneous pulse matrices, hidden unused populations, or invisible constant-rate boundaries.

The theorem compares ALL pairs inside the declared class. It does not claim that a generic model excludes every rate-colliding, rank-deficient or redundant competitor in the unrestricted bounded-network class. Full column rank, within-epoch distinct rates, visible separated boundaries and the two-copy sampling condition are explicit sufficient assumptions, not necessary conditions or a maximal-class theorem.

Classical ingredients include independence of distinct exponentials, symmetric powers of injective linear maps, nonnegative rank-one factor recovery, exponential-polynomial recurrences and compact moment determinacy. Their algebra is proved here rather than presented as new general methodology. Relevant priors include:

- Thawornwattana, Huang, Flouri, Mallet and Yang (2023), *Inferring the Direction of Introgression Using Genomic Sequence Data*, MBE40, msad178: https://academic.oup.com/mbe/article/40/8/msad178/7239274 . This is a direct biological precedent for selected-pair coalescence laws, sampling effects and introgression identifiability.
- Yang and Flouri (2022), *Estimation of Cross-Species Introgression Rates Using Genomic Data Despite Model Unidentifiability*, MBE39, msac083: https://academic.oup.com/mbe/article/39/5/msac083/6568285 . Its parent-path-switch equality for every metric gene tree is a genuine ambiguity retained here, not removed by the finite observation bridge.
- Allman, Matias and Rhodes (2009), *Identifiability of parameters in latent structure models with many observed variables*: https://arxiv.org/abs/0809.5032 . It provides broad prior context for latent-state algebraic identification and label ambiguity. Its HMM/tensor results are not asserted to imply this particular source theorem without an applicability proof.
- Jouniaux, Arredondo, Boitard, Chikhi and Mazet (2026), *Extending the IICR to complex nonstationary structured models*, Genetics232(4), DOI10.1093/genetics/iyag040: https://pubmed.ncbi.nlm.nih.gov/41668442/ . Its changing-dimension transition operators are a direct forward-model precedent. Only the primary abstract was obtained in this check, so no assertion is made about every theorem in the full paper.
- Liang and Terhorst (2026), *Computing coalescence rates for complex demographies and sampling configurations*, bioRxiv DOI10.64898/2026.04.09.717519: https://pubmed.ncbi.nlm.nih.gov/41993468/ . Its event-based coalescence calculations and local information analysis are pertinent prior tools; no new forward engine is claimed here.

A bounded search has not established novelty of this exact class-wide reconstruction/bound. No finite number of loci, stable numerical procedure, convergence guarantee, empirical model fit, continuous-migration/unknown-clock theorem, unrestricted-network identification, original G3/G4 solution or Lean verification follows.
