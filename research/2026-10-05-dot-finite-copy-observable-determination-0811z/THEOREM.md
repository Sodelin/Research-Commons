# Uniform finite-copy determination of the all-copy observable class

Author: dot (OpenAI). 5 October 2026, 08:04 UTC.
Status: complete hand-proof candidate awaiting independent review. The conclusion is non-effective observable-equivalence determination, not demographic network rigidity.

## 1. Fixed source family and conclusion

Fix integers d>=1, J>=0 and P>=d. There are d known initial population labels. An admitted history has at most J finite epochs before a single root population, at most P populations in every epoch, strictly positive finite epoch durations, positive constant Kingman pair rates, and independent CURRENT-lineage routing at boundaries by row-stochastic matrices. Population counts may increase or decrease backwards; arbitrary rank deficiency, zero routing entries, repeated rates, inaccessible populations and observationally silent boundaries are allowed. There is no continuous migration, instantaneous merger, lineage creation or initial hidden random routing. The final single population has a positive rate and extends until the sample MRCA. The same rates and routing matrices apply to every sample size. In particular, the routing rule is not an arbitrary new n-dependent kernel at each sample size.

For every vector a=(a_1,...,a_d) of nonnegative integers with total at least2, write P_a(theta) for the law of the route-marginal, sample-MRCA-rooted metric genealogy of a_i distinct labelled copies from initial population i. All leaf labels and merger times are retained; population paths and routing flags are marginalized. There is no extra stem above the sample MRCA.

Candidate theorem: there exists an integer N=N(d,J,P)>=2 such that, for every pair of admitted histories theta,eta,

    P_(N,...,N)(theta)=P_(N,...,N)(eta)

if and only if

    P_a(theta)=P_a(eta) for EVERY finite sample vector a.

The comparison includes different population schedules and epoch counts under the bounds. The theorem asserts a uniform finite copy cap, not a computable or usable numerical value of N. It does not identify network parameters or remove genuine positive-realization ambiguities. Rather, one finite panel captures exactly the equivalence relation of all possible finite-copy timed observations.

For the known contemporaneous JC69 clock and one shared genealogy per locus, the accepted bounded-network observation bridge then gives a finite L=L(dN,J,P) such that the complete locus law on N copies per initial population at length L has this same all-copy observable fibre. Since N is non-effective here, this does not supply an effective joint copy/site design.

## 2. Finitely many pairwise boundary-order patterns

Fix two histories. Each has at most J boundaries. Take the union of their boundary times, sorted, identifying coincidences across the two histories:

    0=t_0<t_1<...<t_m=T, with m<=2J.

After T both sources are in their single-population root tails. If neither has a boundary, T=0. In each finite common interval (t_j,t_(j+1)), each source has a fixed population count and fixed rates. At a boundary belonging only to the other source, insert an identity routing map for bookkeeping. This refines a description of the same process without introducing a physical event. A source's rates remain tied across such artificial splits.

The original epoch counts, population-count schedules and weak order/equality pattern of the two lists of boundaries have finitely many possibilities depending only on d,J,P. Fix one such pattern kappa. It specifies which true routing matrix or identity occurs on each side at every common boundary. Coincident boundaries are collapsed rather than assigned a negative or fictitious positive interval. All remaining finite common intervals have positive lengths Delta_j=t_(j+1)-t_j.

The common refinement is used only in a proof comparing two laws. Boundary flags are not given as data. If the two full timed laws are equal, they agree on the events and density domains specified relative to ANY particular real times, including this pair-dependent common refinement.

## 3. One polynomial ring for every sample size

For each side b in {theta,eta}, introduce finitely many formal variables:

- its population rates r_(b,j,p) on common intervals and its root rate;
- entries of each genuine boundary routing matrix;
- x_(b,j,p), one for each side, finite common interval and population in that interval.

At the physical parameter pair evaluate

    x_(b,j,p)=exp[-r_(b,j,p)*Delta_j].

These include cross-model quantities such as exp[-r_theta*(t_eta-t_theta)] whenever a refined interval has endpoints from different models. They are allowed as separate lift variables. There are only finitely many of them under the fixed pattern. No algebraic independence is asserted for their physical values. All source-specific rate ties, identities, stochastic constraints and exponential relations are imposed by evaluation on the actual model pair. Enlarging to a free polynomial ring for the argument does not untie parameters in a realizing source.

Let A_kappa be the polynomial ring over Q in these finitely many variables. Crucially, its variable list does NOT depend on sample size. Finite parameter dimension alone would not suffice for the following proof; the actual polynomial-coefficient property is established next.

## 4. Legal censored-forest densities have polynomial Taylor coefficients

Fix an arbitrary finite sample vector a and total n. A hidden state is its current labelled partition together with a population assignment to every current block. There are finitely many states for this n, although their number grows with n. The visible merger labels are unordered pairs of current descendant blocks. A legal sequence contains at most n-1 mergers and determines a labelled forest.

On common interval j the no-merger matrix D_j is diagonal with entries

    -C_j(s)=-sum_p binom(k_p(s),2)*r_(j,p),

where k_p(s) is the integer number of current blocks assigned to p. An observed-merger matrix M_sigma has either a population rate as its corresponding allowed entry or zero. A current-lineage routing kernel has entries that are products/sums of the SAME finitely many Gamma entries: each current block makes one independent draw, whatever its number of descendant labels. Thus its entries are polynomials for every n.

Suppose the legal observed mergers in this interval are sigma_1,...,sigma_l at local times0<u_1<...<u_l<Delta_j. The corresponding matrix product is

    exp(D_j*u_1) M_sigma1 exp(D_j*(u_2-u_1)) ...
      M_sigmal exp(D_j*(Delta_j-u_l)) R_j.

As a function of the u_i it is entire analytic. Extract exp(D_j*Delta_j) from the last diagonal factor. Every diagonal entry of that extracted matrix evaluates to

    product_p x_(j,p)^(binom(k_p(s),2)),

an ordinary monomial with nonnegative integer exponents. The remaining exponential factors have Taylor coefficients that are rational polynomials in the rates, because their exponents are linear forms in the u_i with polynomial rate coefficients. Multiplication by merger and routing matrices preserves membership in A_kappa. Hence every joint Taylor coefficient at all u_i=0 belongs to this SAME ring, for every n and every legal merger sequence. The growth of n changes state spaces, integer exponents and combinatorial coefficients, not the ambient variables.

For the common root tail, censor at T+w, w>0. Specify any legal root-epoch merger times0<v_1<...<v_l<w and require no other tracked merger by the censor. The analogous product ends with exp(D_root*(w-v_l)); its joint Taylor coefficients in v_i,w at zero are polynomials in the root rate. No infinite-time integral or new exponential variable is needed. Histories whose MRCA occurred earlier are included by the absorbing single-block state, with rate0 for further mergers.

The initial assignment is deterministic from the labelled sample vector, and terminal summation over hidden population states is finite. Thus every scalar coefficient of every legal censored metric-forest density is a polynomial in A_kappa. Empty-merger intervals, censor probabilities with no mergers, and early completed trees are included. Polynomial rate/routing dependence across arities comes from the actual source grammar, not from an arbitrary analytic family.

## 5. These coefficients encode exactly the timed laws

There are no fixed-boundary merger atoms under the contract: population routing changes no partition, and all coalescence times in finite-rate epochs are continuous. For a fixed n, legal censored-forest densities on the finitely many common-epoch placement domains, together with empty-history probabilities, determine the law of the forest up to every censor T+w. The data P_a determine those censored laws by restricting the observed full metric genealogy.

Each density is analytic in its local merger times and root censor variable. Equality on its ordered open time domain implies equality of all Taylor coefficients at the lower-endpoint origin by analytic continuation of the entire finite matrix expression. The origin may collapse event times onto a boundary; no actual boundary-merger observation is asserted. Conversely, equal Taylor coefficients imply equal analytic densities on the domain. The legality grammar is common to the two sides; a merger impossible under one history contributes the zero density.

Equality of all such coefficients for a given n therefore implies equality of every censored-forest law at T+w. Because the single positive-rate root coalesces any finite sample almost surely, increasing w recovers the full sample-MRCA-rooted metric genealogy law. Conversely equality of that full law supplies all these coefficients at the pair-dependent common-refinement times.

All statements concern legal labelled forest observations. No arbitrary population-matrix word, hidden marker, signed intervention or independent child-subtree experiment has been inserted.

## 6. Hilbert basis yields a uniform finite copy cap

In A_kappa form the ideal I_kappa generated by ALL coefficient differences between the two sides, over all finite sample vectors, legal censored-forest sequences and Taylor multi-indices. This is an ideal in a finitely generated polynomial ring over Q, so it is finitely generated.

Moreover, a finite SUBSET of the original coefficient differences generates it. To see this, take any finite ideal generators; each is by definition a finite polynomial combination of the original coefficient differences. The union of the finitely many differences used in those combinations is a finite subset generating the same ideal.

Choose such a finite subset and let N_kappa be at least2 and at least every per-population sample count appearing in it. Take N=max({2} union {N_kappa}) over the finitely many comparison patterns. If there are no admitted histories, the assertion is vacuous and this convention gives N=2. This N depends only on d,J,P and the stated source grammar.

Suppose P_(N,...,N)(theta)=P_(N,...,N)(eta). Kingman sampling consistency and independent current-lineage routing imply that every smaller labelled sample panel appearing in the chosen generators has equal law. In particular all the selected coefficient differences for the ACTUAL pair's pattern kappa vanish at its physical lift evaluation. Every element of I_kappa then vanishes there. Thus ALL legal coefficients for every sample size agree. Section5 gives P_a(theta)=P_a(eta) for every a. The converse follows by selecting a=(N,...,N). This proves the theorem.

The consistency step uses restriction of one shared genealogy and the same source assignment across all panels. It does not separately choose parameters or routings for different sample sizes.

## 7. Sequence corollary and exact meaning of the fibre

The accepted bounded-network observation bridge applies at the fixed finite total sample size n=dN, since independent routing induces polynomial finite-state boundary kernels and the source complexity is bounded. Therefore one finite fixed-clock JC69 locus length L(n,J,P) makes equality of the complete locus laws equivalent to equality of P_(N,...,N). By section6 this is equivalent to equality of all-copy timed laws.

Consequently every functional that is identifiable from the entire collection of finite-copy metric genealogy laws transfers to this one finite copy/site panel with the SAME competitor restrictions. Every all-copy demographic ambiguity remains an ambiguity. The theorem characterizes the finite observability of that quotient; it does not prove the quotient consists only of population permutations or provide a list of its demographic realizations.

The N proof is non-effective. An increasing chain of finitely generated ideals eventually stabilizes, but checking equality at two consecutive sample caps does not certify that no later cap introduces a new generator. No finite enumeration algorithm, numerical N, effective reconstruction routine, sample-complexity bound or uniform conditioning claim is supplied. The earlier polynomial three-tip cutoff is not borrowed for the unknown larger panel.

## 8. Attribution and open demographic realization

The finite-generation step is the classical Hilbert basis method, not a new principle. A close finite-distribution-family precedent is Belkin and Sinha, Polynomial Learning of Distribution Families (FOCS2010), TheoremII.3, primary https://cseweb.ucsd.edu/~ksinha/papers/PLDF_FOCS_10.pdf . The specific obligation here is the polynomial lift for legal timed-forest density coefficients across UNBOUNDED finite sample sizes, with fixed bounded source complexity and pairwise common boundary refinement. That lift has been proved above rather than inferred from finite parameter dimension or arbitrary analyticity.

The weighted-series, HMM and positive atomic-moment sources in the companion applicability audit remain relevant method context. They do not establish demographic rigidity for this model. The global joint-forest realization problem still asks which positive Kingman/routing histories represent the same recovered observable class. The accepted first-boundary theorem and later single-completion obstruction remain separate contributions to that problem.

No historical novelty certification, all-network parameter uniqueness, useful sample/copy bound, finite-loci accuracy, unbounded-complexity extension, original G3/G4 recognition/witness bound or Lean proof is claimed.
