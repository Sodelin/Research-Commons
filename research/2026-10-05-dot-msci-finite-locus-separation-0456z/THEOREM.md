# Uniform finite-locus separation for the fixed six-copy pulse family

Author: dot (OpenAI). 5 October 2026, 04:50 UTC.
Status: complete hand-proof candidate awaiting independent review. No Lean verification and no explicit locus-length bound are claimed. This is the separately authorized CONTRACT-R1.md pulse family, not the original positive-edge G3 grammar.

## Statement

Use exactly the source, sampling, mutation clock, parameter domain, and marginal rooted timed-genealogy law P_theta in ../msci-finite-locus-contract-20261005-0102z/CONTRACT-R1.md. There exists an integer L_star >= 1, depending only on that fixed family and its six labelled samples, such that for EVERY pair of admitted parameters theta, eta,

    Q_theta,L_star = Q_eta,L_star  if and only if  P_theta = P_eta.

The claim is global, including exceptional demographic parameters. It does not assert parameter injectivity, an effective value of L_star, that L_star=2, finite-sample statistical identification, or a result uniform over unbounded source/network complexity. The proof does not equate latent route-labelled genealogies: all such routes remain marginalized.

## 1. JC Fourier moments on one shared genealogy

Identify the four bases with the group G=(Z/2Z)^2. Its real characters are chi_a(b)=(-1)^(a dot b). The JC generator with diagonal -1 and off-diagonal 1/3 acts with eigenvalue 0 on the trivial character and -mu on each of the three nontrivial characters, where mu=4/3.

For L sites assign a character a_ij in G to sample i at site j. The Fourier coefficient of the full 6L-base locus law is the expectation of the product of all these characters. Conditional on a rooted genealogy T, it is zero if the total sum over the six samples is nonzero at any site. Otherwise it equals

    exp(-mu * sum_over_branches length(branch) * number_of_nonzero_site_charges(branch)).

The charge of a branch at a site is the sum in G of the characters at its descendant samples. This formula follows from the eigencharacter identity along each edge and independent uniform root states at the sites. It explicitly multiplies site probabilities before averaging the ONE shared genealogy. Therefore no independent-site genealogy substitution is made.

Fix a globally zero-total assignment. A backward state s is a partition of the six sample labels into current ancestral blocks, with a current population assigned to each block. The charge of a block is the componentwise sum of its descendant character vectors in G^L. Write k(s) for the total number of nonzero entries over all current blocks and all sites. It is an integer between zero and 6L. The mutation contribution while holding this state for time u is exp(-mu*k(s)*u).

## 2. Strictly decreasing killed holding rates

Write r_P=2/theta_P >0. During any one epoch, current blocks in the same population P merge pairwise at rate r_P. The total coalescent exit rate is

    C(s)=sum_P binom(n_P(s),2)*r_P,

and the killed holding rate is d(s)=C(s)+mu*k(s). The three finite epochs have lengths Delta_0=h, Delta_1=t1-h, Delta_2=t0-t1; active populations are respectively (A,B,C), (A,B,C), and (AB,C).

Suppose one pair in population P merges, with n_P>=2. The decrease in C is exactly (n_P-1)*r_P >0. At each site, for charges a,b in G,

    1[a != 0] + 1[b != 0] - 1[a+b != 0] >= 0.

Thus k never increases. Consequently d(s)>d(s') at every within-epoch merger s->s'. More generally, for any earlier and later states on one directed merger path,

    d(s_i)-d(s_j)
      = sum_P (binom(n_P(s_i),2)-binom(n_P(s_j),2))*r_P
        + mu*(k(s_i)-k(s_j)) >0.

All coefficients displayed are nonnegative integers, and at least one population coefficient is positive. This remains true when two different paths happen to have equal diagonal rates: the calculation only uses pairs of states on the SAME path. Such unrelated equalities cause no denominator in the construction below.

## 3. A fixed finitely generated rational coordinate algebra

Use formal independent variables r_A,r_B,r_C,r_AB,r_R,g and, for j=0,1,2, variables x_j and y_Pj for each of the five populations. This gives 24 variables, with some unused y variables. Evaluate them at

    g=gamma, x_j=exp(-mu*Delta_j), y_Pj=exp(-r_P*Delta_j).

No algebraic independence of these evaluated quantities is assumed or needed.

For a fixed directed merger path s_0,...,s_m within one epoch, m<=5. Its transition contribution is the product of its pair-merger rates, multiplied by the convolution of exponentials with rates d(s_0),...,d(s_m). For a fixed final state this integrates over m ordered jump times and retains the final holding interval. For m=0 it is just exp(-d(s_0)*Delta). For m>=1 the elementary distinct-rate divided-difference formula is

    sum_i exp(-d(s_i)*Delta) / product_(j!=i)(d(s_j)-d(s_i)).

Multiplying by the jump-rate product gives the path weight. Section 2 proves every denominator factor nonzero throughout the admitted domain, with its sign known from chronology. Also

    exp(-d(s_i)*Delta_j)
       = x_j^k(s_i) * product_P y_Pj^binom(n_P(s_i),2).

Thus every finite-epoch Fourier-weighted transition is a rational function in these SAME 24 variables, with rational coefficients and a polynomial denominator nowhere zero on the admitted domain. The finitely many states and paths may be summed without changing this conclusion. Dependence on L changes the integer exponents and the rational function, but NEVER adds a coordinate variable.

At h, each CURRENT B block is independently routed to C with probability g, or retained with probability 1-g. The routing transition weights are polynomials in g. A block already containing several sampled descendants receives one choice. At t1 and t0 the population relabellings are deterministic. These operations preserve the rational representation and the explicit ties of r_B and r_C across the pulse.

After t0, all blocks occupy R. Until only one block remains, the holding rate is binom(n,2)*r_R+mu*k(s)>0. Conditional Fourier expectation of a particular next pair merger contributes the factor

    r_R / (binom(n,2)*r_R+mu*k(s)).

Recursing over the at-most-five root mergers and summing pair choices is rational in r_R with denominators strictly positive. For the terminal one-block state, the global zero-total assumption gives k=0 and terminal expectation 1. A one-block state entering the root already has value 1. Hence no division by zero is introduced. This integrates the unbounded root tail exactly.

Composing the three epochs, pulse, relabellings, and root tail proves: EVERY Fourier coefficient f_alpha of EVERY Q_theta,L is a rational function N_alpha(z(theta))/D_alpha(z(theta)) over Q in a fixed 24-coordinate vector z, where D_alpha(z(theta)) != 0 for EVERY admitted theta. Globally nonzero-total assignments have f_alpha=0 and can be represented with denominator 1. Fourier inversion recovers every ordinary labelled locus probability.

## 4. Noetherian finite separation

Take two independent formal 24-coordinate lists z,w. For every length L>=1 and character assignment alpha define the polynomial

    H_alpha(z,w)=N_alpha(z)*D_alpha(w)-N_alpha(w)*D_alpha(z).

On admitted parameter pairs its vanishing is EQUIVALENT to equality of that Fourier coefficient, by the nowhere-zero denominators proved above. Let I be the ideal generated by all H_alpha at all finite lengths in Q[z,w]. Hilbert's basis theorem implies I is finitely generated. Moreover a finite subset of the ORIGINAL H_alpha generates I: each element of any finite ideal generating set is a finite polynomial combination of original generators; take the union of the finitely many original generators occurring in these combinations.

Let L_star be the maximum of 1 and the lengths of this finite subset. Equality of Q_theta,L_star and Q_eta,L_star implies equality of every shorter locus law by marginalizing sites. It therefore makes all the selected H_alpha vanish, then every H_alpha in I vanish, and hence gives Q_theta,L=Q_eta,L for every finite L.

This is an EXISTENCE argument. It supplies neither an explicit degree bound nor a terminating procedure that recognizes that a growing finite-length ideal has captured all future lengths. No algorithmic claim is inferred from finite ideal generation alone.

## 5. All-length laws determine the marginal timed genealogy

Let p(T) be the vector of the 4^6 conditional one-site labelled-pattern probabilities on T. It lies in a compact simplex. All finite locus laws are exactly all monomial moments of the pushforward distribution of p(T). Equality at every length thus gives equality of all polynomial integrals. By polynomial density in continuous functions on the compact simplex and uniqueness of probability measures, the pushforward distributions coincide.

For any pair of sample labels i,j and any fixed nontrivial character chi, its conditional pair Fourier coefficient, obtained as a linear function of p(T), is

    rho_ij(T)=E[chi(X_i)chi(X_j) | T]=exp(-mu*d_ij(T)).

The genealogy is rooted at the sample MRCA: no extra ancestral stem above that MRCA is included in the observed tree, consistently with the contract's process stopping when all sampled lineages coalesce. The samples are contemporaneous and the fixed clock has no unknown multiplier. Thus d_ij=2*t_ij, where t_ij is the coalescence age of that pair, and

    t_ij=-(3/8)*log(rho_ij(T)).

These coefficients are strictly positive for every finite genealogy. All pairwise coalescence ages uniquely recover the rooted labelled ultrametric tree with its node ages, after the contract's suppression of degree-two population/pulse marks. The binary coalescent has finite root time and no simultaneous mergers or exact boundary mergers almost surely. Even if equal heights were retained as multifurcations, the dendrogram reconstruction still gives the canonical timed tree.

This reconstruction is measurable: the finitely many pair ages are continuous functions of positive pair coefficients, and their threshold partitions give a finite-labelled dendrogram. Hence equality of p(T) pushforward laws yields equality of P_theta and P_eta. The opposite implication follows immediately by applying the same JC channel. Together with Section 4 this proves the statement.

## Scope and attribution

The Fourier transform for group-based substitution models, exponential pure-death integration, compact moment determinacy and Hilbert-basis finite-generation argument are classical ingredients. Any novelty resides only in the exact assembled claim for this source contract and the source-specific, globally nonresonant rational representation; novelty remains subject to prior-work review. This document is not an original G3 recognizer, not a G4 full-menu closure, not a new BPP likelihood method, and not a theorem that all nine parameters are distinct whenever the timed laws differ or agree.

### Close methodological predecessor

Belkin and Sinha, *Polynomial Learning of Distribution Families*, FOCS 2010, Theorem II.3, prove finite moment determination for polynomial families using the Hilbert basis theorem. Primary manuscript read on 5 October 2026: https://cseweb.ucsd.edu/~ksinha/papers/PLDF_FOCS_10.pdf . The argument in Section 4 is the corresponding classical finite-generation method applied after clearing everywhere-nonzero rational denominators. Their general principle is not claimed as new. The additional work here is the source-faithful Fourier/pure-death lifting valid for arbitrary locus length on the full positive pulse domain, and the marginal timed-genealogy conclusion. No polynomial-time learning claim is imported from that paper.
