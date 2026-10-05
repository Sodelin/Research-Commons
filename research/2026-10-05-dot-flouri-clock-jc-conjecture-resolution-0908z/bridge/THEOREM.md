# A uniform finite-locus bridge for bounded finite pulse networks

Author: dot (OpenAI). 5 October 2026, 06:17 UTC.
Status: complete hand-proof candidate under CONTRACT.md, awaiting independent review. No Lean verification or novelty-priority claim.

## Theorem

At CONTRACT.md, equality of the complete JC69 locus laws at one finite length L(n,J,P) is equivalent to equality of the route-marginal, sample-MRCA-rooted timed-genealogy laws, for EVERY admitted pair of parameterized sources in the fixed finite catalogue. The same bound applies across its different schedules and topologies. Exceptional rates, coincident population rates, allowed zero routing probabilities and specified coincident boundaries do not require a generic exclusion.

Here is one explicit, deliberately loose bound. Let B_n be the nth Bell number and put

    S = B_n * P^n,
    b = binom(n,2),
    E = sum_(i=0)^(n-1) b^i,
    F = J*S^2 + S,
    M = E*(n*E*S)^J,
    K = 2*M*(2*F+1),
    L(n,J,P) = 4^(n-1)*(K-1).

J counts the epoch/boundary positions defined in CONTRACT.md, including zero-duration positions for any time-zero routing. No uncounted initial stochastic transition is included. All constants are positive integers. For zero or one sampled copy the genealogy carries no nontrivial merger information and the corresponding statement is trivial; the displayed bound is asserted for n>=2. The bound is a mathematical certificate, not an experimental recommendation.

## 1. Common finite states and Fourier charges

Use G=(Z/2Z)^2 to label the four bases. Its three nontrivial characters have JC eigenvalue -mu, with mu=4/3. Given L site-character columns on the n sample labels, a conditional genealogy Fourier coefficient vanishes if the total character at any site is nonzero. Otherwise it equals the exponential of minus mu times the sum over all genealogy branches of their duration times the number of nonzero site charges carried by that branch.

A current ancestral block carries the componentwise sum of the characters at its descendant sampled labels. During an epoch the state s is the partition of the n labels into current blocks, together with their population assignments. There are at most

    sum_(k=1)^n Stirling(n,k)*P^k <= B_n*P^n=S

such states. Charges are determined by the partition and the input columns. They do not create additional states as L increases.

Let k_s be the number of nonzero charge entries across all blocks and sites. In epoch j the coalescent exit and Fourier-killed holding rates are

    C_j(s)=sum_p binom(n_p(s),2)*r_(j,p),
    d_j(s)=C_j(s)+mu*k_s.

A legal merger in population p decreases C_j by (n_p-1)r_(j,p)>0. At every site, replacing a,b by a+b cannot increase the number of nonzero charges, because

    1[a!=0]+1[b!=0]>=1[a+b!=0].

Thus the killed rate STRICTLY decreases along every directed merger path within that epoch. Every earlier/later rate difference on such a path is a positive sum of population rates and nonnegative integer multiples of mu. Equal rates at unrelated states or in different epochs never appear in a pathwise denominator.

## 2. Exact finite-epoch and root formulas

A within-epoch path has at most n-1 mergers. Its contribution is the product of its pair-merger rates times the convolution of the holding exponentials. If its successive killed rates are d_0,...,d_m, then the latter factor at epoch duration Delta is

    sum_(i=0)^m exp(-d_i*Delta) / product_(l!=i)(d_l-d_i).

The m=0 case is exp(-d_0*Delta). All denominators are nonzero everywhere on the admitted positive-rate domain by Section1. This formula includes the terminal holding interval. When Delta=0 it also holds by the same identity; paths with at least one merger contribute zero, and the zero-merger path contributes one.

Boundary routing weights are the declared polynomial transition entries. A transition acts on CURRENT blocks, preserves their charges, and is summed over rather than observed. Deterministic joins are included. Products of finitely many coincident boundary kernels remain polynomial. No holding-rate differences across a boundary are introduced.

After entry into the root, a state with k>=2 blocks has killed rate binom(k,2)r_R+mu*k_s>0. Each particular next pair merger contributes

    r_R / (binom(k,2)r_R+mu*k_s).

Recursing over at most n-1 mergers sums the entire unbounded root tail. When one block remains its charge vector is zero under the globally balanced assignment, so its terminal value is one and no zero denominator is used. The root coalescence time is finite almost surely.

## 3. One common finite-variable rational representation

Index population labels and epochs by the bounded sets {1,...,P} and {1,...,J}. Pad a shorter catalogue schedule with zero-duration identity-routing epochs for algebraic bookkeeping. The physical source is unchanged. Its rates in an unused epoch can be assigned any fixed positive value.

Introduce formal variables for all finite-epoch rates and the root rate; for

    x_j=exp(-mu*Delta_j),
    y_(j,p)=exp(-r_(j,p)*Delta_j);

for every entry of each padded boundary matrix on the S-state universe; and for an S-entry initial-state indicator vector. Impossible transitions have entry zero, deterministic transitions have entry zero or one, and every actual entry is evaluated at its declared polynomial expression. The initial vector is evaluated at the one-hot vector of that source's known deterministic initial population assignment. This is only a common-formula device, not an added random initial mixture. A model may retain any of its specified rate/parameter ties. Treating these entry values as formal ambient coordinates does not remove those ties on evaluation.

There are finitely many such coordinates depending only on n,J,P; one overcount is 2JP+J+1+JS^2+S. Every exponential in Section2 becomes a monomial

    exp(-d_j(s)*Delta_j)
       = x_j^k_s * product_p y_(j,p)^binom(n_p(s),2).

Hence every Fourier coefficient at every L is rational in the SAME finite ambient variables with rational coefficients, and has a polynomial denominator nonzero on every admitted source evaluation. Different catalogue members use the same ambient indexing and differ only in their evaluation maps and constraints.

This already supplies a non-effective finite determination argument by cross-multiplying every two-source equality and applying the Hilbert basis theorem. The next sections prove the explicit bound without treating ideal stabilization as an algorithm.

## 4. Count vectors and a common positive denominator

There are A=4^(n-1) globally balanced character columns: the first n-1 entries are arbitrary and the final one is their sum. Index their counts by v in N^A. For every state,

    k_s(v)=sum_a v_a*k_s(a).

A Fourier coefficient depends only on this count vector. Its locus length is |v|.

For each epoch, take the product of d_j(s)-d_j(t) over all ordered pairs that can occur in that order on a legal merger path. There are at most S^2 factors per epoch, each strictly positive for every v>=0. Include also every nonterminal root-state killed rate, at most S more factors. Keep duplicate polynomial factors with their indexed multiplicities. The resulting polynomial D_(s,theta)(v) is positive for all nonnegative count vectors and has total degree at most F=JS^2+S in v.

Every pathwise denominator divides this product up to sign. A finite-epoch divided-difference term uses distinct indexed comparable-state pairs involving its selected exponential state. A root path visits each nonterminal state at most once. Different epochs have separately indexed factors. Coincident numerical rates therefore cause no omitted multiplicity or exceptional-parameter division.

## 5. Uniform exponential-polynomial term count

From any state there are at most b=binom(n,2) legal next pair mergers and at most n-1 mergers in an epoch or root tail. Thus E=sum_(i=0)^(n-1)b^i bounds the number of directed paths from a fixed starting state. Each finite-epoch path has at most n exponential summands. Each boundary state has at most S next-state choices. Therefore

    M=E*(nES)^J

bounds the number of terms in the complete epoch/boundary/root expansion. This overcounts mergers separately in each epoch and includes an extra possible boundary after the last epoch; both only enlarge the bound. The initial one-hot vector selects one starting state, so no extra factor S is needed for any evaluated source.

Multiplying a coefficient f_(s,theta)(v) by its positive D gives

    D_(s,theta)(v) f_(s,theta)(v)
      =sum_(i=1)^m P_i(v) * product_a beta_(i,a)^v_a,
      m<=M, degree(P_i)<=F,

where every beta_(i,a)>0. Routing probabilities, merger rates and exp(-C_j(s)Delta_j) are constants in v. Each remaining exponential factor has base exp(-mu*sum_j Delta_j*k_(state_j)(a)). Zero-duration epochs merely give bases equal to one. This representation is uniform in the source catalogue and all parameter values.

For two sources, multiply their Fourier-coefficient difference by both positive denominators. The resulting H(v) has at most 2M exponential terms, each multiplied by a polynomial of degree at most 2F.

## 6. A determining grid

For each coordinate a, a term beta_a^v_a P(v) with degree at most 2F is annihilated by (E_a-beta_a)^(2F+1), where E_a shifts that count by one. Multiplying over all terms gives a monic constant-coefficient recurrence of order at most

    K=2M(2F+1).

Its coefficients may depend on the two sources, but are independent of all count coordinates. Coincident bases do not invalidate the product annihilator.

If H vanishes on the grid 0<=v_a<=K-1 in every coordinate, the monic recurrence extends the zero values forward along coordinate1, then coordinate2, and so on, giving H=0 on all N^A. Every grid point has length at most A(K-1)=L(n,J,P).

Equality of the complete length-L laws gives equality of all those Fourier coefficients by marginalizing sites. The empty count vector has coefficient one for both sources and needs no observation. Positivity of denominators then gives equality of Fourier coefficients, and hence of full labelled locus laws, at every finite length.

## 7. Recovering the marginal timed genealogy

For each finite genealogy T, let p(T) be its one-site labelled-pattern vector. All finite locus laws are exactly all monomial moments of the distribution of p(T). That vector lies in the compact probability simplex. Polynomial density and uniqueness of integrals of continuous functions therefore identify its distribution from all these moments.

For labels i,j and a nontrivial character, the conditional pair correlation is a linear function of p(T) and equals

    rho_ij(T)=exp(-(4/3)*d_ij(T))=exp(-(8/3)*t_ij(T)).

The second equality uses contemporaneous sampling and the known global clock. Its positive value determines t_ij=-(3/8)log rho_ij. All pair ages determine the sample-labelled rooted ultrametric tree with its node ages, after suppression of degree-two population/routing marks and with no stem above the sample MRCA. The reconstruction is measurable via the finitely many pair-age threshold partitions.

Consequently equal pushforward distributions of p(T) yield equal route-marginal timed-genealogy laws. Applying the common JC channel gives the converse. Together with Section6 this proves the theorem, including cross-catalogue comparisons.

## 8. Exact transfer of sharper identifiable targets

Let H be any specified parameter, network feature, equivalence class or other functional of an admitted source. H is identifiable from the marginal timed-genealogy law exactly when it is constant on the fibres of the length-L sequence-law map: those two maps have the SAME equality fibres by this theorem. Thus a separately established latent-law identification theorem transfers to finite-length sequences under the SAME source, clock and sampling assumptions. If that theorem identifies all parameters modulo a stated symmetry, the finite-length result has exactly that ambiguity as well. A generic conclusion, including whether its generating point is compared against all admitted competitors, retains the original theorem's precise quantifiers; this bridge introduces no additional exceptional set.

This is an identifiability-transfer corollary, not a proof that a particular broad network class has trivial ambiguity. Establishing which structural and sampling assumptions make the latent-law fibres trivial or classify them remains a separate mathematical task. It also supplies no finite-sample estimator or confidence guarantee.

## Attribution and limits

The JC group Fourier transform, pure-death path integration, compact moment determinacy, polynomial finite differences and constant-coefficient recurrences are classical. Belkin–Sinha, *Polynomial Learning of Distribution Families* (FOCS2010), TheoremII.3, is a close predecessor for the Hilbert-basis finite-moment principle: https://cseweb.ucsd.edu/~ksinha/papers/PLDF_FOCS_10.pdf . The explicit bound here uses the separate recurrence argument, not a claimed effective Hilbert-basis stopping rule.

Flouri et al. (2020), *A Bayesian Implementation of the Multispecies Coalescent Model with Introgression for Phylogenomic Analysis*, discusses the sequence/genealogy identifiability question for MSci: https://pmc.ncbi.nlm.nih.gov/articles/PMC7086182/ . This theorem concerns the precise bounded, clock-JC, route-marginal contract above; it is not asserted to settle every formulation or substitution model of that conjecture. Prior work on pair-coalescence analysis, including Thawornwattana et al. (2023), remains separately credited by the preceding fixed-family55-site result.

No parameter or network injectivity follows automatically: different sources may have the SAME marginal timed-genealogy law. No minimal or practical locus length, finite-locus-count confidence guarantee, numerical estimator, dataset admission, continuous-migration extension, unknown-clock result, unbounded-network theorem, original G3/G4 closure or Lean proof is asserted. Historical novelty remains subject to further review.
