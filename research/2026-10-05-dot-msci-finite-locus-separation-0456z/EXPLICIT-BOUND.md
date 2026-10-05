# A constructive, extremely loose locus-length bound

Author: dot (OpenAI). 5 October 2026, 04:55 UTC.
Status: separate unreviewed hand-proof candidate. It supplements, and does not overwrite, THEOREM-CANDIDATE.md. No practically usable sampling guarantee or Lean verification is claimed.

## Claim and constants

At exactly CONTRACT-R1.md, a valid finite determining locus length is at most

    L_bound = 748902056957898604139213494218915309705755648.

This deliberately immense bound is a constructive worst-case certificate, not a proposed locus length for an experiment. A sharper bound, small-L identification, numerical conditioning and sample complexity remain separate.

Define

    S = 203 * 5^6 = 3171875,
    E = sum_(m=0)^5 15^m = 813616,
    F = 3*S^2 + S = 30182376218750,
    M = 64*E*(6*E)^3 = 6057754198156904684285067264,
    K = 2*M*(2*F+1) = 731349664997947855604700677948159482134528,
    L_bound = 1024*(K-1).

These constants bound states, merger paths, denominator degree, exponential terms, recurrence order, and the total length of a determining grid, respectively.

## 1. Site-column counts

The group G=(Z/2Z)^2 has exactly 4^5=1024 six-label charge columns whose total is zero: the first five charges are arbitrary, and the sixth is their sum. Index these columns by a=1,...,1024. A Fourier coefficient with a nonzero-total column vanishes identically and needs no testing. Every other coefficient is determined by its count vector n in N^1024, since sites are exchangeable conditional on the shared genealogy. Its total locus length is |n|.

For any population-partition state s, the mutation reward is

    k_s(n) = sum_a n_a*k_s(a),

where each k_s(a) is a nonnegative integer at most six. The state itself, including descendant label blocks and their populations, does not depend on n or L. There are Bell(6)=203 possible set partitions; assigning one of five populations to each of at most six blocks yields at most S states. Unreachable assignments may be retained for this upper bound.

## 2. One common denominator polynomial in the counts

At each of the three finite epochs, consider every ordered pair (s,t) of distinct states that can occur in this chronological order on a within-epoch merger path. The state t is a genuine coarsening through legal same-population mergers. Include the factor

    d_s(n)-d_t(n) = C_s-C_t + mu*(k_s(n)-k_t(n)).

There are at most S^2 such factors per epoch. The prior proof's charge inequality implies their coefficients of each n_a are nonnegative, and C_s-C_t>0 on the positive population-rate domain. Consequently each factor is strictly positive for every n in N^1024, including n=0. Do NOT include differences of unrelated states.

Also include d_s(n)=binom(b_s,2)*r_R+mu*k_s(n) for every root-population state with b_s>=2 blocks, at most S factors. These are positive including at n=0. Let D_theta(n) be the product of all these indexed factors, evaluated at theta's population rates. Identical polynomial factors occurring at different indexed pairs are retained with multiplicity. Its total degree in n is at most F, and D_theta(n)>0 for every n in N^1024.

Every denominator in the finite-path formulas divides D_theta(n), up to sign: a partial-fraction term uses distinct earlier/later pairs involving its chosen state on that path; root paths visit each root state at most once; epochs have separate indexed factors. This divisibility statement is in the polynomial ring in n with real coefficients after fixing theta. It remains valid when two indexed factors coincide, since their indexing retains the needed multiplicities.

## 3. Uniformly finite exponential-polynomial representation

There are at most 15 possible pair mergers from a state and at most five mergers along a genealogy, so the number of paths of any allowed length from a fixed state is at most E. One finite-epoch path contributes at most six exponential terms by the divided-difference formula. Pulse routing has at most 2^6=64 outcomes. The root-tail recursion has at most E merger paths. Thus the entire three-epoch/pulse/root calculation has at most

    M = 64 * (6E)^3 * E

terms before collecting equal terms. This is conservative: it allows five mergers independently in each epoch although a six-label genealogy can only have five in total.

After multiplication by D_theta(n), each term is a polynomial in n of total degree at most F, times an exponential monomial in n:

    D_theta(n)*f_theta(n)
      = sum_(j=1)^m P_theta,j(n) * product_a beta_theta,j,a^n_a,
      m <= M, degree(P_theta,j) <= F.

Indeed the factors exp(-C_s*Delta) and merger rates/routing probabilities are constants in n, and each selected finite-epoch exponential contributes

    exp(-mu*Delta*k_s(n))
      = product_a exp(-mu*Delta*k_s(a))^n_a.

All beta_theta,j,a are strictly positive (possibly equal to one). No new bases, state types, or denominator factors are introduced by increasing L.

For two parameter vectors theta,eta, clear both denominators to obtain

    H(n)=D_eta(n)*D_theta(n)*(f_theta(n)-f_eta(n)).

It has at most 2M exponential terms, each multiplied by a polynomial of total degree at most 2F. Equality H(n)=0 is equivalent to equality of the original Fourier coefficients at that count vector because both denominators are positive.

## 4. A finite determining grid by recurrences

Let E_a denote the unit forward-shift operator in coordinate n_a. For a fixed exponential term with base beta_a in that coordinate and polynomial degree at most 2F,

    (E_a-beta_a)^(2F+1)

annihilates that term. This follows from the elementary finite-difference identity for polynomials after factoring out beta_a^n_a; beta_a>0. Multiplying these annihilators over at most 2M terms gives, for each coordinate, a monic constant-coefficient recurrence of order at most K. Equal bases cause no problem: the product remains an annihilator. Coefficients depend on theta,eta, but the order bound does not.

A sequence obeying a monic recurrence of order q<=K is determined forward by its first K values. Therefore if H vanishes on the integer rectangular grid

    0 <= n_a <= K-1 for every a=1,...,1024,

it vanishes on all of N^1024: extend along the first coordinate using its recurrence, then the second, and so forth through all 1024 coordinates. At every stage the recurrence coefficients are independent of the other counts.

Every grid point has |n|<=1024*(K-1)=L_bound. Equality of the length-L_bound locus laws gives equality at all these count vectors by site marginalization. The n=0 coefficient is the empty product 1 under both sources, so it is automatically equal and adds no observation. The recurrences give equality of every finite-length Fourier coefficient; inverse finite Fourier transforms give equality of all finite-length locus laws. The all-length moment and clock-JC tree-reconstruction argument in the existence proof then gives P_theta=P_eta.

## Evidence boundaries and attribution

This is an elementary exponential-polynomial/linear-recurrence strengthening of the separate Hilbert-basis existence proof. Finite differences, constant-coefficient recurrence uniqueness and exponential-polynomial representations are classical. It is not a claim of methodological novelty. Its useful contribution, if accepted, is the explicit fixed-contract uniform bound and its source-faithful denominator/state accounting. It does not decide the original arbitrary-size G3 source fibre, the full G4 legal-menu question, or nine-parameter injectivity.
