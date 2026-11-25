# One diverging physical-time sample per cutoff: an exact conditional gap criterion

Status: elementary spectral hand proof; no new Lean verification. This replaces an all-time bound by a diagonal-time requirement **conditional on a continuum reconstruction**. No bound for the actual weak-coupling Wilson theory is established.

## Setup

Take a sequence of lattice spacings a_n -> 0 with volume sent to infinity along the same sequence, or any sequence on which the following physical-time limits have been proved. For each j in a countable family take a vacuum-orthogonal physical vector v_{j,n}. Its zero-temperature positive-transfer-matrix autocorrelation at lattice time k a_n is C_{j,n}(k a_n). Assume finite nonnegative spectral measures so C_{j,n}(t)=int exp(-t E) d mu_{j,n}(E) on the lattice time mesh (a zero transfer eigenvalue contributes nothing at positive times). Units are physical: E = -log(lambda)/a_n, with the vacuum eigenvalue normalized to 1. This is not an assertion of a spectral representation for raw periodic-time traces.

Fix a physical anchor s>0 and set s_n=a_n floor(s/a_n), also positive for n large. For each fixed positive t used below, assume convergence of C_{j,n} at s_n and at s_n+a_n floor(t/a_n) to the corresponding reconstructed vacuum-orthogonal continuum autocorrelations. Write C_j(s)>0 for each nonzero channel. The continuum vectors v_j are assumed to have dense linear span in the vacuum-orthogonal space. No uniform upper bound on unanchored C_{j,n}(0), rate of convergence, or lower bound on spectral overlaps is assumed.

## Criterion

Under those assumptions the continuum Hamiltonian satisfies H >= g on the vacuum-orthogonal space iff there is a single sequence of physical times T_n in a_n Z, T_n -> infinity, with, for every j,

    liminf_n -log[C_{j,n}(s_n+T_n)/C_{j,n}(s_n)] / T_n >= g.

Zero numerator is allowed with rate +infinity. The denominator is eventually positive for each fixed j. This is an existential common time sequence, not a statement for every diverging time sequence.

**Sufficiency.** Normalize the positive measure by weighting it with exp(-s_n E) and dividing by C_{j,n}(s_n). For 0 < u_n <= T_n on the mesh, Jensen for x -> x^(u_n/T_n) yields

    C_{j,n}(s_n+u_n) / C_{j,n}(s_n)
      <= [ C_{j,n}(s_n+T_n) / C_{j,n}(s_n) ]^(u_n/T_n).

Take u_n=a_n floor(t/a_n) for arbitrary fixed t>0. The liminf assumption and convergence give C_j(s+t)/C_j(s) <= exp(-gt). If the continuum normalized tilted spectral measure charged [0,g-epsilon] by any amount b>0, its Laplace transform would be at least b exp(-(g-epsilon)t), a contradiction as t -> infinity. The anchor tilt is strictly positive at every finite energy, so E_H([0,g)) annihilates each v_j and hence their dense linear span. This proves the operator assertion, not merely a one-channel bound.

**Necessity.** At t=m in physical units, the continuum ratio is at most exp(-gm). For each integer m, by convergence and positivity of the finitely many denominators, choose n_m strictly increasing so that for all n >= n_m and j<=m the corresponding lattice ratio at duration a_n floor(m/a_n) is <= 2 exp(-gm), and a_n<1. Take m(n)=max{m:n_m<=n} and the corresponding lattice duration T_n. For fixed j the inequality eventually holds, and the rate is at least (gm(n)-log 2)/T_n, with lower limit >=g. No quantitative lower bound for m(n) results.

## Sharp limit-order obstruction

Let a_n=1/n, with a centered channel having spectral measure delta_2 + exp(-n) delta_1. At every fixed physical time it converges to a pure energy-2 channel; the lattice spectral bottom is 1 at every n. With any fixed positive anchor, the endpoint rate tends to 1 at T_n=n^2, but to 2 at T_n=floor(sqrt(n)) (both times are on the mesh). This verifies both that a uniform lattice Hamiltonian gap of size g need not be necessary for a continuum gap of size g, and that an excessively long prescribed sample can detect a disappearing overlap rather than the continuum spectrum. An isolated channel with a clean plateau cannot certify density of the channel family.

## Consequence for the route

The missing input can be separated into (i) fixed-time reconstruction and density for a countable family of physically smeared gauge-invariant states and (ii) one joint diagonal-time relative-decay estimate at a common g>0. For (ii), even a channel-dependent prefactor exp(o_j(T_n)) in the relative upper bound is enough. A bounded physical-time replay, a one-plaquette conditional Haar estimate, or a fixed lattice-time gap at fixed coupling provides neither input. The diagonal criterion is spectral bookkeeping, not evidence that Yang–Mills satisfies it.

Classical ingredients: positive Wilson transfer matrix, [Osterwalder–Seiler](https://doi.org/10.1016/0003-4916(78)90039-8); continuum target and clustering distinction, [Jaffe–Witten](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf). No novelty claimed for the spectral ingredients.
