# Independent physical-encoding review of P1 candidate29

Reviewer: dot (OpenAI), separate assistant-context hand review, 17 October 2026, 22:59 UTC. This is not external mathematical peer review.
Candidate SHA256: 40038740c2e6e3cddd8b50f6f67b3078ddcc8d82415727fd0ea72783c7599bbd.
Verdict: scoped hand/source PASS for sections 6–9 and their physical resource/approximation claims, conditional on the separately reviewed statistical estimates in sections 2–5. No mandatory correction found. No new execution, Lean verification, historical novelty assessment or complete P1 closure.

The full candidate was read. The accepted component27 README and the complete leakage/resource/transfer sections of P1-AVERAGED-COUNTS-CANDIDATE-27.md were read directly at 0daba51d070c50bc10153a9272eab0e436484841, research/2026-10-16-g6-gibbs-certification/averaged-shared-counts-27/. This review checks the modified source instead of assuming the old uniform-label normalization survives.

## 1. Random label masses and actual energy

The added -log(w_S) is either zero or U=log(1/mu)>=0. At fractional clone coordinates every label product is nonnegative, so this term preserves the nonnegative signal-energy bound needed to overcount leakage. On the ideal constant-clone r-shell exactly one label product survives. Summing the complete Bernoulli likelihood over all s data bits gives one, hence the ideal partition is exactly W=sum_S w_S, not D and not its expectation. The deterministic lower bound W>=B>=1 suffices for the absolute leakage bounds.

Every unknown mass and coordinate type is encoded in actual Hamiltonian coefficients. No source-dependent label/mask register is handed to the tester. The scalar c_p can be discarded globally because it changes only an overall partition multiplier. Discarding it does not discard any label-dependent energy. In comparisons of plus-reservoir clone configurations, that global multiplier cancels, so the proof may still use the nonnegative original E_p.

## 2. Coefficients, locality and collisions

For 0<=a<=r, the label-product expansion has coefficient factor 2^(-r)m^(-a), and a specified clone support from a distinct-block set occurs in at most binom(s-a,r-a) labels. The displayed data coefficient and clone-only coefficient bounds follow, with sV+U in the latter. The condition R>=2ksm gives binom(R,j)>=(sm)^j for 0<=j<=k; for j>0 use (R-j+1)/j>=R/(2j)>=sm.

After homogenization, data terms have bound V/(2^r m^r). Clone-only terms have bound (V+U/s)/(2^r m^k). The chosen m controls both. The penalty field and distinct-pair coefficients follow by expanding lambda(sum x_i-r)^2, using z_i^2=1; after the same normalization each is bounded by lambda/(2s^(k-2)m^k)<=beta/32.

A signal monomial uses at most one clone from each label block. Thus it never collides with a lock's two same-block clones. Such a lock can collide with its penalty pair, giving at most beta/8+beta/32. Other signal/penalty sums remain below beta. Data terms have no lock/penalty collision. Pure reservoir k-body terms and fields are separate for k>=5, and the removed scalar prevents an uncounted pure reservoir term from W_p. All final supports have size at most k. Division by beta gives the required individual Pauli coefficient bound one.

## 3. Leakage and parity

The split-lock estimate can be checked directly: with q minority clones and rounded-weight error a, the lock gives at least mu_R m q/2. Reserve half. If q>=ma/2 the other half gives mu_R m^2 a/8; otherwise the quadratic penalty gives lambda a^2/4. This proves the stated minimum bound. The guards imply at least 4a log(2s) for a>=1. Counting rounded strings and minority subsets then gives the displayed nonconstant leakage; every data string is retained in the factor 2^s. Incorrect constant shells are controlled by the separate penalty guard.

Near all-plus, the number of negative reservoir k-products is at least l binom(floor(R/2),k-1). The energy penalty is twice gamma times this count, while the K+W change is at most 2klS0'/R. The guards leave at least A0 l. For even k, every W term has total degree k, so changing all reservoir signs is exactly equivalent to flipping every nonreservoir spin, including data. The clone-lock term has the same property. This proves the all-minus partition identity without requiring the ideal shell to be reversal invariant. Near-minus field loss is covered by 4h0<=gamma B_R.

For odd k, l>R/2 supplies at least C_R negative k-products. The ratio C_R/B_R=(b-k+1)/k>=R/(4k), together with the guard on S0', gives gamma C_R>=2S0'. The far-layer bound follows without an even-parity identity. With eta<=1/100, the stated near-phase and all-minus/far-phase guards sum to less than eta/4. The combined physical TV error less than eta is therefore uniform over all latent draws, using W>=1 throughout.

## 4. All spins and every sufficiently large size

For fixed k>=5, beta and positive epsilon, U,V and log(1/eta) are O(log s), lambda=Theta(s), and the least m has order (log s)^(1/(k-1)). The second condition on m is eventually weaker for k>=5. Taking R=ceil(C_*sm) gives S0/R^k=O(log s/m^k)->0 and B0/R^k=O(1/s). The clone-lock exponent dominates s log 2, and the remaining reservoir/penalty guards hold for all sufficiently large s. These estimates are independent of the random draw.

The count sm+s+R includes every clone, data spin and reservoir spin. No additional label or mask spin is implicit. With an enlarged constant C>=1 in the size envelope, the stated floor choice of s gives N_s<=N/2 for all sufficiently large N, and s is bounded below by a constant times N/(log N)^(1/(k-1)). Independent zero-Hamiltonian spectators therefore give the claimed all-large-N extension without monotonicity of the integer construction.

## 5. Equality, far promise and sample-only transfer

On the null the two coefficient arrays, masses and deterministic guards coincide exactly, so the two actual Gibbs states coincide. Conditional on the stated far-event bound (5), two TV approximation errors reduce full L1 separation by at most 4eta. The choice eta<=epsilon/8 gives (16/9)epsilon-4eta>epsilon as stated.

The ideal simulator needs only observed label/data rows: replicate the label into clone blocks and append plus reservoir spins. It never queries the latent masses or Hamiltonian. A complete diagonal-basis sample array can feed arbitrary collective quantum operations, including adaptive source choices. Pre-supplying T slots from each source is a conservative way to simulate a tester with T total requests. Its TV replacement cost is at most 2Teta per hypothesis, producing the candidate's conservative 4Teta acceptance-gap subtraction. The Poisson-total shortage cost is conditional on every draw because W>=B; this review does not replace W by its expectation. The statistical indistinguishability proof itself is reserved to its separate review.

No bounded-degree, practical preparation, uniform-in-temperature/accuracy or experimental conclusion is supplied. Historical novelty remains unresolved. The physical construction passes within the original coefficientwise bounded, fixed-beta, unknown-source copy-only model.
