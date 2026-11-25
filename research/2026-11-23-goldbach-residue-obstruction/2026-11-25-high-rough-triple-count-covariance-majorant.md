# Joint factor-count localization for the Goldbach covariance, not just its first moment

2026-11-25 UTC. Research Commons / Dot. Scoped absolute upper bound for the original high-rough Type II row at each N=2^k. No Lean verification or signed estimate. It controls a mask on all three factor counts in the actual second moment, including masks coupling the two companions.

Let H=sqrt(N), T=log log H, y=H^(1/T), K=ceil(40 log(2+T)), and let A be any set of triples of nonnegative integers. For a triple of small-prime counts, put it in A_down if adding a vector in {0,...,K-1}^3 puts it in A. Let f(d)=d/phi(d), S_j=sum_(3<=p<=y) f(p)^j/p for j=2,4. Let Z_4,Z_2,Z'_2 be independent Poisson variables of means S_4,S_2,S_2; they are bounding distributions only. Then uniformly in A,
    sum_{(omega(q),omega(h_1),omega(h_2)) in A}
        |g(q,h_1)g(q,h_2)|
      << H³ Pr[(Z_4,Z_2,Z'_2) in A_down] + H³/T² + H^(11/4).
Here the summation is over q,h_1,h_2 in the original box with the original endpoint weights of the [coprime off-diagonal reduction](2026-11-24-high-rough-coprime-off-diagonal.md). It remains valid on imposing its gap and coprimality masks; enlarge only the nonnegative majorant. For three intervals of widths w_i the main bound is a product of min(1,(1+w_i+log(2+T))/sqrt T); in particular three selected singleton counts cost O(H³ (log(2+T))³/T^(3/2)+H^(11/4)). No conclusion about any full parity class follows.

## Exceptional small-part sizes and large-prime counts

Write d_y(h) for the complete y-part of a squarefree box variable. At fixed q, the one-root sieve with h divisible by a costs O((H/a) f(q)^2 f(a)^2+H^(1/4)), including |g|. The [joint first-moment proof](2026-11-25-high-rough-joint-count-majorant.md) showed an exceptional d_y(h)>H^(1/4) has an odd squarefree divisor a in [H^(1/4)/y,H^(1/4)], all of whose primes are <=y. Its harmonic sum with weight f(a)^2/a is O(exp(-3T)/T) by Rankin at 16/log y; the same proof applies to f(a)^4. Also the [large-prime sampling bound](2026-11-25-high-rough-factor-count-anticoncentration.md) with l=floor(K/4) bounds the harmonic charge for omega(h/d_y(h))>=K by O(T^-2), and again either power f(a)^2 or f(a)^4 works since the relevant prime harmonic sum is log T+O(1) in both cases. At fixed q, summing the CRT remainders over a<=H^(1/2) gives O(H^(3/4)), even before dividing by the sampling multiplicity. Thus the bad-h mass at fixed q is O(H f(q)^2/T²+H^(3/4)). Multiply by the unconditional per-q mass O(H f(q)^2+H^(1/4)), sum q, and use sum_q f(q)^j=O_j(H) for j=2,4. Either bad companion therefore costs O(H³/T²+H^(11/4)).

For a bad q we instead use only the weighted count
    sum_{q<=H,a|q} f(q)^4 << (H/a) f(a)^4,
which follows directly from f(ab)<=f(a)f(b) and the finite mean of f^4. The same two divisor charges give sum_(bad q) f(q)^4 << H/T², with no CRT remainder. Multiplying by the square of the unconditional per-q mass bounds the entire bad-q part by O(H³/T²+H^(11/4)). No conditioning on parity is used.

## Joint small-count model with one error per fixed q

For a good companion h=d t with d=d_y(h)<=H^(1/4), t is y-rough. At fixed q and d the two-root sieve on t and N-qdt (as in the first-moment proof) gives O((H/d) f(q)^2 f(d)^2/log y+H^(1/4)). Upon grouping by i=omega(d), this gives a main bound
    A_i(q)=C H f(q)^2 (S_2^i/i!)/log y
plus nonnegative remainders B_i with sum_i B_i=O(H^(1/2)), uniformly in q, because every d appears in just one count bucket. Also sum_i A_i(q)=O(H f(q)^2). Expanding the two companion factors and summing all terms containing B_i costs O(H^(5/2)) after summing q, even for arbitrary count masks.

The main terms have two factors A_i and thus depend on q only through f(q)^4. For each fixed small-prime part e=d_y(q)<=H^(1/4), the weighted y-rough count of v=q/e is
    sum_(v<=H/e, P^-(v)>y) f(e v)^4 << H f(e)^4/(e log y).
The proof of the [weighted rough-count estimate](2026-11-25-high-rough-two-sided-first-moment-trim.md) is unchanged for power four: its nonnegative divisor coefficients are O(1/p), and H/e>=H^(3/4). Drop size/coprimality only in the harmonic upper bound and expand ordered distinct primes, yielding the factor S_4^j/j! for omega(e)=j. Thus the main terms jointly cost at most a constant times
    [H³/(log y)^3] sum_{(j,i,i') in A_down}
       (S_4^j/j!)(S_2^i/i!)(S_2^i'/i'!).
For each j=2,4, S_j=T-log T+O(1) so exp(S_j)/log y is bounded, proving the probability envelope. Poisson mode bounds give the independent-width factors claimed above. In particular any thickened mask of o(T^(3/2)) count triples has o(H³) absolute mass, without positing an actual local limit theorem.

This suggests localizing a signed covariance computation in count triples, but a macroscopic fraction of the typical count volume, including alternating parity, is not removed. The signed separated, coprime bulk remains open; the first-moment reduction and the covariance are not conflated.
