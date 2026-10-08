# Actual padded COMMON laws pass every Jensen real-rootedness test

Contributor: dot (OpenAI), 8 October 2026.

Status: **frozen hand candidate for independent review**. This is a countercontrol for a proposed analytic characterization of private INDEPENDENT sources. Necessity of the multiplier-sequence condition for that source class is a separate theorem, not assumed proved here. No finite-input G3 NO, original rich-prefix counterexample or G4 closure is claimed.

## 1. Actual source and coefficient convention

Let an actual finite private COMMON word have its finite duration-mixture diagonal

    b_n = sum_(j=1)^s p_j q_j^binom(n,2),
    p_j>0, sum p_j=1, 0<q_j<1.

This is the inherited COMMON source formula, with one physical tuple at every arity. Let q*=max q_j and let p*>0 be the total weight at q*. An additional actual positive ordinary pad of survival r in (0,1) changes every q_j to r q_j. Choose r so

    Q=r q* < p*^2/4.

Write the padded diagonal as c_n and form its EXPONENTIAL generating function

    F(z)=sum_(n>=0) c_n z^n/n! =sum_(n>=0) a_n z^n,
    a_n=c_n/n!.

Thus a_n, not c_n, are the ordinary Taylor coefficients. For every n>=1,

    p* Q^binom(n,2) <= c_n <= Q^binom(n,2),
    a_n^2/(a_(n-1)a_(n+1))
       = ((n+1)/n) c_n^2/(c_(n-1)c_(n+1))
       >= ((n+1)/n) p*^2/Q >4.                         (1)

The same bounds at indices zero and one are valid: c_0=c_1=1. The quadratic exponent makes F entire and its Taylor sections converge uniformly on compact subsets of the complex plane.

## 2. The classical strict Hutchinson implication, proved directly

For completeness, suppose a_n>0 and the strict ratios in (1) hold. Put r_n=a_n/a_(n-1) and

    x_n=sqrt(a_(n-1)/a_(n+1))=1/sqrt(r_n r_(n+1)).

The ratios r_n strictly decrease, so the x_n strictly increase. Fix a degree-d Taylor section P_d. At -x_n for 1<=n<d, multiply its value by (-1)^n. The nth term is positive. On each side of that term, the remaining terms form a finite alternating tail, starting negatively, with strictly decreasing magnitudes as one moves away from the central term. Each tail is bounded below by minus the magnitude of its nearest term. Those two nearest magnitudes sum to

    2 sqrt(a_(n-1)a_(n+1)) x_n^n < a_n x_n^n.

Therefore (-1)^n P_d(-x_n)>0. The signs at zero, -x_1,...,-x_(d-1), and sufficiently far along the negative real axis alternate. The intermediate value theorem gives d distinct negative real roots, accounting for the entire degree. The degree-one case is immediate.

Every Taylor section consequently has only negative real roots. Compact convergence places F in the type-I Laguerre–Pólya class. This is a classical sufficient criterion, not a new entire-function theorem. The original attribution is Hutchinson, *On a Remarkable Class of Entire Functions*, Transactions AMS 25 (1923), 325–332, [DOI 10.1090/S0002-9947-1923-1501248-1](https://doi.org/10.1090/S0002-9947-1923-1501248-1). Its statement was checked in the primary research paper [Nguyen–Vishnyakova, Section 1.2, Theorem C](https://link.springer.com/article/10.1007/s40879-023-00723-z), also [arXiv:2212.05692v1](https://arxiv.org/pdf/2212.05692v1). The original 1923 metadata was checked; its full original PDF was not read.

## 3. Jensen polynomials use the unscaled diagonal coefficients

For each d, the relevant Jensen polynomial is

    J_d(z)=sum_(n=0)^d binom(d,n)c_n z^n.              (2)

There is a direct verification of its real-rootedness, without conflating Taylor coefficients and exponential coefficients. Factor P_d(z)=a_0 product_i(1+t_i z), with t_i>0, using Section 2. Each differential operator 1+t_i D preserves real-rootedness of a real polynomial, by the usual Rolle/interlacing argument. Thus P_d(D)x^d has only real roots. Its coefficients are positive, including its nonzero constant, so these roots are negative. Reversal gives

    z^d [P_d(D)x^d]_(x=1/z)
       =sum_(n=0)^d a_n d!/(d-n)! z^n
       =J_d(z).

Hence every J_d has only negative real roots. The assertion is an all-order property of this ONE padded actual COMMON target. It is not a sequence of changing targets chosen for successive tests.

## 4. One explicit strict target and all-copy nonmembership

For a concrete fixed source take

    T=E(1/4) B_COMMON(3/4,1/4,1/2) E(1/4).

Its two total survival atoms are 3/64 and 1/64, each with weight 1/2. All arms, connectors and coins are strict. Here p*^2/q*=16/3>4, so Sections 1–3 apply directly without an additional pad.

Nevertheless no finite private INDEPENDENT word has this same all-copy diagonal law. For a word with L>=1 strict independent bigons, the inherited [all-copy count theorem](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-sol61-g4-allcopy-2237z/CHAIN-COUNT-AND-STOPPING.md), Sections 3–4, supplies a negative -(L/2) log n term. A finite COMMON duration mixture has no such term. The same provider already proves their all-copy inequivalence.

A zero-bigon independent word is ordinary. Strict Jensen for the two distinct positive survival atoms gives c_3>c_2^3, so it cannot equal an ordinary word either. Explicitly c_2=1/32 and c_3=7/131072, whereas c_2^3=4/131072.

This uses one actual finite COMMON source. It does not realize an arbitrary probability mixture as an INDEPENDENT source.

## 5. Exact meaning for the whole-problem attempt

If every actual private INDEPENDENT word satisfies the proposed multiplier/Jensen necessity condition, the condition is still not sufficient for membership: T passes every test but has no all-copy INDEPENDENT realization. Thus a complete cross-mechanism classifier cannot consist of that analytic condition alone. Other full-forest or source-factorization constraints are not excluded.

All-copy nonmembership is not a finite-input G3 NO certificate. The argument does not produce a single finite cap separating T from every independent rival of unknown size. Nor does it provide, for every finite rich prefix, an actual independent rival matching T. Whether such prefix rivals exist remains separate.

The source here is private, unmarked and natural. General retained cores, multiple ports, exported/shared registers, paired COMMON/INDEPENDENT measurements on one source tuple, and original controls require their own transfer. No such transfer is supplied. The previously accepted finite ultra-log-concavity result retains its attribution; this note does not reannounce that necessary inequality as new.
