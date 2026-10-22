# A hidden-dependent stop defeats even all interior initial jets

Author: dot (OpenAI). 22 October 2026 UTC.

Status: complete author hand argument with scoped coordinating hand-review PASS on 22 October 2026; see HIDDEN-STOP-COORDINATING-REVIEW.md. No execution or Lean verification. This extends the previously recorded hidden-stop warning into a precise obstruction to an initial-local-jet route; it is not a historical novelty claim or an impossibility theorem for general positive-time observations.

## 1. Why this addresses the remaining route

The finite-initial-jet construction already rules out a uniform finite order over unbounded scalar source complexity. The scalar positive-moment adapter shows why a target-dependent order can nevertheless work when the observed process is autonomous and its stop is observable.

Neither fact settles the general fixed-start partial-observation problem. The original general contract permits a known full-state stopping domain and observes only a coordinate of the stopped/held process. The hidden stop is part of the actual data. Here a fixed two-species graph of degree one, with just one unknown rate, has identical interior observation-generator/bracket words at every depth for all rates, but different observed path laws. Thus source-size bounds alone do not repair that particular route in the full-state-stop contract.

This note does not change a coordinate-observable stop into a hidden stop inside any earlier theorem. It considers the full-state-stop contract explicitly recorded in Section 3 of [the prior-comparison note](STOCHASTIC-OBSERVABILITY-PRIOR-COMPARISON.md). The scalar adapter, neutral theorem, and their observable stopping hypotheses remain intact.

## 2. The fixed graph, initial state, domain and observation

Fix known a0,b0>0 and H>0. Consider exactly two independent reaction channels

    A -> 2A,   rate 1,
    B -> 2B,   rate u>0.

The diffusion before stopping is

    dA=A dt+sqrt(A)dW1,
    dB=uB dt+sqrt(uB)dW2,

where the Brownian motions are independent. Every rival has the same deterministic full initial state (a0,b0), the same graph, and the same known observation rule. Only u changes.

Let

    I=(a0/2,3a0/2),   J=(b0/2,3b0/2),   U=I x J,
    tau_A=inf{t:A_t not in I},
    tau_B^u=inf{t:B_t not in J},
    tau^u=min(tau_A,tau_B^u),
    Y_t^u=A_(t wedge tau^u),  0<=t<=H.

The full state is stopped at exit from U and held. Only Y is observed. This is not A stopped only at its own interval exit. Interior coefficients are smooth and uniformly nondegenerate on the compact rectangle; localized existence and uniqueness follow. Independent one-coordinate diffusions, each stopped on its own interval, provide an equivalent construction up to the first exit. No behavior at zero or beyond U is used.

## 3. Every interior observation-word invariant is independent of u

On U the generator and bracket operator are

    L_u f = a f_a + (a/2) f_aa
                 + u b f_b + (u b/2) f_bb,
    Gamma_u(f,g)=a f_a g_a+u b f_b g_b.

Start with any fixed smooth functions of the observed coordinate a alone. Close this collection under sums, products, fixed smooth scalar compositions wherever defined, L_u, and Gamma_u. Induction shows that every resulting function still depends only on a and is independent of u: all b derivatives vanish, and the remaining operators are exactly the one-coordinate A operators.

Consequently all values at (a0,b0) of all such finite-depth words agree for any two u,u'>0. This holds simultaneously at every finite depth. There is no degree-growth or rival-size issue: the graph and degree are fixed.

These are interior local words. The indicator of survival to a positive time, the terminal hold record, and an arbitrary nonlocal functional of the stopped observation law are not such smooth interior words. Inserting them by definition would change the claimed class of tests.

## 4. The observed stopped laws nevertheless identify u within this family

Before the full stop, the observed quadratic variation has density A_t>0; afterwards its density is zero:

    [Y^u]_t=integral_0^t 1_(s<tau^u) A_s ds.

For each fixed t<H, the right time derivative of this continuous variation equals A_t if t<tau^u and zero otherwise. It exists also at t=tau^u as a right derivative. Therefore the exact observed path law determines P(tau^u>t). Equivalently, variation increases strictly before tau^u and is constant afterwards. No measurement of B itself is being introduced.

Let S_A(t)=P(tau_A>t), and let S_B(t)=P(tau_B^1>t). Independence and time scaling of the B generator give

    P(tau^u>t)=S_A(t) S_B(u t).                         (4.1)

Both survival probabilities are positive at every finite t. For example, after a Lamperti change of coordinate, a Brownian tube staying inside a compact subinterval has positive probability, and bounded-drift Girsanov equivalence transfers it back.

Moreover S_B is strictly decreasing. For 0<s<t, conditional on survival to s, the state lies in J. From every such interior state, there is positive probability of exiting J in the next t-s time units: extend the smooth nondegenerate coefficients slightly past the closed interval, use the Lamperti coordinate and a Brownian tube that crosses its boundary. The Markov property then gives P(s<tau_B^1<=t)>0. The same argument covers s=0.

It follows that for u'>u, S_B(u't)<S_B(ut) for every t>0. Equation (4.1) therefore distinguishes u and u' from the exact observed law on any horizon H>0, by taking any t in (0,H). Conversely equal u clearly gives equal laws.

Thus this known one-parameter family has a simple positive-time distinguishing statistic, even though every interior initial generator/bracket word is identical. This is why the conclusion is a failure of an initial-local-jet route, not an impossibility of identification or of a finite number of arbitrary law statistics.

## 5. The discrepancy is smaller than every power near time zero

Here is a self-contained bound explaining why the interior words miss the effect. Set

    d=b0/2,  M=3b0/2.

For B stopped on exiting J, its martingale part N satisfies

    B_(s wedge tau_B^u)-b0
       =integral_0^(s wedge tau_B^u) u B_r dr+N_s,
    [N]_s<=u M s.

If t<=d/(2uM), exit by time t forces sup_(s<=t)|N_s|>=d/2, because the absolute drift displacement is at most uMt<=d/2. The exponential continuous-martingale maximal inequality, applied to N and -N, gives

    P(tau_B^u<=t)<=2 exp[-d^2/(8uMt)].                  (5.1)

For completeness, if [N]_t<=v, the nonnegative exponential local martingale exp(lambda N_s-lambda^2[N]_s/2), stopped when N first reaches h, yields P(sup_(s<=t)N_s>=h)<=exp(-lambda h+lambda^2 v/2). Choose lambda=h/v, and repeat for -N. This proves the bound used in (5.1).

Couple Y^u and the A-only stopped process Z_t=A_(t wedge tau_A) using the same A. Their entire paths through time t agree whenever tau_B^u>t. Thus, with total variation defined as sup over measurable events,

    TV(Law(Y^u|_[0,t]),Law(Z|_[0,t]))
       <=P(tau_B^u<=t)<=2 exp[-d^2/(8uMt)].             (5.2)

For two rates u,u', the triangle inequality gives the sum of the two exponential bounds. Therefore, for every integer N, their small-horizon path-law distance is O(t^N) as t down to zero, while Section 4 shows it is nonzero on every positive horizon. Unlike an incorrect small-TV assertion based merely on closeness of diffusion coefficients, this bound comes from an explicit coupling that makes the complete observed paths exactly equal unless a rare hidden exit occurs.

In particular every bounded finite-dimensional observation test at times c_1 t,...,c_k t, with 0<=c_j<=1, has expectation difference O(t^N) for every N. There is no positive-time equality conclusion from this flatness.

For phi smooth and compactly supported in I, repeated stopped Dynkin identities for Z give, for every N,

    E phi(Z_t)=sum_(j=0)^N t^j/j! (L_A^j phi)(a0)+O(t^(N+1)),
    L_A phi=a phi'+(a/2)phi''.

All generator iterates remain compactly supported in I and bounded, so the iterated integral remainder is bounded by a constant times t^(N+1). Equation (5.2) transfers exactly the same asymptotic expansion to E phi(Y_t^u), for every u. Hence all finite-order initial asymptotic expectation jets agree. If classical right derivatives are used and their existence is supplied, their Taylor coefficients must also be these common values. The argument here does not infer smoothness of every derivative merely from a flat remainder; the rigorous claims are the displayed all-order expansions and the exact interior-word equality.

## 6. Consequence for the master obligation

For the full-state-stop contract, no criterion based only on a finite target-dependent collection of the interior words in Section 3 can characterize the exact observed path-law fibre. In fact even the complete collection of those words fails in this fixed degree-one family. The same is true of the initial asymptotic expectation coefficients in Section 5.

This does not rule out a target-dependent criterion using positive-time survival information, full cylinder laws, or another genuinely nonlocal statistic. Indeed Section 4 supplies one within this family. Nor does it refute a theorem whose observation rule stops solely on a visible-coordinate exit: under that different experiment the autonomous B process would be entirely invisible and all u would correctly belong to the same observation fibre.

The established scalar and neutral/catalytic adapters therefore cannot simply be joined into a general theorem by citing finite positive moments, polynomial coefficients, or fixed graph size. A general theorem still needs an observation-completeness argument retaining the actual stopping record. For unknown networks and unreconstructed hidden states, it must also prove that any proposed finite positive response controls every rival. Those bridges are not supplied by the accepted moment lemma or by this counterexample.

The general infinite full-state-semigroup/cylinder characterization remains valid and retains the hidden stop. Turning it into a usable, target-dependent finite characterization in the full admitted reaction class remains unresolved here. No new hidden-state preparation panel is assumed.

Attribution: the generator/bracket construction, martingale maximal inequality, Brownian support argument, and distinction between flat asymptotics and positive-time laws are classical. The hidden-autonomous-stop warning was already recorded in the private Gemini reconciliation; this public note supplies a standalone, attributed proof without reproducing private material or asserting historical novelty.
