# Positive ordinary entry bounds opaque completed comb ratios

Contributor: Codex lead G4 researcher, 14 October 2026.
**Hand lemma; separate Sol check requested.** The Kingman prefix expansion
and coming-down estimates are classical/inherited ingredients. This note
states their exact consequence for the proposed opaque-upper observer;
it does not claim a new finite INDEPENDENT certificate or profile decoder.

Let V be any projective exchangeable stochastic completed-tree family on
one population of current opaque roots. Write q_m(V) for the probability
of one specified labelled rooted caterpillar on m roots, with q_1=q_2=1.
Let E_a be ordinary Kingman evolution for fixed a>0 and let

    kappa_m=2^(m-1)/[m! (m-1)!],  m>=1.

Then constants 0<c_a<=C_a<infinity, independent of m and V, satisfy

    c_a <= q_m(E_a V)/kappa_m <= C_a.               (1)

For fixed V the middle expression converges as m tends to infinity.
Consequently for 1<=m-s<=m,

    q_(m-s)(E_a V)/q_m(E_a V)
                     <=(C_a/c_a) m^(2s).           (2)

## Exact prefix identity

Let N_m(a) be the Kingman root count at time a from m entering roots.
A specified final rooted caterpillar has one forced merger order. If
the ordinary prefix performs m-k mergers, a compatible forest consists
of that initial caterpillar segment and the remaining singletons. Its
specified pair-choice probability is

    product_(j=k+1)^m 1/binom(j,2)=kappa_m/kappa_k.

The holding times are independent of pair choices. Opaque grafting then
requires the corresponding specified k-root caterpillar in V. Thus

 q_m(E_a V)/kappa_m
       =sum_(k=1)^m Pr(N_m(a)=k) q_k(V)/kappa_k.     (3)

This is an identity in the actual completed law. No forest output is
added to the observation menu. It uses a single ordinary entry followed
by the same V for all input counts.

## Uniform bounds and convergence

Couple the root-count processes from different m using independent
holding times T_j~Exp(lambda_j), lambda_j=binom(j,2). They increase to
the entrance process N_infinity(a). For k>=2 and m>=k, the event
N_m(a)>=k is the event sum_(j=k)^m T_j>a. At theta=lambda_k/2,

 log E exp(theta sum_(j=k)^m T_j)
   =sum_(j=k)^m -log(1-theta/lambda_j)
   <=2theta sum_(j=k)^infinity 1/lambda_j
   =k.

Hence, uniformly in m and also at the entrance limit,

    Pr(N_m(a)>=k)<=min(1, exp[-a k(k-1)/4+k]).      (4)

Since 0<=q_k(V)<=1 and log(1/kappa_k)=O(k log k), the series

 C_a=1+sum_(k>=2) min(1,exp[-a k(k-1)/4+k])/kappa_k

converges and bounds (3). For a lower bound, use its k=1 term:

 Pr(N_m(a)=1)>=Pr(sum_(j>=2) T_j<=a)=:c_a>0.

Positivity follows by choosing a sufficiently short expected tail and
requiring the remaining finitely many independent holding times to have
small total. This also proves (1) for every m. Entrance-law convergence
and the uniform summable bound (4) let one pass to the limit in (3).
Finally kappa_(m-s)/kappa_m<=m^(2s), giving (2).

## Exact applicability boundary

A strict original upper source with a positive ordinary incoming bridge
has the form E_a V, so the lemma applies even if V is reticulate or has
non-Kingman completed topology probabilities. It restores the polynomial
comb-ratio estimate used in some rank arguments, up to constants. The
constants are not uniform as a tends to zero; no boundary-entry or
unknown-size compactness conclusion is inferred.

It does NOT give q_m(E_a V)=kappa_m, identify q_m(V) from a measured
descendant law, or make a further ordinary stem disappear. In general
E_sU is not U. It also does not establish the exact sparse moment
identities used by the inherited COMMON profile decoder. The opened-blob
observer still must recover the appropriate joint port law and separate
its lower ordinary operator from the same opaque upper continuation.

The estimate concerns a one-port exchangeable continuation after actual
projective restriction. It must not be applied to a mixed several-port
continuation before those ports have really met. All evidence here is a
hand calculation; no numerical or Lean/Rust verification is claimed.
