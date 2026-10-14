# Unknown-upper moments: one exact identity and a failed general statistic

Contributor: Codex whole-source lane, 14 October 2026. **Hand calculations
and a preserved failed approach.** This was an exploratory route to the
shared-upper observer; the subsequent one-orbit theorem does not depend
on it. No general sparse-moment decoder or forcing theorem is claimed.

## A valid four-leaf identity

Suppose n A roots traverse an ordinary A-private interval of length L
and then meet one B root, followed by an exchangeable completed upper
law U. L and U may be jointly random; all identities are conditional on
that joint state, so no independence between them is assumed. Put
mu_1=E exp(-L), mu_3=E exp(-3L).

For three A labels, let Bal be the probability of the specified
cross-balanced topology ((A1,B),(A2,A3)), and let C_B be the probability
of the specified B-spine comb (((B,A1),A2),A3). If b_U and c_U are the
probabilities of a specified balanced and comb topology on four
exchangeable roots, then 3b_U+12c_U=1. The comb forbids every younger
A-only merger, while the balanced tree allows only the younger A2/A3
merger. Thus

 Bal=E[exp(-3L)b_U]+(mu_1-mu_3)/6,
 C_B=E[exp(-3L)c_U].

The second term in Bal is the probability of precisely the specified
first A-pair merger and no second younger merger, namely
(exp(-L)-exp(-3L))/2, times the upper triple probability 1/3. Hence

                         mu_3=6 Bal+24 C_B-mu_1.            (1)

The usual crossed triple gives mu_1. This calculation survives an
arbitrary exchangeable upper continuation and a common-stem dependence
between L and U. It does not by itself extend to all sparse exponents.

## The harmonic-leaf statistic loses every higher exponent

For a completed rooted binary tree, let d_B be the number of edges from
its root to B and consider h_B=2^(-d_B). Kraft's identity says that the
sum of this weight over all leaves is one. Grafting an A-only forest
into other leaves does not change B's depth. Conditional on k A roots
reaching the meeting, upper exchangeability therefore gives

                          E[h_B | k]=1/(k+1).

For ordinary Kingman root count N_n(t), define
phi_n(t)=E[1/(N_n(t)+1)]. This is indeed a universal unknown-upper
observable. However its exact value is

                phi_n(t)=1/2-[(n-1)/(2(n+1))]exp(-t).        (2)

To check (2), set a_n=(n-1)/(2(n+1)), with a_1=0. The pure-death
backward equations are

 phi'_n=lambda_n(phi_(n-1)-phi_n),
 phi_n(0)=1/(n+1),

and lambda_n(a_n-a_(n-1))=a_n. Formula (2) satisfies the equations and
initial values; uniqueness proves it for every n. Consequently all
sample sizes of this statistic recover only mu_1. The initially
suggested higher-eigenvalue induction was false; even its apparently
promising n=3 cancellation persists at every larger n.

This is failure of one universal statistic, not failure of (1), of the
subsequent fair-orbit observer, or of the original G4 problem. A genuine
all-order unknown-upper directed-moment decoder would require additional
observables or another construction.

Evidence: exact hand derivations, no computational or formal-verification
claim. Both the successful identity and the failure are retained for
attribution and to prevent reuse of the false higher-moment argument.
