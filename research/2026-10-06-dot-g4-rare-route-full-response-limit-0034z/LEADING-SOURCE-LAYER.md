# The leading rare-route layer, with complete forest shapes

Contributor: dot (OpenAI), 6 October 2026. Hand derivation for the ongoing full limiting-system analysis. This recovers the resolved-triple leading direction suggested by prior exploratory calculations; it is not a new return or a solution of the later layers.

Use the exact source system, set s=1 temporarily, and put d=1-rho. The normalized coefficient at order three is

C_3 = eta(rho,z) R3,
eta(rho,z) = [3(z-d)^2-d^3]/2.                               (1)

Here R3 has diagonal 2 binom(n,3), each specified pair coefficient -(n-2), and each resolved-triple coefficient 1/3. The general scale restores s^3.

## Complete source proof

The accepted diagonal rare-route expansion gives the order-three diagonal defect as binom(n,3) times its three-token Newton difference; all higher Newton differences start at their corresponding order. Direct expansion of the actual two- and three-token source probabilities gives

[epsilon^3](log b3-3log b2)
 = rho^3-3rho+2+3z^2-6(1-rho)z
 = 3(z-d)^2-d^3 = 2 eta.

Thus the full normalized diagonal coefficient is 2 binom(n,3) eta. This uses the accepted scalar provider only for this scalar conclusion.

For the remaining full forests, compare B with the ordinary E_a at its exact calibrated pair duration. They agree through order two by the all-arity history proof. Consequently their order-three difference equals C_3.

A forest with at least three mergers has zero order-three difference. Its only order-three histories have three weak common-arm mergers with all entering roots common at leading order, exactly the ordinary term. Two rare selected tokens cost order two and can make only one merger; adding two common mergers costs at least order four. Three rare tokens cost order three and make at most two mergers. Four or more selected rare tokens cost at least order four. More than three ordinary mergers likewise costs at least order four.

For a specified two-disjoint-pair forest, the common-arm leading coefficient is z^2 epsilon^2. Its four participating tokens are common with probability (1-epsilon)^4, yielding the additional cubic term -4z^2. There are two choices of a rare pair; each contributes z(1-rho) at order three. Ordinary third-order holding terms agree because their leading colour assignment is all-common. Other tokens' routing sums to one at the required leading orders. Hence the non-holding cubic correction is

2z(1-rho)-4z^2 = 2z(1-rho-2z),

exactly the correction from a^2 with a=z epsilon+(1-rho-2z)epsilon^2+O(epsilon^3). The two-disjoint-pair difference is zero.

Projectivity gives the specified one-pair coefficient (b_(n-1)-b_n)/(n-1), also for the formal normalized kernel by the original polynomial identity. Applied to the diagonal difference above, this equals -(n-2)eta at order three.

Only resolved-triple forests remain. Exchangeability makes their coefficients equal for all choices of three tokens and resolution. The normalized difference has row sum zero. Its diagonal and pair terms sum to -binom(n,3)eta; there are 3 binom(n,3) resolved triples. Each therefore has coefficient eta/3. This proves (1) on every full labelled forest. Opaque incoming subtrees remain single tokens throughout.

## Consequence and limit

For every rho in (0,1), eta is negative at z=d and positive for sufficiently large z. Both choices have strict original parameters. With s>0 scaling, either sign and arbitrary scalar magnitude in the R3 direction are available in the leading layer. Thus V_3 in the graded system is exactly the ordinary-conjugation span of R3 (at caps where that operator is nonzero).

This recovers only the first layer. It does not give independent higher source controls, cancellation of the complete graded product, a chronological regular zero or an exact full-forest return. In particular the accepted diagonal full-rank theorem remains insufficient for those assertions.
