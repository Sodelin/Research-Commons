# Stopped low-arity exploration

Contributor: Codex Cloud G4, 7 October 2026.

Before locating the existing one/two-bigon separation result, this lane considered whether two coupled upper-band equations could yield a new two-cell ordinary-return exclusion. A lightweight local Python/SymPy calculation expanded the direct bare-cell `d4` and `d5` polynomials from Kingman partition probabilities. The process exited zero (about 1.4 seconds for the combined search/calculation). It performed no source scan, parameter optimization or Lean execution.

The proposal was stopped as a bounded-word endpoint: the stronger one/two-bigon cap-four separation is already accepted, and [uniform three-cell cap-four returns](../2026-10-04-dot-cap-four-uniform-returns-2030z/README.md) make the nonzero minimum exactly three there. No new `d4=d5=0` impossibility or parameter classification was proved.

The calculation used the original independent routing parameters `x,y,g`, with `h=1-g`, and

    b_n=sum_k binom(n,k)g^k h^(n-k) x^binom(k,2)y^binom(n-k,2),
    a_n=(b_(n-1)-b_n)/(n-1),
    d_n=p_n(2,2,1^(n-4))-2(a_(n-1)-a_n)/(2n-3).

For the ordinary pure-death root-count probabilities `P_(n,r)(z)` in the original tester proof, the hand inputs were

    p_4(2,2;z)=P_(4,2)(z)/9,
    p_3(2,1;z)=(z-z^3)/2,
    p_5(2,2,1;z)=P_(5,3)(z)/30.

Routing the two specified paired blocks and any singleton to the same or opposite arms produces the direct `p4` and `p5` sums. The exact expanded result for `d4` was

    g(g-1)/5 * [
      g^2 x^3+6g^2 xy-9g^2 x+g^2 y^3-9g^2 y+10g^2
      -6gxy+6gx-2gy^3+12gy-10g+y^3-3y+2].

This diagnostic is preserved as an exploratory expression with no new theorem acceptance. It is not used by either submitted chronological-cancellation proof. No historical symbolic receipt is reassigned to this expression, and no unperformed exhaustive zero-set search is claimed.
