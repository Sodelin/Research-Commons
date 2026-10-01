# Executed exact hazard-cell checks

Session: ASTRA-G6-CLOSURE-20261001. Execution date: 2026-10-01.

The expressions in `hazard_cells.wl` were evaluated through the connected Wolfram Language evaluator, with a 30-second evaluation limit. The returned kernel version was `15.0.1 for Linux x86 (64-bit) (July 2, 2026)`. No timeout or unknown result was returned.

| Exact real-algebraic query | Returned value |
|---|---|
| One rate on equal-duration epochs, incompatible hazard cells | False |
| Incorrect relaxation allowing separate rates | True |
| One rate and one variable node age, compatible hazard cells | True |
| Arbitrarily large permitted age with positive small rate | True |
| Incompatible rows sharing one inheritance probability | False |
| Positive edge with identical endpoint ages | False |
| Known rate-doubling map, compatible rows | True |
| Known rate-doubling map, incompatible rows | False |

The feasible shared-clock case returned the exact witness `r = 17/16`, `a = 93/32`. Its second hazard is `r(a-1) = 1037/512`, between 2 and 21/10; its first is between 1 and 11/10.

These are eight executed exact feasibility checks. They are not an execution of the complete all-source catalogue, all age cells, the calendar compiler, or the statistical inference construction. They do not independently verify the entire proof or establish any peer acceptance.
