# Can the five-taxon minimum lift to the exact minimum for every size?

Contributor: Codex `minimal_projection`, USER-MINIMUM-LIFT-20260930.
Date: 2026-09-30 UTC. Status: hand-derived counting/decision-tree facts and
scope analysis. No all-size exact minimum or historical novelty claim.

## 0. Answer

The five-taxon optimum is a useful base case, but it does not determine
the all-size optimum. An exact reduction or recurrence could transfer it;
that transfer must preserve the actual oracle, full split output, source
admission, and worst-case decision-tree cost. A smaller exact stored
representation by itself supplies none of those query guarantees.

A direct continuation now supplies more than this limitation:
[EXACT-MINIMUM-THEOREM.md](EXACT-MINIMUM-THEOREM.md) proves, conditional on
the audited source structure, that every profile has an actual admitted
representative with at most `8n-14` unrooted vertices. Exact finite graph
enumeration plus the recurrence below therefore gives a uniform algorithm
computing q(n) and an optimal policy for each n. It is an exponential
specification, unimplemented beyond the small-case controls, rather than
a closed formula or efficient optimizer. It uses actual source graphs
and admission checks, not an assumed converse for arbitrary compact codes.

## 1. An all-size bound already excludes five queries for all sizes

Let q(n) be the optimal deterministic adaptive worst-case number of
complete-support quartet queries for EXACT-QUERY-01.
Every labeled unrooted binary tree is admitted. There are

    T_n = (2n-5)!!

such trees, with distinct required full split unions. On this subclass,
each query has three possible singleton answers. A depth-q decision tree
has at most `3^q` leaves on these inputs. Therefore

    q(n) >= ceil(log_3((2n-5)!!)) = Omega(n log n).

| n | Binary trees T_n | Tree-count lower bound |
|---|---:|---:|
| 4 | 3 | 1 |
| 5 | 15 | 3 |
| 6 | 105 | 5 |
| 7 | 945 | 7 |
| 8 | 10,395 | 9 |
| 10 | 2,027,025 | 14 |
| 12 | 654,729,075 | 19 |
| 16 | 213,458,046,676,875 | 31 |
| 20 | 221,643,095,476,699,771,875 | 43 |

These integer bounds were calculated by multiplying the odd factors and
repeatedly multiplying 3 until it reached T_n, avoiding floating-point
rounding. They are arithmetic illustrations of the proof, not new
computational evidence about source identifiability.

In particular `q(7)>=7`: a constant five-query lift is impossible.
At n=5, the counting bound gives only three, while the explicit admitted
N2/five-rotated-N1 adversary proves `q(5)=5`. That discrepancy demonstrates
why a general information lower bound need not be the exact minimum.

## 2. What a direct-sum lift would prove

Suppose t independently variable copies of the five-taxon hard gadget
could be combined into admitted networks, and suppose each allowed
quartet query could distinguish alternatives in at most one gadget.
Following the all-baseline transcript would then require five relevant
measurements per gadget, giving a lower bound `5t`.

Both hypotheses need proof. Grafting can change source rootability,
switching independence, and which cross-component quartets change.
Local ports may stand for many original taxa. These facts cannot be
assumed from the five-taxon certificate.

Even if the construction used `n=Theta(t)` taxa, the bound `5t` would be
only linear and asymptotically weaker than the admitted tree-count
`Omega(n log n)` bound. It would not prove an equality recurrence such
as `q(n+4)=q(n)+5`. Equality requires both a matching universal algorithm
and a lower bound covering all strategies, not simply independent gadgets.

## 3. The exact finite recurrence, and its limits

Let P_n be the finite set of actual admitted complete oracle profiles.
For a remaining candidate set H, let `H(Q,a)` contain the profiles giving
answer a on quartet Q. The exact decision-tree recurrence is

    D(H) = 0                                  if |H|<=1,
    D(H) = 1 + min_Q max_a D(H(Q,a))           otherwise,

where Q ranges over queries that genuinely partition H. Then
`q(n)=D(P_n)` for the full split-plus-order target: distinct admitted
profiles have distinct split unions under the inherited reconstruction
identity. A common order can be constructed after the union is known.

This recurrence is executable when the exact finite candidate profiles
are supplied. It is not a closed formula in n, an efficient source census,
or a polynomial-time all-size algorithm. An overinclusive family of
arbitrary common-circle trees can overestimate the source optimum.
The five-taxon proof avoids that issue through actual admitted witnesses
and the universal five-query upper bound.

For every fixed finite n, a minimum is attained: full-table acquisition
gives a finite upper bound, and feasible worst-case depths form a nonempty
set of integers. This does not show that a uniform efficient algorithm
attains every finite-n optimum, or that the published asymptotic lower
bound is tight.

## 4. Orders and complete outputs are different targets

N1, N2, and the relevant cyclic rotations share the same compatible
circle while having different split unions. Counting possible returned
circles cannot account for this distinction. The five-query adversary
lower-bounds complete split recovery; it does not prove an order-only
five-query lower bound.

Conversely the exact `Theta(n log n)`-bit compressed representation in
MINIMAL-PROJECTION.md shows a real information shadow. A scalar storing
those bits still needs that precision. Obtaining it from constant-answer
point queries requires enough measurements to distinguish the admitted
outputs. Packing answers or squaring a complex encoding does not multiply
the information received from each query.

## 11. Process integrity

The finite source witness, the broader-family minimax calculation, and
the all-size counting theorem remain separate. No grafted direct-sum
family or equality recurrence was executed or proved here. The source
and primary-prior dependencies are documented in MAXIMAL-ADAPTIVE-NEXT.md.

## 12. Robustness and decisive next theorem

A valid all-size lift must supply a source-admitted reduction and show
matching query costs in both directions, or establish a universally
efficient learner with a matching scalable admitted adversary. That
could settle the minimum. The finite base case, storage codec, primitive
rank barrier, and unproved direct-sum idea cannot settle it individually.
