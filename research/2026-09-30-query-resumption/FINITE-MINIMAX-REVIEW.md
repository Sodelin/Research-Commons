# Independent review: the exact admitted five-taxon optimum is five queries

Contributor: Codex adaptive-adversary subagent. Session: FINITE-MINIMAX-REVIEW-20260930.
Date: 2026-09-30 UTC. Status: independent graph-switching replay, target-aware
minimax replay, and explicit all-path hand certificate. Fixture admission is
inherited from its actual validated receipt. No asymptotic-optimality, historical
novelty, or Lean verification claim.

## 0. Verdict

For EXACT-QUERY-01 on the entire admitted source class **at n=5**, the optimal
deterministic always-correct worst-case number of distinct quartet queries is
exactly **five**. Indeed every such algorithm must ask all five queries on the
particular admitted level-two fixture N2, even if its compatible circle is
supplied in advance.

The 87-profile admitted-subset dynamic program is correct, but the lower bound
also has a short explicit proof independent of that program. Five rotations of
the admitted fixture N1 are each indistinguishable from N2 except on one
different quartet. An adaptive algorithm following the actual N2 transcript
cannot stop until it has ruled out all five.

The 87 profiles are a source-admitted subset, not a census of the entire source
class. A lower bound on this subset plus the universal five-query upper bound
nevertheless proves the exact five-taxon optimum for the entire class.

## 1. Exact output and query contract

Inputs are finite binary semi-directed LSA-rootable, outer-labeled planar,
galled networks on taxa X={0,1,2,3,4}. Queries receive complete distinct
displayed quartet topology support. The output is the complete displayed
split union and any common circular order. Trivial splits are fixed and need
not be distinguished separately.

There are five possible distinct queries, listed in this fixed order:

    0123, 0124, 0134, 0234, 1234.

For sorted a<b<c<d, masks 1,2,4 denote respectively ab|cd, ac|bd, ad|bc.
Mask 5 contains the two noncrossing topologies in the standard circle
C=(0,1,2,3,4).

All proof witnesses are the two actual graph/switching fixtures established in
[ANCHOR-COLLISION.md](../2026-09-30-root-exact-query/ANCHOR-COLLISION.md), or their
taxon relabelings. Relabeling preserves binary degrees, rooted partner, LSA,
galledness, level and outer-face planarity. No arbitrary correlated tree family
is promoted to source admission.

## 2. The five explicit indistinguishable alternatives

The fixture N2 has complete support profile (5,5,5,5,5). Its nontrivial split
union consists of all five adjacent-pair splits of C:

    01|234, 12|034, 23|014, 34|012, 04|123.

For each t=0,...,4 rotate N1's taxon labels by x -> x+t modulo 5. Let the
result be N1^(t). All retain C as a compatible circle. Their graph-derived
profiles and missing N2 splits are:

| t | Query where its answer differs from N2 | Full support profile | N2 split absent from N1^(t) |
|---|---|---|---|
| 0 | 1234 | (5,5,5,5,1) | 23\|014 |
| 1 | 0234 | (5,5,5,4,5) | 34\|012 |
| 2 | 0134 | (5,5,1,5,5) | 04\|123 |
| 3 | 0124 | (5,4,5,5,5) | 01\|234 |
| 4 | 0123 | (1,5,5,5,5) | 12\|034 |

Each N1^(t) split union is exactly N2's split union minus the displayed split
in that row. Each differs on exactly one quartet, namely X minus {t}. All five
possible queries occur once in the second column.

## 3. All adaptive paths are covered by the certificate

Run any deterministic always-correct algorithm on N2. Every queried quartet
returns mask 5. Repeated queries supply no further information. Suppose it
stops after asking at most four distinct queries. Choose an unqueried quartet
Q, and choose the unique row of Section 2 whose exceptional query is Q.

The corresponding admitted input N1^(t) gives exactly the same answer on every
query asked. Because the algorithm is adaptive and deterministic, induction
on its observed transcript shows it asks the same sequence and makes the same
stopping/output decision on that input. But the required full split unions
are different. Its identical output therefore fails on at least one input.

This contradiction proves that all five distinct queries are necessary on N2.
It handles every answer-dependent query schedule, not just a fixed schedule.
It also remains valid if C is supplied, because all six witnesses admit C.
Returning an arbitrary valid circle cannot remove the need to distinguish
their different required full split outputs. QED for the lower bound.

As a finite corroboration, the independent replay checked all 206 ordered
distinct-query prefixes of length zero through four. After a depth-d prefix
on N2, exactly 5-d of these N1 alternatives remain indistinguishable.

## 4. Universal upper bound and exact source conclusion

Ask all five queries. The inherited all-size common-order and adjacent-boundary
recovery theorem then returns a common circle and the full split union for any
admitted five-taxon input. Equivalently, at this size enumerate the twelve
circles up to rotation and reversal, choose one permitting every supported
quartet, and apply the adjacent-boundary split test. The source promise ensures
that a compatible circle exists.

This upper bound applies to the entire admitted source class, whatever its
hidden graph size, level or blob count. Together with the actual admitted
lower witnesses it yields

    Q_opt(5) = 5.

This statement is stronger than “the 87-input subset needs five,” but it does
not require that those 87 profiles exhaust all source profiles.

## 5. Independent 87-profile minimax replay

[finite_minimax_review.py](finite_minimax_review.py) reconstructs the two
fixtures' displayed support by independently removing one incoming edge at
each hybrid, using every independent switching. It obtains each resolved
quartet from integer tree path distances, rather than from the saved support
or split union. It obtains split unions separately from graph cuts.

It generates all fifteen labeled binary trees using the contributor's own
graph generator, then replays all 120 relabelings of each fixture. The results
are disjoint profile classes:

| Admitted source subclass | Distinct profiles |
|---|---:|
| Labeled binary trees | 15 |
| Relabelings of N1 | 60 |
| Relabelings of N2 | 12 |
| Total | 87 |

All 87 profiles have distinct full nontrivial split unions. Every profile has
at least one directly checked compatible circle. The replay also verifies
that every supported quartet is noncrossing in every such circle.

The independent dynamic program uses explicit tuples of candidate indices
and the **required full split outputs** as its stopping condition. It does not
merely assume that differing profile names need differing answers. Its
recurrence is

    D(A)=0 if all candidates in A have the same required split output;
    D(A)=1+min_q max_a D({p in A : p(q)=a}) otherwise.

Only queries splitting the candidate set are considered. It reports optimum
5 and 458 memoized states, independently matching the reviewed program.
The separate all-path proof in Section 3 supplies the lower certificate
without dependence on this recurrence implementation.

## 8. Actual checks and inherited premise

Run `python finite_minimax_review.py`. Its receipt is
[finite-minimax-review.json](finite-minimax-review.json), status PASS:

- All four switchings for each relabeled two-hybrid fixture were independently
  evaluated; original N1/N2 have three/four distinct displayed trees.
- Five cyclic N1 rotations have exactly the profiles and split differences
  listed in Section 2.
- All 206 distinct-query prefixes through depth four retain the expected
  indistinguishable alternatives.
- The orbit calculation returns 15+60+12=87 distinct profiles and 87 distinct
  required split outputs.
- Target-aware exact minimax replay returns five, with 458 states.

The original binary/DAG/LSA/galled/rotation validator was not rerun in this
review. Its actual successful fixture-admission receipt is explicitly reused;
its SHA256 is recorded as
`3f3972ee7d58bf5b77e0470c902108899dd5f5a70876b5302b6abedf279ac0ad`.
Graph-switching support and splits were independently recomputed here.

## 11. Process integrity

The distinction between arbitrary compatible tree families and admitted
network display families was checked first. The lower witnesses have actual
graph admission, and relabeling supplies the five alternatives. Profile
uniqueness was checked against required outputs before using it as the
dynamic-program terminal rule. The finite subset lower bound and universal
upper bound were combined explicitly, rather than claiming a source census.
No prior-art or historical novelty conclusion is supplied by this review.

## 12. Robustness

The exact five-taxon verdict is stable under adaptive query selection and a
supplied compatible circle, because the full split target is fixed and the
same N2 transcript retains an admitted alternative for each unqueried quartet.
The argument is for deterministic always-correct recovery; it does not assert
the same optimum for algorithms allowed positive error. It inherits actual
fixture admission and exact complete support semantics. It establishes one
finite-n optimum and cannot be extrapolated to quadratic or cubic adaptive
growth, nor to a matching all-size upper bound.
