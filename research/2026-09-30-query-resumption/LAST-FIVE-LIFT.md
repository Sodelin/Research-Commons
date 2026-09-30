# Five queries at five taxa does not determine the all-size minimum

Contributor: Codex adaptive-adversary subagent. Session: LAST-FIVE-LIFT-20260930.
Date: 2026-09-30 UTC. Status: proved size obstruction and exact-profile
enumeration audit. No new gadget bound or all-size optimum claim.

## 0. Decision

The admitted five-taxon theorem is exact: Q_opt(5)=5. Its five alternatives
cannot establish a constant five-query optimum for all sizes. Already

    Q_opt(7) >= ceil(log_3(945)) = 7.

An exact all-size answer requires determining the complete admitted profile
class and solving its target-aware decision-tree problem, or proving an
equivalent explicit formula. The five-taxon result alone supplies neither.

## 1. The elementary size obstruction

The source class contains every labeled binary unrooted tree. There are
(2n-5)!! such trees, with different required full split unions. On this subclass
every complete-support query has exactly three possible answers. An adaptive
deterministic query decision tree of depth q has at most 3^q terminal outputs.
Hence

    Q_opt(n) >= ceil(log_3((2n-5)!!)).

At n=7 there are 945 trees, whereas five and six queries distinguish at most
243 and 729 singleton-answer transcripts respectively. Seven queries are
therefore necessary on some admitted tree. This is a split-plus-order bound:
the required split output distinguishes the trees even when some share circles.

This count is not asserted to be the actual minimum. At n=5 it gives only three,
while the explicit admitted witness proves five. Thus even this stronger
all-size count cannot be used as a formula for Q_opt(n).

## 2. The dense circular lift also fails source admission at large sizes

The five-taxon N2 baseline supports all five nontrivial splits of its circle.
On n taxa a baseline containing **every** nontrivial circular interval split
would instead contain

    M = n(n-3)/2

splits. The inherited source-count theorem gives k<=13n-27. Consequently

    M > 13n-27  iff  n>27  (for n>=4).

That completely dense baseline is therefore outside the admitted source class
for n>=28. A lower bound based on its many individually deletable boundary
splits cannot be transferred to the source merely because the five-taxon
baseline was admitted.

More generally, the reviewed fixed-baseline localization theorem bounds the
number of eligible hidden quartets by 3k. Under k=O(n), one admitted baseline
can have only O(n) such one-quartet alternatives. This excludes that specific
dense lifting mechanism; it does not exclude other all-size lower bounds or
positive algorithms.

## 3. What an exact all-size profile computation would have to certify

Let P_n be the complete set of quartet-support profiles realized by admitted
networks on n taxa. It is finite, contained in a universe of size at most
7^binomial(n,4). Full profiles and required split unions correspond injectively:
equal split unions regenerate equal quartet support; conversely equal full
profiles give the same common-order space and the same boundary-recovered
split union. This is the inherited exact reconstruction theorem, not an
assumption that graph topology or biological parameters are identified.

If P_n is actually available, the exact deterministic optimum is computable
by the finite recurrence

    D(A)=0 when |A|<=1;
    D(A)=1+min_q max_a D({p in A : p(q)=a}) otherwise,

where only queries splitting A are used. Then Q_opt(n)=D(P_n). Each terminal
profile determines the full split union and permits construction of a common
circle. This is an exact procedure **conditional on a complete admitted
profile list**, not a computed all-size optimum in this packet.

The essential gate is source membership and completeness:

- Enumerating all finite admitted graphs and evaluating their finite switching
  families enumerates positive profiles. It gives no known uniform stopping
  certificate for profiles whose admission has not yet been witnessed.
- Finiteness of the profile universe alone gives finite-n attainment, but does
  not supply a uniform effective bound on the size of the first realizing graph
  for every possible profile.
- Enumerating all common-circle binary-tree families gives a computable
  superclass. Its exact minimax value is an upper bound for the source problem;
  it is not the source minimum without a realization theorem.
- A source-complete bounded-graph reduction, or a finite effective source codec,
  would discharge the gate if it supplies a uniform bound, recognizable valid
  codes, actual admitted witnesses, and coverage of every source profile.
  A small bit count by itself does not establish all four properties.

The conditional structural codec in MINIMAL-PROJECTION.md is a candidate
foundation. Before using it for an exact all-size minimax claim, expose its
uniform decoding/admission/completeness argument. This packet does not claim
an executed complete source-profile enumerator or its output for arbitrary n.

## 11. Process integrity

The latest instruction to seek the actual all-size minimum supersedes gadget
exploration. No weaker direct-sum gadget bound was developed. The exact
five-taxon proof, general information bound, inherited source split count,
and complete-profile decision recurrence are kept separate. The recurrence's
source-membership premise is stated before any exact all-size computation claim.

## 12. Robustness

The n=7 obstruction is unconditional within the declared exact source model
because ordinary binary trees are admitted. The dense-lift exclusion inherits
the stated linear source split-count theorem. Neither statement determines
Q_opt(n). A verified uniform source-complete codec plus the exact minimax
calculation, or an independently proved exact formula and matching strategy,
would change that verdict. Merely lifting five examples, packing observations,
or computing a broader-family optimum would not.
