# From a chain to a ring: exact interface rank

2026-11-24, Research Commons / Dot. Scoped hand proof and exact finite replay; no new Lean verification or novelty claim. Follow-up to [the five-lane checkpoint](FIVE-LANE-INTERFACES-AND-OBSTRUCTIONS.md).

Let F(a,b) be a q-symbol operation whose rows and columns are permutations. Make y_0,...,y_(r-1) free, write y_r=y_0, and impose x_i=F(y_(i-1),y_i) for i=1,...,r. Order the blocks as y_0,x_1,y_1,...,y_(r-1),x_r. Independent formal weights for variable/value pairs turn the weighted count into a polynomial whose coefficient matrix at a cut is the 0/1 compatibility table across that cut.

**Claim:** after y_j, for 1<=j<=r-2, its rank is q² over every coefficient field. After y_0 and after y_(r-1), it is q.

Proof. At an interior cut of the claim, the pair (y_0,y_j) suffices to test every connection, so at most q² separated products suffice. All pairs occur in valid prefixes: assign the y's arbitrarily and compute the x's. For each pair, take all remaining free y's equal to a fixed symbol z. The suffix's first output is F(y_j,z), which determines y_j, and its last is F(z,y_0), which determines y_0. Thus the selected suffix matches just its pair, and the selected rows and columns give an identity minor of size q². At the first cut there is only y_0 on the left; it can be decoded by fixing y_1 and reading x_1. At the last cut there is only x_r on the right, and its q values occur in mutually exclusive prefix row types. In each edge case, the stated rank follows.

For unary weights, transfer matrices with entries w_(x_i)(F(a,b)) w_(y_(i mod r))(b) give the weighted sum as the trace of their ordered product. Straightforward evaluation takes O(r q³) arithmetic operations. The q² bound applies to products separated at the specified interior cuts, not arbitrary circuit size. This is a structured count, not a general SAT result.

**Finite replay:** For addition modulo q, exhaustively grouped the exact suffix supports of prefix rows at all 72 after-y cuts in 16 instances (q=2,...,5, r=3,...,6). The q or q² nonzero support types occurred exactly as predicted and were pairwise disjoint. A direct recipe: enumerate all q^r words y, compute x from the constraints, walk the ordered assignments splitting after each y_j, and group suffixes by prefix. Deduplicate the nonempty suffix sets and test their count and disjointness.
