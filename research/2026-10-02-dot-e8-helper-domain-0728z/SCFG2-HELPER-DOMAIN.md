# Pinned SCFG2 scaffold-helper domain and the next all-input admission gate

Attribution: dot. Checked 2026-10-02. Public source only, at
`TakumiOtagaki/PKProbDesign@27afdd054272dbda8a74c8aad156970a44c23cd8`.

## Result and scope

The fixed-width sparse-tree RMQ has a sharper conditional domain than a bound
read directly from its fourteen columns. For a balanced nested round scaffold,
with helper endpoints in the stated domains, all actual guarded `B` and `b`
queries are covered when **1 ≤ n ≤ 8193**. A balanced scaffold at n = 8194 has
a guarded `B` query requiring column 14, outside the allocated columns 0–13.
This is a source-arithmetic argument plus a bounded Python mirror screen. It
is not a Lean parser theorem, a C++ crash test, a whole-runtime memory proof,
or a claim that every input accepted by `ExactSession` satisfies these premises.

The existing universal Lean interpreter theorem remains parameterized over a
valid ordered provider and observer frame. Its mathematical size parameter
has no 8193 cutoff. This implementation-specific prerequisite belongs in the
source/executable refinement contract.

## Exact helper access contract

Sources: [sparse_tree.cc](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/sparse_tree.cc),
[sparse_tree.hh](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/sparse_tree.hh).

1. Constructor: n ≥ 1, the string has at least n positions, the integer n is
   represented faithfully by the stored uint16 length, all allocation-size
   arithmetic is defined, and allocations/recursive traversal succeed. Tree
   and `up` have n+1 entries; `FAI` and `logn` have 2(n+1) entries. A nonempty
   scaffold prefix must never pop the root stack marker. Balanced round
   brackets supply that prefix condition and the intended completed pairing.
2. `bp(i,l)` and `Bp(l,j)` first dereference the parent of tree[l], so
   1 ≤ l ≤ n is required. Their scalar i/j comparisons do not index i/j.
3. `b(i,l)` additionally requires 1 ≤ i ≤ l ≤ n when it reaches LCA.
   `B(l,j)` additionally requires 1 ≤ l ≤ j ≤ n when it reaches LCA.
4. `weakly_closed(i,j)` is an endpoint lookup, not an interval scan. The
   explicit (1,0) case returns before any lookup. Otherwise 0 ≤ i,j ≤ n is
   sufficient for its tree/FAI/depth lookups under the constructor invariant;
   intended nucleotide calls use 1 ≤ i,j ≤ n. Reversed or empty intervals
   with in-range endpoints are a separate semantic issue, not automatically
   an out-of-range array access.
5. The private LCA/query path requires valid first appearances, a nonnegative
   initialized distance, a column in 0–13, and initialized RMQ blocks whose
   selected Euler indices are inside the depth array. The argument below
   derives these properties for the guarded B/b domain.

The active context checks bounds for pair partners, parent indices, unpaired
prefixes and unpaired predicates, but forwards the four border helpers and
`weakly_closed` directly. Thus their preconditions cannot be inferred from
the context wrappers alone. Source:
[WFinalExactInsideContext](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/replay/w_final_exact_inside.hh).

## Why the cutoff is 8193

For the tree produced by a balanced round scaffold:

- Every nucleotide has one parent with smaller index. The opening pair node
  owns its interior positions; its closing position is attached after the
  stack pop, so that closing node is not its own descendant.
- The DFS first-visit order is 0,1,…,n. The Euler walk has 2n+1 entries.
- If h(v) is a node's depth, then FAI(v) = 2v − h(v). This counts v earlier
  first visits and v−h(v) earlier return events. For v≥1, 1≤h(v)≤v.

A B/b call only reaches LCA after rejecting an unpaired l whose parent is
the root, and after rejecting a paired l. Thus a surviving l has h(l)≥2,
l≥2, and l≤n−1 (its parent has a later closing endpoint).

For B(l,j), the additional parent-closing guard gives an in-range j after l.
Consequently FAI(l)≥2 and FAI(j)≤2n−1, so its distance is at most 2n−3.
For b(i,l), the parent-opening guard puts i before l; FAI(i)≥1 and
FAI(l)≤2(n−1)−2, so its distance is at most 2n−5.

`preprocess` initializes floor(log2 d) for 1≤d<2n. With n≤8193, every
surviving distance is ≤16383, and floor(log2 d)≤13. The stored uint16
length also equals n on this domain. The constructor/owner quadratic
32-bit size expressions are below their overflow limits on this domain;
that arithmetic observation does not promise available RAM or stack space.

The boundary witness uses scaffold `(`, then n−3 dots, then `).`, and
calls B(2,n). The parent of position2 is opening1 with closing n−1, so
the B guard passes. FAI(2)=2, FAI(n)=2n−1, hence d=2n−3:

- n8193: d16383, required column13
- n8194: d16385, required column14

This is an index-domain witness derived from source semantics. No large
SCFG2 schedule, allocation, or undefined C++ query was run.

## Why table construction itself is covered

The source base column stores the minimum of two adjacent Euler positions.
Column c therefore represents an interval of **2^c+1 positions**, not
2^(c+1) positions. Its initialized rows are exactly i+2^c<E, where E=2n+1.

For the next column, C++ short-circuit evaluation first checks the previous
block at i. If that block is initialized, i+2^(c−1)<E, so the second row
lookup is in range. That second block exists exactly when i+2^c<E. The
first missing block ends the contiguous initialized prefix. This is why
the apparent unchecked row addition is not, by itself, a small-n failure.

For a query distance d>0, q=2^floor(log2 d) satisfies q≤d<2q. The two
blocks starting at FAI(left) and FAI(right)−q stay within the queried Euler
interval. Their overlap covers the full interval, and neither selected
index is −1. Equal-endpoint LCA calls return before querying.

## Active-provider endpoint checks and remaining source premises

Sources:
[generator](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/generate_exact_basic.hh),
[WMB geometry](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/wmb_geometry.hh),
[schedule](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/engine/basic_schedule.hh).

The exact schedule supplies ordinary parents 1≤i≤j≤n and BE parents
with i≤ip<jp≤j, both anchors matched by the scaffold. Border calls use
the ordinary parent endpoints or an interior split l. The WMB closing
split starts after an in-range positive paired opening. These are the
same ordered endpoint premises used above.

The generator's explicit weak-closure calls fall into four groups:

- parent endpoints and root prefixes (1,j)
- (1,k−1), including the explicitly handled (1,0)
- root decomposition's (1,p−1) and guarded (k+1,j)
- BE wings (i+1,k−1) and (l+1,j−1), whose paired/ordered anchor guards
  keep both endpoint reads inside 1..n even when a wing is empty

The next single tree contract needed for all seventeen families is:
opening-node subtree interval [open,close), ordered opening children,
and the LCA separation property induced by that same tree. It implies
positive bp/b results in [i,l), and positive Bp/B results in (l,j]. Those
bounds are needed to prove both child-span containment and scheduled BE
anchor membership for WMB dependencies. Helper bodies alone, or bare
`is_valid(Deduction)`, do not establish those facts.

These source-contract checks are not a formal C++ alias/parser extraction
proof. Energy-library/encoded-sequence accesses, coefficient indices,
floating-point finiteness/rounding, resource availability, concurrent
global configuration, RNA support and physical weights remain named gates.

## Front-end enforcement and evidence

[ExactSession validation](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/api/exact.cc)
checks only nonempty sequence and matching scaffold length. It does not
enforce this size/scaffold/helper contract. The four-bracket target parser
is a separate operation and cannot validate the scaffold constructor.
A source-specific guarded adapter or a dynamic RMQ/length representation
is therefore an implementation obligation before claiming the public API
refines the mathematical all-size theorem.

`audit_scfg2_helper_domain.py` checks the public-source tree/Euler/table
mirror for all3561 balanced round scaffolds of lengths1–10,40792 positive
guarded B/b queries, and the two arithmetic boundary witnesses. Every
assertion passed. `SCFG2-HELPER-DOMAIN-RECEIPT.json` pins the script SHA256,
nine public source SHA256/Git-blob hashes, counts and qualified status.
The original source files were read-only throughout. This is implementation
admission evidence; it is not counted as another Lean PASS module.

## Closest established contract and usefulness

RMQ/Euler-tree indexing and defined-memory preconditions are established
implementation techniques. This report claims no new RMQ or DP theorem.
Its use is to expose the exact missing preconditions for the pinned SCFG2
source instantiation of the already checked universal interpreter, and to
avoid conflating all mathematical n with all strings accepted by the API.
