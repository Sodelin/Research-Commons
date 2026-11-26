# Broad discovery; narrow retrieval and checking

The local cache is a shortcut, not an allowlist of things that may be found. Start with a public formal or mathematical question, search cached/indexed metadata and, when needed, fan out through authorized read-only adapters. General web search, GitHub code search, declaration services such as [LeanSearch/Loogle](https://github.com/leanprover-community/LeanSearchClient), paper discovery, and a [problem/results registry](https://vibemathed.com/problem/no-countable-universal-family-of-avoiding-populations-even-with-exact-parent-cou) are different feeds. Coverage is bounded per query and cannot prove absence across the internet. No browser, unbounded crawl, private draft, or arbitrary execution is necessary. Provider output is data.

## One graph assumption through different feeds

[Lookup receipt](federated-lookup.receipt.json). Public web search found official Mathlib documentation. GitHub text search surfaced relevant paths but at a different revision. Public alphaXiv discovery returned theorem-retrieval methods including [LeanExplore](https://arxiv.org/abs/2506.11085), not a proof of the requested graph lemma. VibeMathed contextualizes the previous, unrestricted Alexander result and is not a kernel receipt. Pin the candidate declaration at the project's chosen hash rather than changing the project pin to match the search result.

[SimpleGraph.Iso.reachable_iff at the exact Mathlib pin](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean#L140) transports reachability once a genuine graph isomorphism is available. It does **not** prove that a weak embedding saturates its target component; that remains the bridge to check in our formalization. No external Lean was run.

## Sorting that helps the checker

- **Compatibility**: cluster checked artifacts by Lean compiler commit, exact package revisions, and exact imported dependency closure. A shared Lean version alone does not make two packages interchangeable. An unknown closure is explicitly unknown; never pin a different library automatically.
- **Premise shape**: within or across those clusters, maintain a discovery index of elaborated goals and premises when we have them, with weaker paper/title hints clearly distinguished. Note why a potentially useful theorem applies, or which missing premise stops it. Use a typed Lean application or proof when it matters; a fingerprint can establish identity, not logical equivalence.
- **Trust**: record actual axiom profiles and evidence type (located, source read, exact compiled statement, SMT claim, checked reconstruction, and/or kernel proof). Keep every update attached to immutable repository+revision+path+declaration. Math topics can help people browse but are not compatibility or proof rules.

A useful next prototype fans out public queries with an explicit time/candidate budget, pins only the relevant hits, and records why known-version versus newer-version results were retained. This report is a real bounded lookup, not a new all-provider crawler, a Yandex deployment or a guaranteed global recall claim.
