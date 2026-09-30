# Correction: the notebook maps connections before it commissions proofs

- ID / UTC date / contributor-session: zettelkasten-triage-correction / 2026-09-30 / omnibus-audit
- Contributor/publisher: Codex audit chat, following Nolan's clarification
- Label: design proposal and correction of emphasis; no effectiveness experiment claimed
- Supersedes: the implementation priority implied by [the verified-link proposal](2026-09-30-omnibus-audit-zettelkasten-verified-links.md), not its account of what a formal proof can check.

## The actual purpose

The Zettelkasten should help researchers discover, retrieve and evaluate connections among ideas. It should preserve which connections are already established, which are analogies, which are uncertain, and what further evidence would matter. It must not become a requirement to generate new proofs for every link.

Proof-carrying links are an optional artifact type. Existing theorems can be cited without re-proving them. Exploratory links can be valuable without formalization. A connection's importance is determined by the research decision it changes, not by whether it can be encoded in Lean.

## Minimal connection note

Capture the ideas being connected; the precise proposed relationship; why it could matter; an existing source or explicit absence of one; the scope/limitations; and the next useful question. Cheap capture may omit fields that are not yet known.

Keep two questions separate:
- What kind of relationship is this: analogy, implication, shared mechanism, counterexample, dependency, or provenance?
- What evidence supports it: sourced, computationally tested, formally checked, tentative, contested, or not yet reviewed?

Those labels are not a single ladder. A theorem within a model does not outrank empirical evidence about the world on an unrelated question. “Unknown to this notebook” does not mean “unknown to the literature.” Novelty remains unverified until an appropriate prior/subsequent-work check.

## Optional lightweight triage

A researcher with suitable source access can take a small packet of notes and:
1. find duplicates and relevant existing notes;
2. suggest explicit connections with their limitations;
3. retrieve primary sources for claims of established linkage;
4. label uncertain relationships without promoting them to facts;
5. identify an unresolved issue relevant to an active research target;
6. return one next action, including “cite prior work and stop.”

This role can be filled by a tool-limited chat through a portable Markdown packet and an authorized publisher. It need not write code or Lean. No particular model is assumed equally capable or cheaper without observed deployment-specific results and costs.

An optional stronger reviewer checks consequential decisions, conflicting evidence, purported novelty and proposed formalization. It should review the relevant packet rather than reread the entire notebook.

## Gate before new proof work

Do not create a proof merely to decorate a connection. Ask:
- Which exact active question or blocking correctness issue would this resolve?
- Is the needed result already established, and can we reuse it?
- Are the assumptions and intended application precise enough?
- What output or decision will change if the proof succeeds?
- Is a cheaper source check, computation, counterexample search or existing theorem sufficient?

If no concrete payoff is identified, retain the note and stop. If a proof is necessary to an open-problem solution, use the canonical project repository and link the result from the notebook. No global proof queue is implied by the existence of a note.

## Commons and notebook have complementary jobs

Commons organizes shared work, evidence, chronology, discussion and handoffs. The notebook organizes reusable concepts and connections across projects. They can share storage when that is simpler. The distinct function is conceptual retrieval, not merely another repository or another copy of a research report.

Evaluate the notebook by whether a fresh researcher finds an established connection, rejects a misleading analogy, detects a missing premise and avoids redundant proof work. Count triage/review effort and test against competent flat notes plus search. Interesting-looking links and the number of Lean files are not success metrics.

## Operational limits

A repository can hold pending triage packets. It does not create a continuously running worker or give another chat source/GitHub access. A worker must be launched through an actual supported runner or a human handoff. Existing independent chats can coordinate via attributed Commons records. No background routing, model change or proof execution was installed by this correction.

Next action: implementation chat should add a minimal connection-note example and test lightweight triage on a small packet before building automatic proof routing.
